Require Import Arith.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Inductive WType := Qubit | Bit | One | Tensor : WType -> WType -> WType.

Notation "W1 ⊗ W2" := (Tensor W1 W2) (at level 1, left associativity): circ_scope.

Open Scope circ_scope.

(* Coq interpretations of wire types *)
Fixpoint interpret (w:WType) : Set :=
  match w with
    | Qubit => bool
    | Bit => bool 
    | One => Datatypes.unit
    | Tensor w1 w2 => (interpret w1) * (interpret w2)
  end.

Definition Var := nat.
Definition Ctx := list (option WType).

Inductive SingletonCtx : Var -> WType -> Ctx -> Set :=
| SingletonHere : forall w, SingletonCtx 0 w (Some w :: [])
| SingletonLater : forall x w ctx, SingletonCtx x w ctx -> SingletonCtx (S x) w (None::ctx)
.

Inductive MergeOption : option WType -> option WType -> option WType -> Set :=
| MergeNone : MergeOption None None None
| MergeLeft : forall a, MergeOption (Some a) None (Some a)
| MergeRight : forall a, MergeOption None (Some a) (Some a)
.

Inductive MergeCtx : Ctx -> Ctx -> Ctx -> Set :=
| MergeNilL : forall ctx, MergeCtx [] ctx ctx
| MergeNilR : forall ctx, MergeCtx ctx [] ctx
| MergeCons : forall o1 o2 o g1 g2 g, 
              MergeOption o1 o2 o -> MergeCtx g1 g2 g -> 
              MergeCtx (o1 :: g1) (o2 :: g2) (o :: g)
.

(* For future tactics *)
Inductive MergeCtxList : list Ctx -> Ctx -> Set :=
| MergeZero : MergeCtxList [] []
| MergeOne : forall Γ, MergeCtxList [Γ] Γ 
| MergeMult : forall Γ Γs Γ' Γ'', MergeCtxList Γs Γ' -> MergeCtx Γ Γ' Γ'' -> 
                             MergeCtxList (Γ :: Γs) Γ''.

(* Typed Circuits Scope [UC is UntypedCircuits] *)
Module TC.

Inductive Pat : Ctx -> WType -> Set :=
(* | var  : forall x w ctx, SingletonCtx x w ctx -> Pat ctx w *)
| unit : Pat [] One
| qubit : forall x ctx, (SingletonCtx x Qubit ctx) -> Pat ctx Qubit 
| bit : forall x ctx, (SingletonCtx x Bit ctx) -> Pat ctx Bit 
| pair : forall ctx1 ctx2 ctx w1 w2,
         MergeCtx ctx1 ctx2 ctx
      -> Pat ctx1 w1
      -> Pat ctx2 w2
      -> Pat ctx (Tensor w1 w2).

Inductive Unitary : WType -> Set := 
  | H : Unitary Qubit 
  | σx : Unitary Qubit
  | σy : Unitary Qubit
  | σz : Unitary Qubit
  | CNOT : Unitary (Qubit ⊗ Qubit)
  | control : forall {W} (U : Unitary W), Unitary (Qubit ⊗ W) 
  | bit_control : forall {W} (U : Unitary W), Unitary (Bit ⊗ W) 
  | transpose : forall {W} (U : Unitary W), Unitary W.

Inductive Gate : WType -> WType -> Set := 
  | U : forall {W} (u : Unitary W), Gate W W
  | init0 : Gate One Qubit
  | init1 : Gate One Qubit
  | new0 : Gate One Bit
  | new1 : Gate One Bit
  | meas : Gate Qubit Bit
  | discard : Gate Bit One.

Coercion U : Unitary >-> Gate.

Inductive Circuit : Ctx -> WType -> Set :=
| output : forall {ctx ctx' w},  MergeCtx ctx [] ctx' -> Pat ctx w -> Circuit ctx' w
| gate   : forall ctx {ctx1 ctx1' w1 w2 w}, 
          MergeCtx ctx1 ctx ctx1'            
        -> Gate w1 w2
        -> Pat ctx1 w1
        -> (forall {ctx2 ctx2'}, MergeCtx ctx2 ctx ctx2' 
            -> Pat ctx2 w2 -> Circuit ctx2' w)
        -> Circuit ctx1' w.

Inductive Box : WType -> WType -> Set :=
| box : forall {w1} {w2}, 
        (forall {ctx}, Pat ctx w1 -> Circuit ctx w2) -> Box w1 w2.

Definition unbox {ctx ctx'} {w1} {w2} (b : Box w1 w2) : 
  MergeCtx ctx [] ctx' -> Pat ctx w1 -> Circuit ctx' w2.
  refine (match b with box f => _ end). intros M; inversion M; auto. Qed.

End TC.
Import TC.

Open Scope type_scope.

Definition disjoint Γ1 Γ2 := {Γ : Ctx & MergeCtx Γ1 Γ2 Γ}.
Definition subset Γ1 Γ := {Γ2 : Ctx & MergeCtx Γ1 Γ2 Γ}.

Infix "∥" := disjoint (at level 30).
Infix "⊆" := subset (at level 30).

Lemma disjoint_nil_l : forall Γ, [] ∥ Γ.
Proof. intro. exists Γ. constructor. Qed.

Lemma disjoint_nil_r : forall Γ, Γ ∥ [].
Proof. intro. exists Γ. constructor. Qed.

Lemma disjoint_cons : forall o1 o2 o Γ1 Γ2,
      MergeOption o1 o2 o -> Γ1 ∥ Γ2 -> (o1 :: Γ1) ∥ (o2 :: Γ2).
Proof. destruct 2 as [Γ pfDisjoint]. exists (o :: Γ). constructor; auto. Qed.

Lemma disjoint_cons_inv: forall (o1 o2 : option WType) (Γ1 Γ2 : Ctx),
  (o1 :: Γ1) ∥ (o2 :: Γ2) -> Γ1 ∥ Γ2 * {o : (option WType) & MergeOption o1 o2 o}.
Proof.
  intros.
  inversion H0.
  inversion H1; subst.
  split.
  exists g. assumption.
  exists o. assumption.
Qed.

Lemma merge_nil_l : forall Γ1 Γ2, MergeCtx [] Γ1 Γ2 -> Γ1 = Γ2.
Proof. intros Γ1 Γ2 H. inversion H; subst; reflexivity. Qed.

Lemma merge_nil_r : forall Γ1 Γ2, MergeCtx Γ1 [] Γ2 -> Γ1 = Γ2.
Proof. intros Γ1 Γ2 H. inversion H; subst; reflexivity. Qed.

Lemma merge_option_disjoint : forall o1 o2 o3 o o',
      MergeOption o1 o2 o -> MergeOption o o3 o' -> 
      {o0 : option WType  & MergeOption o1 o3 o0} 
    * {o0' : option WType & MergeOption o2 o3 o0'}.
Proof.
  inversion 1; inversion 1; subst; split;
    try (exists None; constructor);
    try (exists (Some a); constructor).
Qed.

Lemma merge_disjoint : forall Γ1 Γ2 Γ3 Γ Γ',
      MergeCtx Γ1 Γ2 Γ -> MergeCtx Γ Γ3 Γ' -> Γ1 ∥ Γ3 * Γ2 ∥ Γ3.
Proof.
  intros ? ? ? ? ? merge_Γ1_Γ2_Γ merge_Γ_Γ3_Γ';
    revert Γ1 Γ2 merge_Γ1_Γ2_Γ.
  induction merge_Γ_Γ3_Γ' as [ | | o o3 o' Γ Γ3 Γ' merge_o_o3_o' merge_Γ_Γ3_Γ']; 
    intros Γ1 Γ2 merge_Γ1_Γ2_Γ;
    inversion merge_Γ1_Γ2_Γ; subst;
    try (split; (apply disjoint_nil_l || apply disjoint_nil_r); fail).
  - split; try apply disjoint_nil_l.
    destruct (IHmerge_Γ_Γ3_Γ' Γ []) as [disjoint_g1_g2 _]; try constructor.
    eapply disjoint_cons; eauto.
  - split; try apply disjoint_nil_l.
    destruct (IHmerge_Γ_Γ3_Γ' Γ []) as [disjoint_g1_g2 _]; try constructor.
    eapply disjoint_cons; eauto.
  - destruct (IHmerge_Γ_Γ3_Γ' _ _ H5).
    edestruct (merge_option_disjoint o1 o2 o3) as [ [? ?] [? ?]]; eauto.
    split; eapply disjoint_cons; eauto.
Qed.

Lemma merge_option_functional : forall o1 o2 o o',
                              MergeOption o1 o2 o -> MergeOption o1 o2 o' -> o = o'.
Proof. destruct 1; inversion 1; auto. Qed.

Lemma merge_functional : forall {Γ1 Γ2 Γ Γ'}, 
                 MergeCtx Γ1 Γ2 Γ -> MergeCtx Γ1 Γ2 Γ' -> Γ = Γ'.
Proof.
  intros Γ1 Γ2 Γ Γ' merge_Γ1_Γ2_Γ.
  revert Γ'.
  induction merge_Γ1_Γ2_Γ; intros Γ' merge_Γ1_Γ2_Γ'.
  - inversion merge_Γ1_Γ2_Γ'; auto.
  - inversion merge_Γ1_Γ2_Γ'; auto.
  - inversion merge_Γ1_Γ2_Γ'; subst.
    erewrite merge_option_functional with (o := o) (o' := o4); eauto.
    rewrite IHmerge_Γ1_Γ2_Γ with (Γ' := g4); eauto.
Qed.

Lemma merge_option_symm : forall o1 o2 o, MergeOption o1 o2 o -> MergeOption o2 o1 o.
Proof. destruct 1; constructor. Qed.

Lemma merge_symm : forall {Γ1 Γ2 Γ}, MergeCtx Γ1 Γ2 Γ -> MergeCtx Γ2 Γ1 Γ.
Proof. induction 1; constructor; auto. apply merge_option_symm; auto. Qed.

Lemma disjoint_symm : forall Γ1 Γ2, Γ1 ∥ Γ2 -> Γ2 ∥ Γ1.
Proof.
  intros Γ1 Γ2 D.
  destruct D as [Γ M].
  apply merge_symm in M.  
  exists Γ. assumption.
Qed.

Lemma merge_option_assoc : forall o1 o2 o3 o o' o0,
      MergeOption o1 o2 o -> MergeOption o o3 o'
   -> MergeOption o1 o3 o0
   -> MergeOption o2 o0 o'.
Proof. inversion 1; inversion 1; inversion 1; constructor. Qed.

(* An associativity rule should have Γ1 Γ0 Γ' as the conclusion *)
Lemma merge_assoc : forall Γ1 Γ2 Γ3 Γ Γ' Γ0,
      MergeCtx Γ1 Γ2 Γ -> MergeCtx Γ Γ3 Γ' 
   -> MergeCtx Γ1 Γ3 Γ0
   -> MergeCtx Γ2 Γ0 Γ'.
Proof.
  intros Γ1 Γ2 Γ3 Γ Γ' Γ0 merge_Γ1_Γ2_Γ. (* merge_Γ_Γ3_Γ' merge_Γ1_Γ3_Γ0. *)
  revert Γ3 Γ' Γ0.
  induction merge_Γ1_Γ2_Γ; intros Γ3 Γ' Γ0 merge_Γ_Γ3_Γ' merge_Γ1_Γ3_Γ0.
  - inversion merge_Γ1_Γ3_Γ0; subst; auto.
  - rewrite (merge_functional merge_Γ_Γ3_Γ' merge_Γ1_Γ3_Γ0); constructor.
  - inversion merge_Γ1_Γ3_Γ0; subst; auto.
    * inversion merge_Γ_Γ3_Γ'; subst; auto.
      constructor. apply merge_option_symm; auto. apply merge_symm; auto.
    * inversion merge_Γ_Γ3_Γ'; subst; auto.
      constructor.
      + eapply merge_option_assoc; eauto.
      + eapply IHmerge_Γ1_Γ2_Γ; eauto.
Qed.        

Definition merge3 Γ1 Γ2 Γ3 Γ := { Γ0 : Ctx & MergeCtx Γ1 Γ2 Γ0 * MergeCtx Γ0 Γ3 Γ}.

(* more commutativity than associativity *)
Lemma merge3_assoc : forall Γ1 Γ2 Γ3 Γ,
                    merge3 Γ1 Γ2 Γ3 Γ -> merge3 Γ1 Γ3 Γ2 Γ.
Proof.
  destruct 1 as [Γ0 [merge_Γ1_Γ2_Γ0 merge_Γ0_Γ3_Γ]].
  assert (disjoint_Γ1_Γ3 : Γ1 ∥ Γ3).
    edestruct (merge_disjoint Γ1 Γ2 Γ3); eauto.
  destruct disjoint_Γ1_Γ3 as [Γ0' merge_Γ1_Γ3_Γ0'].
  exists Γ0'. split; auto.
  apply merge_symm.
  eapply (merge_assoc Γ1 Γ2 Γ3); eauto.
Qed.

Fixpoint compose {Γ1} {W} (c : Circuit Γ1 W)
                 : forall {Γ} {Γ1'} {W'}, 
                  MergeCtx Γ1 Γ Γ1' ->
                  (forall {Γ2} {Γ2'}, MergeCtx Γ2 Γ Γ2'
                                    -> Pat Γ2 W
                                    -> Circuit Γ2' W') 
                -> Circuit Γ1' W'.
  refine (match c with
            output _ p1 => fun Γ Γ1' W' pfM f => _ (* f _ _ pfM p1 *)
          | gate ctx pfM' g p1 h  => fun Γ Γ1' W' pfM f => _
          end). 
  (*output case*)
  eapply f.
  apply pfM.
  apply merge_nil_r in m; subst.
  apply p1.
  (* gate case*)
  clear W c Γ1;
  rename w into W1, w0 into W2, w1 into W;
  rename c0 into Γ01, c1 into Γ1, ctx into Γ0.
  rename pfM' into Merge_Γ01_Γ0_Γ1, pfM into Merge_Γ1_Γ_Γ1'.
  edestruct (merge_disjoint Γ01 Γ0 Γ) as [Disj_Γ01_Γ Disj_Γ0_Γ]; eauto.
  destruct Disj_Γ0_Γ as [Γ0' Merge_Γ0_Γ_Γ0'].
  assert (Merge_Γ01_Γ0'_Γ1' : MergeCtx Γ01 Γ0' Γ1').
    eapply merge_assoc; eauto. apply merge_symm; auto.
  refine (gate _ Merge_Γ01_Γ0'_Γ1' g p1 (fun Γ02 Γ02' Merge_Γ02_Γ0'_Γ02' q => _)).
    edestruct (merge_disjoint Γ0 Γ Γ02) as [[Γ002 Merge_Γ_Γ02_Γ002]
                                           [Γ02'' Merge_Γ0_Γ002_Γ02'']]; eauto;
      try (eapply merge_symm; eauto; fail).
  refine (compose _ _ (h Γ02 Γ002 _ q) _ _ _ _ f);
    try (apply merge_symm; auto; fail).
    (* Γ002 = Γ0 ⋓ Γ02 *)
    (* Γ02' = Γ02 ⋓ Γ0' = Γ02 ⋓ (Γ0 ⋓ Γ) *)
    (* So want to show that (Γ0 ⋓ Γ02) ⋓ Γ = Γ02 ⋓ (Γ0 ⋓ Γ) *)
    assert (Merge3_Γ0_Γ_Γ02 : merge3 Γ0 Γ Γ02 Γ02'). eexists.
      constructor; eauto; try (apply merge_symm; auto; fail).
    apply merge3_assoc in Merge3_Γ0_Γ_Γ02.
    destruct Merge3_Γ0_Γ_Γ02 as [Γ002' [Merge_Γ0_Γ02_Γ002' Merge_Γ002'_Γ_Γ02']].
    assert (Γ002' = Γ002).
      eapply merge_functional; eauto.
    subst. auto.
Qed.
