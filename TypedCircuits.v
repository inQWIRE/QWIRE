Require Import Arith.
Require Import List.
Import ListNotations.
Open Scope list_scope.



Inductive WType := Qubit | Bit | One | Tensor : WType -> WType -> WType.

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

Inductive EmptyCtx : Ctx -> Set :=
| EmptyNil : EmptyCtx []
| EmptyCons : forall ctx, EmptyCtx ctx -> EmptyCtx (None :: ctx)
.

Inductive SingletonCtx : Var -> WType -> Ctx -> Set :=
| SingletonHere : forall w ctx, EmptyCtx ctx -> SingletonCtx 0 w (Some w :: ctx)
| SingletonLater : forall x w ctx, SingletonCtx x w ctx -> SingletonCtx (S x) w (None :: ctx)
.

Inductive AddCtx : Var -> WType -> Ctx -> Ctx -> Set :=
| AddHere : forall w ctx, AddCtx 0 w (None :: ctx) (Some w :: ctx)
| AddLater : forall x w ctx ctx' m, AddCtx x w ctx ctx' -> AddCtx (S x) w (m :: ctx) (m :: ctx')
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
              MergeOption o1 o2 o -> MergeCtx g1 g2 g -> MergeCtx (o1 :: g1) (o2 :: g2) (o :: g)
.

Inductive Pat : Ctx -> WType -> Set :=
| var  : forall x w ctx, SingletonCtx x w ctx -> Pat ctx w
| unit : forall ctx, EmptyCtx ctx -> Pat ctx One
| pair : forall ctx1 ctx2 ctx w1 w2,
         MergeCtx ctx1 ctx2 ctx
      -> Pat ctx1 w1
      -> Pat ctx2 w2
      -> Pat ctx (Tensor w1 w2)
.

Parameter (Gate : WType -> WType -> Set).

Inductive Circuit : Ctx -> WType -> Set :=
| output : forall {ctx w}, Pat ctx w -> Circuit ctx w
| gate   : forall ctx {ctx1 ctx1' w1 w2 w},
           Gate w1 w2
        -> Pat ctx1 w1
        -> (forall {ctx2 ctx2'}, MergeCtx ctx2 ctx ctx2' 
            -> Pat ctx2 w2 -> Circuit ctx2' w)
        -> MergeCtx ctx1 ctx ctx1'
        -> Circuit ctx1' w
.

Inductive Box : WType -> WType -> Set :=
| box : forall {w1} {w2}, 
        (forall {ctx}, Pat ctx w1 -> Circuit ctx w2) -> Box w1 w2.

Definition unbox {ctx} {w1} {w2} (b : Box w1 w2) : Pat ctx w1 -> Circuit ctx w2 :=
  match b with
    box f => f ctx
  end.

Open Scope type_scope.

Definition Disjoint Γ1 Γ2 := {Γ : Ctx & MergeCtx Γ1 Γ2 Γ}.
Definition Subset Γ1 Γ := {Γ2 : Ctx & MergeCtx Γ1 Γ2 Γ}.

Lemma mergeDisjoint : forall Γ1 Γ2 Γ3 Γ Γ',
      MergeCtx Γ1 Γ2 Γ -> MergeCtx Γ Γ3 Γ' -> Disjoint Γ1 Γ3 * Disjoint Γ2 Γ3.
Admitted.

Lemma disjointTrans : forall Γ1 Γ2 Γ Γ', 
      MergeCtx Γ1 Γ2 Γ -> Disjoint Γ1 Γ' -> Disjoint Γ2 Γ' -> Disjoint Γ Γ'.
Admitted.

Lemma mergeAssoc : forall Γ1 Γ2 Γ3 Γ Γ' Γ0,
      MergeCtx Γ1 Γ2 Γ -> MergeCtx Γ Γ3 Γ' 
   -> MergeCtx Γ2 Γ3 Γ0
   -> MergeCtx Γ1 Γ0 Γ'.
Admitted.

Lemma mergeSymm : forall {Γ1 Γ2 Γ}, MergeCtx Γ1 Γ2 Γ -> MergeCtx Γ2 Γ1 Γ.
Admitted.

Lemma mergeFunctional : forall {Γ1 Γ2 Γ Γ'}, 
                 MergeCtx Γ1 Γ2 Γ -> MergeCtx Γ1 Γ2 Γ' -> Γ = Γ'.
Admitted.


Definition Merge3 Γ1 Γ2 Γ3 Γ := { Γ0 : Ctx & MergeCtx Γ1 Γ2 Γ0 * MergeCtx Γ0 Γ3 Γ}.
Lemma merge3Assoc : forall Γ1 Γ2 Γ3 Γ,
                    Merge3 Γ1 Γ2 Γ3 Γ -> Merge3 Γ1 Γ3 Γ2 Γ.
Admitted.


Fixpoint compose {Γ1} {W} (c : Circuit Γ1 W)
                 : forall {Γ} {Γ1'} {W'}, 
                  (forall {Γ2} {Γ2'}, MergeCtx Γ2 Γ Γ2'
                                    -> Pat Γ2 W
                                    -> Circuit Γ2' W') 
               -> MergeCtx Γ1 Γ Γ1' -> Circuit Γ1' W'.
  refine (match c with
            output p1 => fun Γ Γ1' W' f pfM => f _ _ pfM p1
          | gate ctx g p1 h pfM' => fun Γ Γ1' W' f pfM => _
          end). 
  clear W c Γ1;
  rename w into W1, w0 into W2, w1 into W;
  rename c0 into Γ01, c1 into Γ1, ctx into Γ0.
  rename pfM' into Merge_Γ01_Γ0_Γ1, pfM into Merge_Γ1_Γ_Γ1'.
  edestruct (mergeDisjoint Γ01 Γ0 Γ) as [Disj_Γ01_Γ Disj_Γ0_Γ]; eauto.
  destruct Disj_Γ0_Γ as [Γ0' Merge_Γ0_Γ_Γ0'].
  assert (Merge_Γ01_Γ0'_Γ1' : MergeCtx Γ01 Γ0' Γ1').
    eapply mergeAssoc; eauto.
  refine (gate _ g p1 (fun Γ02 Γ02' Merge_Γ02_Γ0'_Γ02' q => _) Merge_Γ01_Γ0'_Γ1').
    edestruct (mergeDisjoint Γ0 Γ Γ02) as [[Γ002 Merge_Γ_Γ02_Γ002]
                                           [Γ02'' Merge_Γ0_Γ002_Γ02'']]; eauto;
      try (eapply mergeSymm; eauto; fail).
  refine (compose _ _ (h Γ02 Γ002 _ q) _ _ _ f _);
    try (apply mergeSymm; auto; fail).
    (* Γ002 = Γ0 ⋓ Γ02 *)
    (* Γ02' = Γ02 ⋓ Γ0' = Γ02 ⋓ (Γ0 ⋓ Γ) *)
    (* So want to show that (Γ0 ⋓ Γ02) ⋓ Γ = Γ02 ⋓ (Γ0 ⋓ Γ) *)
    assert (Merge3_Γ0_Γ_Γ02 : Merge3 Γ0 Γ Γ02 Γ02'). eexists.
      constructor; eauto; try (apply mergeSymm; auto; fail).
    apply merge3Assoc in Merge3_Γ0_Γ_Γ02.
    destruct Merge3_Γ0_Γ_Γ02 as [Γ002' [Merge_Γ0_Γ02_Γ002' Merge_Γ002'_Γ_Γ02']].
    assert (Γ002' = Γ002).
      eapply mergeFunctional; eauto.
    subst. auto.
Qed.


