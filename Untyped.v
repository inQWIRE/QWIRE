Require Import Arith.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require Import Program.
Require Import Contexts.
Require Import Patterns.

Inductive Gate : Set := 
  | H | σx | σy | σz | CNot 
  | init0 | init1 | new0 | new1 | meas | discard
  | control : Gate -> Gate
  | bit_control : Gate -> Gate
  | transpose : Gate -> Gate
.

Inductive Unitary : Gate -> Set := 
  | U_H : Unitary H | U_σx : Unitary σx | U_σy : Unitary σy | U_σz : Unitary σz 
  | U_CNot : Unitary CNot 
  | U_control : forall g, Unitary g -> Unitary (control g)
  | U_bit_control : forall g, Unitary g -> Unitary (bit_control g)
  | U_transpose : forall g, Unitary g -> Unitary (transpose g)
.

(* We have GateWType guarantee that only unitary gates are controlled/transposed *)
Inductive GateWType : Gate -> WType -> WType -> Set :=
  | H_type: (GateWType H Qubit Qubit)
  | σx_type : (GateWType σx Qubit Qubit) 
  | σy_type : (GateWType σy Qubit Qubit) 
  | σz_type : (GateWType σz Qubit Qubit) 
  | CNot_type : (GateWType CNot (Qubit ⊗ Qubit) (Qubit ⊗ Qubit))
  | init0_type : (GateWType init0 One Qubit)
  | init1_type : (GateWType init1 One Qubit)
  | new0_type : (GateWType new0 One Bit)
  | new1_type : (GateWType new1 One Bit)
  | meas_type : (GateWType meas Qubit Bit)
  | discard_type : (GateWType discard Bit One)
  | control_type : forall g W, Unitary g -> GateWType g W W -> 
                              GateWType (control g) (Qubit⊗W) (Qubit⊗W)
  | bit_control_type : forall g W, Unitary g -> GateWType g W W -> 
                              GateWType (bit_control g) (Bit⊗W) (Bit⊗W)
  | transpose_type : forall g W, Unitary g -> GateWType g W W -> 
                              GateWType (transpose g) W W
. 

Inductive Circuit  :=
| output : Pat -> Circuit
| gate : Gate -> Pat -> Pat -> Circuit -> Circuit (* 1st pat is input, 2nd output *)
| lift : forall {w:WType}, Pat -> (interpret w -> Circuit) -> Circuit
.

Notation "p2 <- 'gate' g p1 ; C" := (gate g p1 p2) (at level 10) : circ_scope.
Delimit Scope circ_scope with circ.

(* Lift notation? *)

Inductive WF_Circuit : OCtx -> Circuit -> WType -> Set :=
| wf_output : forall ctx p w, WF_Pat ctx p w -> WF_Circuit ctx (output p) w
| wf_gate   : forall ctx ctx1 ctx2 ctx1' ctx2' g p1 p2 c w1 w2 w,
              ctx1 ⋓ ctx = ctx1'
           -> ctx2 ⋓ ctx = ctx2'
           -> GateWType g w1 w2
           -> WF_Pat ctx1 p1 w1
           -> WF_Pat ctx2 p2 w2
           -> WF_Circuit ctx2' c w
           -> WF_Circuit ctx1' (gate g p1 p2 c) w
| wf_lift   : forall ctx1 ctx2 ctx p w w' f,
              ctx1 ⋓ ctx2 = ctx
           -> WF_Pat ctx1 p w
           -> (forall (x:interpret w), WF_Circuit ctx2 (f x) w')
           -> WF_Circuit ctx (lift p f) w'
.
Inductive Boxed_Circ : WType -> WType -> Set := 
| box : forall {W1 W2 Γ} p c,
               WF_Pat Γ p W1 -> WF_Circuit Γ c W2 -> Boxed_Circ W1 W2
.

Definition Typed_Pattern Γ W := {p : Pat & WF_Pat Γ p W}.
Definition Typed_Circuit Γ W := {c : Circuit & WF_Circuit Γ c W}.


Fixpoint compose {Γ1} {W} (c : Typed_Circuit Γ1 W)
                 : forall {Γ Γ1' : Ctx} {W'}, 
                  Valid Γ1' = Γ1 ⋓ Γ ->
                  (forall {Γ2 Γ2' : Ctx}, Valid Γ2' = Γ2 ⋓ Γ -> 
                                          Typed_Pattern Γ2 W  -> Typed_Circuit Γ2' W') 
                -> Typed_Circuit Γ1' W'.
  destruct c as [c wf_c].
  refine (match wf_c with
          | wf_output _ _ _ wf_p => _
          | wf_gate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wf_p1 wf_p2 wf_c => _
          | wf_lift _ _ _ _ _ _ _ _ wf_p f => _
          end).
  -
  -
  -
  -

Definition compose (c1 : Typed_Circuit Γ1' W1) 
                   (forall Γ2 Γ2', 


Inductive Fresh_Pat (σ : Substitution) : Pat -> Set :=
| Fresh_Var : forall x, σ x = None -> Fresh_Pat σ (var x)
| Fresh_Unit : Fresh_Pat σ unit
| Fresh_Pair : forall p1 p2, Fresh_Pat σ p1 -> Fresh_Pat σ p2 -> Fresh_Pat σ (p1,p2)
.

Lemma get_ctx_WF : forall p W Γ, get_ctx p W = Valid Γ -> WF_Pat (get_ctx p W) p W.
Proof.
  induction p; intros W Γ H.
  - inversion H. apply wf_var. apply singleton_singleton.
  - destruct W; inversion H. apply wf_unit. 
  - destruct W as [ | | | W1 W2]; inversion H.
    remember (get_ctx p1 W1) as Γ1.
    remember (get_ctx p2 W2) as Γ2.
    destruct Γ1 as [ | Γ1]; inversion H1.
    destruct Γ2 as [ | Γ2]; inversion H2.
    rewrite H.
    econstructor; eauto.
    * rewrite HeqΓ1. eapply IHp1; eauto.
    * rewrite HeqΓ2. eapply IHp2; eauto.
Qed.


(*
Lemma fresh_singleton_consistent : forall x W Γ,
      SingletonCtx x W Γ -> forall σ,
      σ x = None ->
      Consistent_Ctx σ Γ.
Proof.
  induction 1; intros σ eq; simpl.
  - Print Consistent_Ctx.
  -
Admitted.

Lemma fresh_consistent : forall σ p,
      Fresh_Pat σ p -> forall W,
      WF_Pat (get_ctx p W) p W ->
      Consistent_Ctx σ (get_ctx p W).
Proof.
  induction 1; simpl in *; intros W wf_p.
  - eapply fresh_singleton_consistent; eauto.
    apply singleton_singleton.
  - destruct W; inversion wf_p.
    constructor.
  - destruct W as [ | | | W1 W2]; inversion wf_p; subst.
    remember (get_ctx p1 W1 ⋓ get_ctx p2 W2) as Γ.
    destruct Γ as [ | Γ].
    * assert False.
        eapply wf_pat_not_invalid; eauto.
      contradiction.
    * eapply consistent_merge; eauto.
      + apply IHFresh_Pat1; auto.
        eapply wf_pat_equiv; eauto.
        apply wf_pat_unique; auto.
      + apply IHFresh_Pat2; auto.
        eapply wf_pat_equiv; eauto.
        apply wf_pat_unique; auto.
Qed.
*)


Inductive Consistent_Circ : Substitution -> Circuit -> WType -> Set :=
| consistent_output : forall σ p W, 
    (* Consistent_Pat σ p W -> *)
    Consistent_Circ σ (output p) W
| consistent_gate : forall g W1 W2 p1 p2 c σ W,
    GateWType g W1 W2 ->
    (* Consistent_Pat σ p1 W1 -> *)
    Fresh_Pat σ p2 ->
    Consistent_Circ σ c W ->
    Consistent_Circ σ (gate g p1 p2 c) W
| consistent_lift : forall σ p W f W',
    (* Consistent_Pat σ p W -> *)
    (forall (x : interpret W), Consistent_Circ σ (f x) W') ->
    Consistent_Circ σ (lift p f) W'
.

Fixpoint subst (σ : Substitution) (c : Circuit) : Circuit :=
  match c with
  | output p => output (subst_pat' σ p)
  | gate g p1 p2 c' => gate g (subst_pat' σ p1) p2 (subst σ (c'))
  | lift p0 f => lift (subst_pat' σ p0) (fun x => subst σ (f x))
  end.

Inductive Consistent_OCtx : Substitution -> OCtx -> OCtx -> Set :=
| Consistent_Valid : forall σ Γ Γ',
  Consistent_Ctx σ Γ Γ' -> Consistent_OCtx σ Γ Γ'.

(*
Lemma consistent_circ_ctx : forall Γ c W,
      WF_Circuit Γ c W -> forall σ,
      Consistent_Circ σ c W ->
      Consistent_OCtx σ Γ (subst_ctx_O σ Γ).
Proof.
  induction 1
Admitted.
*)

Lemma fresh_singleton : forall x w Γ,
      SingletonCtx x w Γ ->
      forall σ, σ x = None -> subst_ctx σ Γ = Γ.
Proof.
  induction 1; intros σ fresh.
  - simpl. rewrite fresh; auto.
  - simpl. rewrite IHSingletonCtx.


Lemma fresh_subst : forall Γ p W,
    WF_Pat Γ p W -> forall σ,
    Fresh_Pat σ p ->
    subst_ctx_O σ Γ = Γ.
Admitted.

Lemma consistent_subst : forall Γ c W,
      WF_Circuit Γ c W -> forall σ,
      Consistent_Circ σ c W ->
      WF_Circuit (subst_ctx' σ Γ) (subst σ c) W.
Proof.
  intros Γ c W wf_c σ consistent_c.
  assert (consistent_Γ : Consistent_Ctx σ Γ).
    eapply consistent_circ_ctx; eauto.
  revert σ consistent_c consistent_Γ.
  induction wf_c; intros σ consistent_c consistent_Γ; simpl.
  - constructor. apply wf_subst_pat; auto.
  - assert (consistent : Consistent_Ctx σ ctx1 * Consistent_Ctx σ ctx).
      eapply consistentO_split; eauto.
    destruct consistent as [consistent1 consistent].
    eapply wf_gate with (w1 := w1) (w2 := w2);
      [ | | auto | apply wf_subst_pat; eauto | eauto | ].
    * apply subst_OCtx_split; eauto.
    * inversion consistent_c; subst.
      assert (consistent2' : Consistent_Ctx σ ctx2').
        
      rewrite <- fresh_subst with (Γ := ctx2) (σ := σ) (p := p2) (W := w2); auto.
      apply subst_OCtx_split; eauto.
      +
      +
    *
  -

Lemma wf_subst : forall Ω c W,
                 WF_Circuit Ω c W
              -> forall σ,
                 Consistent_Ctx σ Ω -> 
                 WF_Circuit (subst_ctx' σ Ω) (subst σ c) W.
Proof.
  induction 1 as [Ω p W | |]; intros σ pf; simpl.
  - constructor. apply wf_subst_pat; auto.
  - assert (consistent : Consistent_Ctx σ ctx1 * Consistent_Ctx σ ctx).
      eapply consistentO_split; eauto.
    (* The admits below depend on the fact that ctx2 is fresh for σ? 
       i.e. we need capture avoiding substitution *)
    destruct consistent as [consistent1 consistent].
    eapply wf_gate with (w1 := w1) (w2 := w2); auto.
    Focus 3. apply wf_subst_pat; eauto. 
    Focus 3. eauto. 
    * apply subst_OCtx_split; eauto.
    * admit.
    * apply IHWF_Circuit. admit.
  - assert (consistent : Consistent_Ctx σ ctx1 * Consistent_Ctx σ ctx2).
      eapply consistentO_split; eauto.
    destruct consistent as [consistent1 consistent2].
    eapply wf_lift. 
    * apply subst_OCtx_split; eauto.
    * apply wf_subst_pat; auto.
    * intro x. apply H0; auto.
Admitted.


Inductive Boxed_Circ : WType -> WType -> Set := 
| box : forall {W1 W2 ctx} p c {pf : Concrete p W1}
               {wf_p : WF_Pat ctx p W1} {wf_c : WF_Circuit ctx c W2}, 
               Boxed_Circ W1 W2
.
(*Arguments box {w1} {w2} _ p c _ _. Check subst.*)

Definition subst_pat' {W} (p' : Pat) (p : Pat) {pf : Concrete p W} {pf' : Concrete p' W} : p' ≼ p.
Proof.
    revert p' pf'.
    induction pf; intros p' pf'.
    - constructor.
    - constructor.
    - inversion pf'. constructor.
    - inversion pf'; subst. constructor. apply IHpf1; auto. apply IHpf2; auto.
Defined.

Definition subst' {W} (p' : Pat) (p : Pat) 
                          {pf : Concrete p W} {pf' : Concrete p' W}
                          (c : Circuit) : Circuit.
  refine (subst (subst_var (subst_pat' p' p)) c ).
  exact pf. exact pf'.
Defined.

Definition unbox {W1 W2} (c : Boxed_Circ W1 W2) p' {pf' : Concrete p' W1} 
                   : Circuit.
  revert p' pf'.
  destruct c; intros p' pf'.
  eapply (@subst' W1 p' p _ _ c).
  Unshelve. auto. auto.
Defined.

Lemma wf_subst' : 

Lemma wf_unbox : forall Γ W1 W2 p (c : Boxed_Circ W1 W2) {pf : Concrete p W1},
                 WF_Pat Γ p W1 -> WF_Circuit Γ (@unbox W1 W2 c p pf) W2.
Proof.
  intros Γ W1 W2 p c pf wf_p.
  revert Γ p pf wf_p.
  destruct c; intros Γ p' pf' wf_p'.
  simpl.
  
Qed.


Fixpoint compose  (p : Pat) (c:Circuit) (c' : Circuit) : Circuit :=
  match c with
    | output p' => subst p' p c'
    | gate p2 g p1 c => gate p2 g p1 (compose p c c')
    | lift p' f => lift p' (fun x => compose p (f x) c')
  end.

Lemma wf_compose : forall ctx ctx1 ctx2 ctx1' ctx2' p c c' w w',
      MergeCtx ctx1 ctx ctx1'
   -> MergeCtx ctx2 ctx ctx2'
   -> WF_Circuit ctx1 c w
   -> WF_Pat ctx2 p w
   -> WF_Circuit ctx2' c' w'
   -> WF_Circuit ctx1' (compose p c c') w'.
Admitted.
