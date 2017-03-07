Require Import Arith.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require Import Program.
Require Import Contexts.

Inductive Pat := var : Var -> Pat | unit | pair : Pat -> Pat -> Pat.

(* Dangerous to take this notation *)
Notation "a , b" := (Datatypes.pair a b) (at level 11, left associativity) : default_scope.
Notation "w1 , w2" := (pair w1 w2) (at level 11, left associativity) : circ_scope.
(* Notation "()" := unit : circ_scope. *)

(*
Parameter (Gate : Set).

Parameter (GateWType : Gate -> WType -> WType -> Set).
*)

Inductive WF_Pat : Ctx -> Pat -> WType -> Set :=
| wf_qubit : forall x ctx, SingletonCtx x Qubit ctx -> WF_Pat ctx (var x) Qubit
| wf_bit   : forall x ctx, SingletonCtx x Bit ctx -> WF_Pat ctx (var x) Bit
(*| wf_var  : forall x w ctx, SingletonCtx x w ctx -> WF_Pat ctx (var x) w*)
| wf_unit : forall ctx, ctx = [] -> WF_Pat ctx unit One
| wf_pair : forall (Γ1 Γ2 Γ : Ctx) w1 w2 p1 p2, 
            Γ1 ⋓ Γ2 = Valid Γ -> WF_Pat Γ1 p1 w1 -> WF_Pat Γ2 p2 w2 
         -> WF_Pat Γ (pair p1 p2) (Tensor w1 w2)
.

(*Definition wf_var W : {Γ : Ctx & {p : Pat & WF_Pat Γ p W}}.*)

(* p' ≼ p *)
Inductive Le_Pat : Pat -> Pat -> Set :=
| le_var : forall p x, Le_Pat p (var x)
| le_unit : Le_Pat unit unit
| le_pair : forall p1 p2 p1' p2',
            Le_Pat p1' p1 -> Le_Pat p2' p2 -> Le_Pat (pair p1' p2') (pair p1 p2)
.
Notation "p' ≼ p" := (Le_Pat p' p) (at level 50).

Definition Substitution := Var -> option Pat.

Fixpoint mk_subst {p' : Pat} {p : Pat} (pf : p' ≼ p) : Substitution :=
  match pf with
    | le_var p' y             => fun x => if beq_nat x y then Some p' else None
    | le_unit                 => fun x => None
    | le_pair _ _ _ _ pf1 pf2 => fun x => xor_option (mk_subst pf1 x) (mk_subst pf2 x)
  end.

Fixpoint subst_pat' (σ : Substitution) (p0 : Pat) : Pat :=
  match p0 with
  | var y => match σ y with
             | Some p0' => p0'
             | None     => var y
             end
  | unit  => unit
  | pair p1 p2 => pair (subst_pat' σ p1) (subst_pat' σ p2)
  end.
Definition subst_pat {p' : Pat} {p : Pat} (σ : p' ≼ p) (p0 : Pat) : Pat :=
  subst_pat' (mk_subst σ) p0.

Definition shift (σ : Substitution) : Substitution := fun i => σ (S i).



Inductive Consistent_Ctx : Substitution -> Ctx -> Ctx -> Set :=
| Consistent_Nil  : forall σ, Consistent_Ctx σ [] []
| Consistent_None : forall σ Γ Γ',
                    Consistent_Ctx (shift σ) Γ Γ' -> 
                    Consistent_Ctx σ (None :: Γ) (None :: Γ')
| Consistent_Some : forall σ W (Γ Γ' Ω Ω' : Ctx) p0,
                    σ 0 = Some p0 ->
                    WF_Pat Ω p0 W ->
                    Consistent_Ctx (shift σ) Γ Γ' ->
                    Ω ⋓ (Valid (None :: Γ')) = Valid Ω' ->
                    Consistent_Ctx σ (Some W :: Γ) Ω'.

Lemma consistent_split : forall σ (Γ Γ' : Ctx),
      Consistent_Ctx σ Γ Γ' ->
      forall (Γ1 Γ2 : Ctx), Γ1 ⋓ Γ2 = Valid Γ ->
      {Γ1' : Ctx & {Γ2' : Ctx & 
      (Γ1' ⋓ Γ2' = Γ') * Consistent_Ctx σ Γ1 Γ1' * Consistent_Ctx σ Γ2 Γ2'}}%type.
Proof.
  induction 1; intros Γ1 Γ2 merge.
  - apply Ctx_nil_inversion in merge. destruct merge; subst.
    exists []. exists []. split; [split; constructor | constructor].
  - apply Ctx_cons_inversion in merge.
    destruct merge as [o1 [o2 [Γ1' [Γ2' [[[merge1 merge2] merge] merge_none]]]]].
    destruct o1; destruct o2; inversion merge_none.
    destruct (IHConsistent_Ctx Γ1' Γ2' merge) 
             as [Γ1'' [Γ2'' [[merge' consistent1] consistent2]]].
    exists (None :: Γ1'').
    exists (None :: Γ2'').
    inversion merge'. simpl. rewrite H1.
    inversion merge1. 
    inversion merge2.
    split; [split; auto | ].
    * constructor. auto.
    * constructor. auto.
  - apply Ctx_cons_inversion in merge.
    destruct merge as [o1 [o2 [Γ1' [Γ2' [[[merge1 merge2] merge] merge_some]]]]].
    inversion merge1.
    inversion merge2.
    inversion merge.
    destruct (IHConsistent_Ctx Γ1' Γ2')
        as [Γ1'' [Γ2'' [[merge' consistent1] consistent2]]]; auto.
    exists (o1 :: Γ1'').
    exists (o2 :: Γ2'').
    inversion e0.
    destruct o1 as [ W1 | ]; destruct o2 as [ W2 | ]; try (inversion merge_some; fail).
    + simpl in *. inversion merge_some. split; [split | ]; try (constructor; auto; fail). 
      * rewrite merge'. admit.
      * econstructor; eauto. admit.
    + simpl in *. inversion merge_some. split; [split | ]; try (constructor; auto; fail).
      * rewrite merge'. admit.
      * econstructor; eauto. admit.
Admitted.

Lemma consistent_merge : forall σ Γ1 Γ2 Γ1' Γ2' Γ Γ',
                         Consistent_Ctx σ Γ Γ'   ->
                         Consistent_Ctx σ Γ1 Γ1' ->
                         Consistent_Ctx σ Γ2 Γ2' ->
                         Γ1 ⋓ Γ2 = Γ -> Γ1' ⋓ Γ2' = Γ'.
Admitted.

Lemma consistent_singleton : forall x W Γ,
                             SingletonCtx x W Γ ->
                             forall σ Γ', Consistent_Ctx σ Γ Γ' ->
                             WF_Pat Γ' (subst_pat' σ (var x)) W.
Proof.
  induction 1; intros σ Γ' consistent; simpl.
  - inversion consistent; subst.
    rewrite H1.
    inversion H4; subst. simpl in *. 
    assert (Ω = Γ'). admit.
    subst. auto.
  - inversion consistent; subst.
    apply IHSingletonCtx in H2. simpl in *.
    unfold shift in H2. admit.
Admitted.

  


Lemma wf_subst_pat : forall Ω p0 W, WF_Pat Ω p0 W
                  -> forall σ Ω',
                     Consistent_Ctx σ Ω Ω' ->
                     WF_Pat Ω' (subst_pat' σ p0) W.
Proof.
  induction 1; intros σ Ω' consistent; simpl.
  - admit.
  - admit.
  - constructor. subst. inversion consistent. auto.
  - edestruct consistent_split with (σ := σ) (Γ := Γ) (Γ' := Ω') (Γ1 := Γ1) (Γ2 := Γ2)
      as [Γ1' [Γ2' [[merge' consistent1] consistent2]]]; auto.
    econstructor; [exact merge' | | ].
    * apply IHWF_Pat1; auto.
    * apply IHWF_Pat2; auto.
Admitted.
    

(***************************************************************************)

    
Lemma wf_subst_var : forall {p' p} (σ : p' ≼ p) x (Γ Γ' : Ctx) W,
                     lookup Γ x = Some W ->
                     Consistent_Ctx σ Γ Γ' ->
                     WF_Pat Γ' (subst_pat σ (var x)) W.
Admitted.


Lemma consistent_tail : forall {p' p} (σ : p' ≼ p) o (ctx : Ctx),
                        Consistent_Ctx σ (Valid (o :: ctx)) -> Consistent_Ctx σ ctx.
Admitted.

Lemma consistent_singleton : forall {p' p} (σ : p' ≼ p) W (Γ : Ctx) x
                     (consistent : Consistent_Ctx σ Γ),
                     SingletonCtx x W Γ ->
                     WF_Pat (subst_ctx σ consistent) (subst_pat σ (var x)) W.
Proof.
  intros p' p σ W Γ x; revert p' p σ W Γ.
  induction x as [ | x]; intros.
  - inversion H; subst. unfold subst_ctx. simpl. 
    assert (wf_0 : WF_Pat (subst_ctx' σ consistent 0) (subst_pat σ (var 0)) W).
      apply wf_subst_var.
    rewrite eta_OCtx. 
    auto.
  - inversion H; subst. 
    assert (consistent' : Consistent_Ctx σ ctx).
      eapply consistent_tail; eauto. 
    simpl. unfold subst_ctx. simpl.


Lemma wf_subst_pat : forall Ω p0 W, WF_Pat Ω p0 W
                  -> forall p' p (σ : p' ≼ p) (consistent : Consistent_Ctx σ Ω),
                     WF_Pat (subst_ctx σ consistent) (subst_pat σ p0) W.
Proof.
  induction 1 as [x | x | | p1 p2]; intros p' p σ consistent.
  - apply consistent_singleton; auto.
  - apply consistent_singleton; auto.
  - econstructor. subst. apply consistent_empty.
  - econstructor.
    * apply consistent_merge.
    * apply IHWF_Pat1. 
    * apply IHWF_Pat2.
    Unshelve. destruct (consistent_split σ p1 p2); subst; auto.
              destruct (consistent_split σ p1 p2); subst; auto.
Qed.