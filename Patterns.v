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

Inductive WF_Pat : OCtx -> Pat -> WType -> Set :=
| wf_qubit : forall x ctx, SingletonCtx x Qubit ctx -> WF_Pat ctx (var x) Qubit
| wf_bit   : forall x ctx, SingletonCtx x Bit ctx -> WF_Pat ctx (var x) Bit
(*| wf_var  : forall x w ctx, SingletonCtx x w ctx -> WF_Pat ctx (var x) w*)
| wf_unit : forall ctx, EmptyCtx ctx -> WF_Pat ctx unit One
| wf_pair : forall (Γ1 Γ2 Γ : OCtx) w1 w2 p1 p2, 
            MergeO Γ1 Γ2 Γ ->
            WF_Pat Γ1 p1 w1 -> WF_Pat Γ2 p2 w2 ->
            WF_Pat Γ (pair p1 p2) (Tensor w1 w2)
.

Lemma wf_pat_not_invalid : forall p W, WF_Pat Invalid p W -> False.
Proof.
  remember Invalid as Γ eqn:H.
  intros p W wf_p.
  revert H.
  induction wf_p; subst; inversion 1.
  rewrite H in *.
  inversion m.
Qed.

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

Fixpoint shift_pat (p : Pat) : Pat :=
  match p with
  | var x => var (S x)
  | unit  => unit
  | (p1,p2) => (shift_pat p1, shift_pat p2)
  end.
Definition shift (σ : Substitution) : Substitution := fun i => 
    match σ (S i) with
    | Some p => Some (shift_pat p)
    | None   => None
    end.
(*
Inductive Maps_To : Var -> WType -> Ctx -> Set :=
| WSO : forall Γ W, Maps_To O W (Some W :: Γ)
| WSS : forall Γ W o x, Maps_To x W Γ -> Maps_To (S x) W (o :: Γ)
.

Definition Consistent_Ctx σ Γ := forall x W p0, Maps_To x W Γ ->
                                             σ x = Some p0 -> 
                                             { Ω : Ctx & WF_Pat Ω p0 W }.
*)

Open Scope default_scope.
Fixpoint get_ctx (p : Pat) (W : WType) : OCtx :=
  match (p,W) with
  | (var x, W)   => singleton x W
  | (unit,  Unit) => ∅
  | (pair p1 p2, W1 ⊗ W2) => get_ctx p1 W1 ⋓ get_ctx p2 W2
  | (_,_)                 => Invalid
  end.
Close Scope default_scope.


Inductive Consistent_Ctx : Substitution -> OCtx -> Set :=
| Consistent_Nil  : forall σ, Consistent_Ctx σ ∅
| Consistent_None : forall σ Γ,
                    Consistent_Ctx (shift σ) (Valid Γ) -> 
                    Consistent_Ctx σ (Valid (None :: Γ))
| Consistent_Some : forall σ W (Γ : Ctx) p0,
                    σ 0 = Some p0 ->
                    WF_Pat (get_ctx p0 W) p0 W ->
                    Consistent_Ctx (shift σ) (Valid Γ) ->
                    Consistent_Ctx σ (Valid (Some W :: Γ))
.



Lemma consistent_split : forall σ Γ,
      Consistent_Ctx σ Γ ->
      forall Γ1 Γ2, Γ1 ⋓ Γ2 = Γ ->
      Consistent_Ctx σ Γ1 * Consistent_Ctx σ Γ2.
Proof.
  induction 1; intros Γ1 Γ2 merge.
  - apply Ctx_nil_inversion in merge. destruct merge; subst.
    split; constructor.
  - apply Ctx_cons_inversion in merge. 
    destruct merge as [o1 [o2 [Γ1' [Γ2' [[[eq1 eq2] merge'] mergeo]]]]].
    destruct o1; destruct o2; try inversion mergeo.
    inversion eq1; inversion eq2; subst.
    destruct (IHConsistent_Ctx Γ1' Γ2'); auto.
    split; constructor; auto.
  - apply Ctx_cons_inversion in merge.
    destruct merge as [o1 [o2 [Γ1' [Γ2' [[[eq1 eq2] merge'] mergeo]]]]].
    destruct IHConsistent_Ctx with (Γ1 := Γ1') (Γ2 := Γ2'); auto.
    inversion eq1; inversion eq2.
    destruct o1; destruct o2; try inversion mergeo; subst;
    split; econstructor; eauto.
Qed.


Lemma consistent_merge : forall Γ1 Γ2 Γ σ,
      Consistent_Ctx σ Γ1 -> Consistent_Ctx σ Γ2 ->
      Γ1 ⋓ Γ2 = Valid Γ ->  Consistent_Ctx σ Γ.
Proof.
  destruct Γ1 as [ | Γ1]; try (inversion 1; fail).
  destruct Γ2 as [ | Γ2]; try (inversion 2; fail); revert Γ2.
  induction Γ1 as [ | [W1 | ]];
  destruct  Γ2 as [ | [W2 | ]];
    intros Γ σ consistent1 consistent2 merge;
    try (inversion merge; subst; auto; fail);
    inversion consistent1;
    inversion consistent2; subst;
    simpl in merge;
    remember (merge' Γ1 Γ2) as Γ';
    destruct Γ' as [ | Γ']; inversion merge; subst;
    econstructor; eauto.
Qed.


Program Fixpoint subst_ctx (σ : Substitution) (Γ : Ctx) : OCtx :=
  match Γ with
  | [] => ∅
  | None   :: Γ' => cons_o None (subst_ctx (shift σ) Γ')
  | Some W :: Γ' => match σ 0 with
                    | None => Invalid
                    | Some p => get_ctx p W ⋓ (cons_o None (subst_ctx (shift σ) Γ'))
                    end
  end.
Definition subst_ctx' σ Γ := 
  match Γ with
  | Valid Γ' => subst_ctx σ Γ'
  | Invalid => Invalid
  end.

Lemma consistent_empty : forall (Γ : Ctx),
      EmptyCtx Γ -> forall σ, subst_ctx σ Γ = Γ.
Proof.
  induction 1; intros σ; simpl; auto.
  rewrite IHEmptyCtx. auto.
Qed.

Hint Unfold subst_ctx': auto.
Lemma consistent_valid : forall σ (Γ : OCtx), Consistent_Ctx σ Γ ->
      { Γ' : Ctx & subst_ctx' σ Γ = Valid Γ' }.
Proof.
  induction 1; simpl.
  - exists []; auto. 
  - destruct IHConsistent_Ctx as [Γ' IH].
    exists (None :: Γ'); simpl. unfold subst_ctx' in IH. rewrite IH.
    simpl. reflexivity.
  - destruct IHConsistent_Ctx as [Γ' IH].
    rewrite e.
    unfold subst_ctx' in IH.
    rewrite IH.
    simpl.
    admit.
Admitted.

Lemma equiv_subst : forall σ Γ1 Γ2,
                    EquivO Γ1 Γ2 -> 
                    EquivO (subst_ctx' σ Γ1) (subst_ctx' σ Γ2).
Admitted.

Lemma subst_ctx_split : forall (Γ Γ1 Γ2 : Ctx),
      Merge Γ1 Γ2 Γ ->
      forall σ, 
      Consistent_Ctx σ Γ ->
      Consistent_Ctx σ Γ1 ->
      Consistent_Ctx σ Γ2 ->
      MergeO (subst_ctx σ Γ1) (subst_ctx σ Γ2) (subst_ctx σ Γ).
Proof.
  induction 1; intros σ consistent consistent1 consistent2;
    unfold subst_ctx' in *;
    subst.
  - rewrite consistent_empty with (Γ := Γ1); auto.
    apply MergeOEmptyL; auto.
    apply EquivValid in e0; apply equiv_subst with (σ := σ) in e0.
    unfold subst_ctx' in e0; auto.
  - rewrite consistent_empty with (Γ := Γ2); auto.
    apply MergeOEmptyR; auto.
    apply EquivValid in e0; apply equiv_subst with (σ := σ) in e0.
    unfold subst_ctx' in e0; auto.
  - inversion m; subst; simpl.
    * apply MergeOCons; [constructor | ].
      inversion consistent; subst.
      apply IHMerge; auto.
      + inversion consistent1; auto.
      + inversion consistent2; auto.
    * inversion consistent; subst.
      rewrite H2. admit.
    * inversion consistent; subst.
      rewrite H2. admit.
Admitted.

Lemma singleton_get_ctx : forall x W Γ,
      SingletonCtx x W Γ ->
      forall σ p, Consistent_Ctx σ Γ ->
                σ x = Some p -> 
                EquivO (subst_ctx σ Γ) (get_ctx p W).
Proof.
  induction 1; intros σ p consistent σ_eq; simpl; try rewrite σ_eq.
  - inversion consistent; subst. 
    rewrite consistent_empty; auto.
    apply equivO_symm.
    apply equiv_merge_empty.
    constructor; auto.
  - inversion consistent; subst.
    eapply IHSingletonCtx in H2; auto.
    admit. admit.
Admitted.

Lemma wf_pat_var_S : forall σ (Γ : Ctx) x W,
      Consistent_Ctx σ (Valid (None :: Γ)) ->
      WF_Pat (subst_ctx (shift σ) Γ) (subst_pat' (shift σ) (var x)) W ->
      WF_Pat (cons_o None (subst_ctx σ Γ)) (subst_pat' σ (var (S x))) W.
Proof.
Admitted.



Lemma wf_pat_consistent : forall Γ1 p W, WF_Pat Γ1 p W -> 
      forall Γ2, EquivO Γ1 Γ2 -> WF_Pat Γ2 p W.
Proof.
  induction 1; intros Γ0 eq.
  - inversion eq; constructor. eapply equiv_singleton; eauto.
  - inversion eq; constructor. eapply equiv_singleton; eauto.
  - inversion eq; constructor. eapply equiv_empty; eauto.
  - inversion m; subst.
    * (* Γ2 is invalid *) edestruct (wf_pat_not_invalid); eauto.
    * (* Γ1 is invalid *) edestruct (wf_pat_not_invalid); eauto.
    * inversion eq; subst.
      destruct (equiv_split _ _ _ _ H1 H3) as [Γ1' [Γ2' [[merge' eq1] eq2]]].
      econstructor; [ | apply IHWF_Pat1; constructor; eauto 
                      | apply IHWF_Pat2; constructor; eauto].
      constructor; auto.
Qed.
    

Lemma consistent_singleton : forall x W Γ σ,
      SingletonCtx x W Γ ->
      Consistent_Ctx σ Γ ->
      WF_Pat (subst_ctx σ Γ) (subst_pat' σ (var x)) W.
Proof. 
  induction x as [ | x]; intros W  Γ σ pf_singleton consistent;
    inversion pf_singleton; subst.
  - inversion consistent; subst. simpl. rewrite H2.
    rewrite consistent_empty; auto.
    apply wf_pat_consistent with (Γ1 := get_ctx p0 W); auto.
    apply equiv_merge_empty.
    constructor; auto.
  - inversion consistent; subst. 
    eapply IHx in H2; eauto.
    apply wf_pat_var_S; auto.
Qed.


Lemma wf_subst_pat : forall Ω p0 W, WF_Pat Ω p0 W
                  -> forall σ,
                     Consistent_Ctx σ Ω ->
                     WF_Pat (subst_ctx' σ Ω) (subst_pat' σ p0) W.
Proof.
  induction 1; intros σ consistent.
  - apply consistent_singleton; auto.
  - apply consistent_singleton; auto.
  - simpl. apply wf_pat_consistent with (Γ1 := ∅); try (constructor; constructor).
    rewrite consistent_empty; auto.
    constructor. apply EquivEmpty; auto. constructor.
  - simpl. 
    destruct consistent_split with (σ:=σ) (Γ1:=Γ1) (Γ2:=Γ2) (Γ:=Γ)
        as [consistent1 consistent2]; auto. 
    econstructor; eauto.
    apply subst_ctx_split; auto.
Qed.

