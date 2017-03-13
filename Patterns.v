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
(*
| wf_qubit : forall x ctx, SingletonCtx x Qubit ctx -> WF_Pat ctx (var x) Qubit
| wf_bit   : forall x ctx, SingletonCtx x Bit ctx -> WF_Pat ctx (var x) Bit
*)
| wf_var  : forall x w ctx, SingletonCtx x w ctx -> WF_Pat ctx (var x) w
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
  inversion m; subst.
  - apply IHwf_p2. inversion H1; subst; auto.
  - apply IHwf_p1. inversion H1; subst; auto.
Qed.

Lemma wf_pat_equiv : forall Γ1 p W, WF_Pat Γ1 p W -> 
      forall Γ2, EquivO Γ1 Γ2 -> WF_Pat Γ2 p W.
Proof.
  induction 1; intros Γ0 eq.
  - inversion eq; constructor. eapply equiv_singleton; eauto.
(*  - inversion eq; constructor. eapply equiv_singleton; eauto.*)
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
    | Some p => Some p (*(shift_pat p)*)
    | None   => None
    end.



Open Scope default_scope.
Fixpoint get_ctx (p : Pat) (W : WType) : OCtx :=
  match p, W with
  | var x,      W       => singleton x W
  | unit,       Unit    => ∅
  | pair p1 p2, W1 ⊗ W2 => get_ctx p1 W1 ⋓ get_ctx p2 W2
  | _,          _       => Invalid
  end.
Close Scope default_scope.


Inductive Consistent_Ctx : Substitution -> OCtx -> Set :=
(*| Consistent_Invalid : forall σ, Consistent_Ctx σ Invalid*)
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

Lemma singleton_equiv : forall x W Γ,
      SingletonCtx x W Γ -> Equiv Γ (singleton x W).
Proof.
  induction 1; simpl.
  - apply EquivCons. apply EquivEmpty; auto. constructor.
  - apply EquivCons. auto.
Qed.

Lemma wf_pat_unique : forall Γ p W,
      WF_Pat Γ p W -> EquivO Γ (get_ctx p W).
Proof.
  induction 1; simpl.
  - apply EquivValid. apply singleton_equiv. auto.
(*  - apply EquivValid. apply singleton_equiv. auto.*)
  - apply EquivValid. apply EquivEmpty; auto. constructor.
  - apply equivO_trans with (Γ2 := Γ1 ⋓ Γ2).
    * apply equivO_symm. apply equiv_merge_merge. auto.
    * apply equiv_merge; auto.
Qed.


Lemma shift_equiv : forall p W,
      WF_Pat (get_ctx (shift_pat p) W) (shift_pat p) W ->
      WF_Pat (get_ctx p W) p W.
Proof.
  induction p as [x | | p1 IHp1 p2 IHp2]; destruct W as [ | | | W1 W2]; 
  simpl; inversion 1; subst;
    try (constructor; inversion H2; auto; fail).
  - constructor. auto.
  - inversion H; subst.
    econstructor; [ | apply IHp1 | apply IHp2].
    * apply mergeO_merge'.
    * assert (wf_p1 : WF_Pat Γ1 (shift_pat p1) W1); auto.
      apply wf_pat_unique in wf_p1.
      apply wf_pat_equiv with (Γ1 := Γ1); auto.
    * assert (wf_p2 : WF_Pat Γ2 (shift_pat p2) W2); auto.
      apply wf_pat_unique in wf_p2.
      apply wf_pat_equiv with (Γ1 := Γ2); auto.
Qed.

Lemma consistent_ctx_correct : forall σ Γ,
      Consistent_Ctx σ Γ ->
      forall x p W, σ x = Some p -> 
                    lookupO Γ x = Some W -> 
                    WF_Pat (get_ctx p W) p W.
Proof.
  induction 1; intros x p W' eq_σ eq_Γ.
  - inversion eq_Γ.
(*  - inversion eq_Γ.*)
  - destruct x; [ inversion eq_Γ | ].
    simpl in eq_Γ.
(*    apply shift_equiv.*)
    eapply IHConsistent_Ctx; eauto.
    unfold shift. rewrite eq_σ. auto.
  - destruct x.
    * inversion eq_Γ; subst.
      rewrite e in eq_σ. inversion eq_σ; subst.
      auto.
    * simpl in eq_Γ.
(*      apply shift_equiv.*)
      eapply IHConsistent_Ctx; eauto.
      unfold shift. rewrite eq_σ. auto.
Qed.

Lemma consistent_ctx_empty : forall Γ, EmptyCtx Γ -> forall σ,
      Consistent_Ctx σ Γ.
Proof.
  induction 1; intros; constructor; auto.
Qed.

Lemma consistent_equiv : forall Γ1 Γ2,
      EquivO Γ1 Γ2 -> 
      forall σ, Consistent_Ctx σ Γ1 -> Consistent_Ctx σ Γ2.
Proof.
  destruct 1 as [ | Γ1 Γ2 equiv].
  - intros. inversion H.
  - induction equiv; intros σ consistent.
    * apply consistent_ctx_empty; auto.
    * inversion consistent; subst.
      + constructor; auto.
      + econstructor; eauto.
Qed.

Lemma consistent_split : forall σ (Γ : Ctx),
      Consistent_Ctx σ Γ ->
      forall Γ1 Γ2, Merge Γ1 Γ2 Γ ->
      Consistent_Ctx σ Γ1 * Consistent_Ctx σ Γ2.
Proof.
  intros σ Γ consistent Γ1 Γ2 merge.
  remember (Valid Γ) as Γ'.
  revert Γ HeqΓ' Γ1 Γ2 merge.
  induction consistent; intros Γ' eq Γ1 Γ2 merge; inversion eq; subst.
  - inversion merge; subst; split;
      apply consistent_ctx_empty; auto;
      (apply equiv_empty with (Γ1 := []); [apply equiv_symm; auto | constructor ]).
  - inversion merge; subst; split;
    try (apply consistent_ctx_empty; auto; fail).
    * eapply consistent_equiv; 
        [apply EquivValid; apply equiv_symm; eauto | constructor; auto].
    * eapply consistent_equiv; 
        [apply EquivValid; apply equiv_symm; eauto | constructor; auto].
    * inversion H3; subst; rename Γ0 into Γ1, Γ3 into Γ2.
      constructor.
      destruct IHconsistent with (Γ0 := Γ) (Γ1 := Γ1) (Γ2 := Γ2); auto.
    * inversion H3; subst; rename Γ0 into Γ1, Γ3 into Γ2.
      constructor.
      destruct IHconsistent with (Γ0 := Γ) (Γ1 := Γ1) (Γ2 := Γ2); auto.
  - inversion merge; subst; split;
    try (apply consistent_ctx_empty; auto; fail).
    * eapply consistent_equiv; 
      [ apply EquivValid; apply equiv_symm; eauto | econstructor; eauto ].
    * eapply consistent_equiv; 
      [ apply EquivValid; apply equiv_symm; eauto | econstructor; eauto ].
    * rename Γ0 into Γ1, Γ3 into Γ2.
      destruct IHconsistent with (Γ0 := Γ) (Γ1 := Γ1) (Γ2 := Γ2) as [IH1 IH2]; auto.
      inversion H3; subst; econstructor; eauto.
    * rename Γ0 into Γ1, Γ3 into Γ2.
      destruct IHconsistent with (Γ0 := Γ) (Γ1 := Γ1) (Γ2 := Γ2) as [IH1 IH2]; auto.
      inversion H3; subst; econstructor; eauto.
Qed.
  

Lemma consistentO_split : forall σ Γ,
      Consistent_Ctx σ Γ ->
      forall Γ1 Γ2, MergeO Γ1 Γ2 Γ ->
      Consistent_Ctx σ Γ1 * Consistent_Ctx σ Γ2.
Proof.
  intros σ Γ consistent Γ1 Γ2 merge. 
  destruct merge; try (split; 
    try constructor;
    eapply consistent_equiv; eauto; apply equivO_symm; eauto; constructor; auto;
    fail);
    try (inversion consistent; fail).
    eapply consistent_split; eauto.
Qed.



Lemma consistent_merge : forall Γ1 Γ2 Γ σ,
      Consistent_Ctx σ Γ1 -> Consistent_Ctx σ Γ2 ->
      Γ1 ⋓ Γ2 = Valid Γ ->  Consistent_Ctx σ Γ.
Proof.
  destruct Γ1 as [ | Γ1]; try (inversion 3; fail).
  destruct Γ2 as [ | Γ2]; try (inversion 3; fail); revert Γ2.
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


(* (cons_o None (get_ctx p W)) = (get_ctx (shift_pat p) W). *)
Program Fixpoint subst_ctx (σ : Substitution) (Γ : Ctx) : OCtx :=
  match Γ with
  | [] => ∅
  | None   :: Γ' => (subst_ctx (shift σ) Γ')
  | Some W :: Γ' => match σ 0 with
                    | None => Invalid
                    | Some p => get_ctx p W ⋓ subst_ctx (shift σ) Γ'
                    end
  end.
Definition subst_ctx' σ Γ := 
  match Γ with
  | Valid Γ' => subst_ctx σ Γ'
  | Invalid => Invalid
  end.

Lemma consistent_empty : forall (Γ : Ctx),
      EmptyCtx Γ -> forall σ, EmptyOCtx (subst_ctx σ Γ).
Proof.
  induction 1; intros σ; simpl; auto.
  do 2 constructor.
Qed.


Hint Unfold subst_ctx': auto.

Lemma equiv_subst : forall σ Γ1 Γ2,
                    Equiv Γ1 Γ2 -> 
                    EquivO (subst_ctx σ Γ1) (subst_ctx σ Γ2).
Proof.
    intros σ Γ1 Γ2 eq; revert σ. 
    induction eq; intros σ.
    * apply EquivOEmpty;
      apply consistent_empty; auto.
    * destruct o as [ W |]; simpl; auto.
      remember (σ 0) as x; 
      destruct x; simpl; try (constructor; fail).
      apply equiv_merge; auto.
      apply equivO_refl.
Qed.

Lemma equivO_subst : forall Γ1 Γ2,
                     EquivO Γ1 Γ2 ->
                     forall σ, EquivO (subst_ctx' σ Γ1) (subst_ctx' σ Γ2).
Proof.
  destruct 1; intros; simpl; try constructor.
  apply equiv_subst; auto.
Qed.
    

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
  - apply MergeOEmptyL; [apply consistent_empty | apply equiv_subst]; auto.
  - apply MergeOEmptyR; [apply consistent_empty | apply equiv_subst]; auto.
  - inversion m; subst; simpl.
    * inversion consistent1. 
      inversion consistent2. 
      inversion consistent. 
      apply IHMerge; auto.
    * inversion consistent; subst.
      rewrite H2. 
      rewrite <- merge_nil_l with (Γ := subst_ctx (shift σ) Γ2).
      apply mergeO_merge. 
      + apply MergeOEmptyR; [repeat constructor | apply equivO_refl].
      + inversion consistent1.
        inversion consistent2.
        apply IHMerge; auto.
    * inversion consistent; subst.
      rewrite H2. 
      rewrite <- merge_nil_l with (Γ := subst_ctx (shift σ) Γ1).
      apply mergeO_merge.
      + apply MergeOEmptyL; [ repeat constructor | apply equivO_refl].
      + inversion consistent1.
        inversion consistent2.
        apply IHMerge; auto.
Qed.


Lemma subst_OCtx_split : forall (Γ Γ1 Γ2 : OCtx),
      MergeO Γ1 Γ2 Γ ->
      forall σ, 
      Consistent_Ctx σ Γ ->
      Consistent_Ctx σ Γ1 ->
      Consistent_Ctx σ Γ2 ->
      MergeO (subst_ctx' σ Γ1) (subst_ctx' σ Γ2) (subst_ctx' σ Γ).
Proof.
  induction 1; intros σ consistent consistent1 consistent2; simpl.
  - inversion consistent.
  - inversion consistent.
  - apply subst_ctx_split; auto.
Qed.


Lemma get_ctx_shift : forall Γ (p : Pat) W,
    WF_Pat Γ p W -> 
    EquivO (cons_o None (get_ctx p W)) (get_ctx (shift_pat p) W).
Proof.
  induction 1; simpl.
  - apply equivO_refl.
  - repeat constructor. 
  - apply equivO_trans 
      with (cons_o None (get_ctx p1 w1) ⋓ cons_o None (get_ctx p2 w2)).
    * rewrite cons_distr_merge. apply equivO_refl.
    * apply equiv_merge; auto.
Qed.

Lemma singleton_get_ctx : forall x W Γ,
      SingletonCtx x W Γ ->
      forall σ p, Consistent_Ctx σ Γ ->
                σ x = Some p -> 
                EquivO (subst_ctx σ Γ) (get_ctx p W).
Proof.
  induction 1; intros σ p consistent σ_eq; simpl; try rewrite σ_eq.
  - inversion consistent; subst. 
    rewrite merge_symm. 
    apply equiv_merge_empty.
    apply consistent_empty; auto.
  - inversion consistent; subst.
    apply IHSingletonCtx; auto.
    unfold shift. rewrite σ_eq. auto.
Qed.


Lemma singleton_consistent_lookup : forall x W Γ,
    SingletonCtx x W Γ ->
    forall σ, Consistent_Ctx σ Γ ->
    {p : Pat & σ x = Some p}.
Proof.
  induction 1; inversion 1; subst.
  - exists p0; auto.
  - destruct IHSingletonCtx with (σ := shift σ) as [p0 IH]; auto.
    exists p0. unfold shift in IH. remember (σ (S x)) as y.
    destruct y; inversion IH; auto.
Qed.

Lemma singleton_lookup : forall x W Γ,
    SingletonCtx x W Γ -> lookupO Γ x = Some W.    
Proof.
  induction 1; simpl; auto.
Qed.

Lemma consistent_singleton : forall x W Γ σ,
      SingletonCtx x W Γ ->
      Consistent_Ctx σ Γ ->
      WF_Pat (subst_ctx σ Γ) (subst_pat' σ (var x)) W.
Proof. 
  intros x W Γ σ singleton consistent.
  remember (σ x) as p0.
  destruct p0 as [p0' | ]; simpl; rewrite <- Heqp0.
  - apply wf_pat_equiv with (Γ1 := get_ctx p0' W). 
    * eapply consistent_ctx_correct; eauto.
      apply singleton_lookup; auto.
    * apply equivO_symm. eapply singleton_get_ctx; eauto.
  - edestruct singleton_consistent_lookup as [p pf]; eauto.
    rewrite pf in *. inversion Heqp0.
Qed.
    


Lemma wf_subst_pat : forall Ω p0 W, WF_Pat Ω p0 W
                  -> forall σ,
                     Consistent_Ctx σ Ω ->
                     WF_Pat (subst_ctx' σ Ω) (subst_pat' σ p0) W.
Proof.
  induction 1; intros σ consistent.
  - apply consistent_singleton; auto.
  - simpl. apply wf_pat_equiv with (Γ1 := ∅); try (constructor; constructor).
    apply EquivOEmpty; [ repeat constructor | ].
    apply consistent_empty; auto.
  - simpl.
    destruct consistentO_split with (σ:=σ) (Γ1:=Γ1) (Γ2:=Γ2) (Γ:=Γ)
        as [consistent1 consistent2]; auto. 
    econstructor; eauto.
    unfold subst_ctx'.
    apply subst_OCtx_split; auto.
Qed.

