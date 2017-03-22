Require Import Arith.
Require Import Program.
Require Import Contexts.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Inductive Pat := var : Var -> Pat | unit | pair : Pat -> Pat -> Pat.

(* Dangerous to take this notation *)
Notation "a , b" := (Datatypes.pair a b) (at level 11, left associativity) : default_scope.
Notation "w1 , w2" := (pair w1 w2) (at level 11, left associativity) : circ_scope.

(*
Inductive WF_Pat : Ctx -> Pat -> WType -> Set :=
(*
| wf_qubit : forall x ctx, SingletonCtx x Qubit ctx -> WF_Pat ctx (var x) Qubit
| wf_bit   : forall x ctx, SingletonCtx x Bit ctx -> WF_Pat ctx (var x) Bit
*)
| wf_var  : forall x w ctx, SingletonCtx x w ctx -> WF_Pat ctx (var x) w
| wf_unit : WF_Pat [] unit One
| wf_pair : forall (Γ1 Γ2 Γ : Ctx) w1 w2 p1 p2, 
            Valid Γ = Γ1 ⋓ Γ2 ->
            WF_Pat Γ1 p1 w1 -> WF_Pat Γ2 p2 w2 ->
            WF_Pat Γ (pair p1 p2) (Tensor w1 w2)
.
*)

Inductive WF_Pat : OCtx -> Pat -> WType -> Set :=
(*
| wf_qubit : forall x ctx, SingletonCtx x Qubit ctx -> WF_Pat ctx (var x) Qubit
| wf_bit   : forall x ctx, SingletonCtx x Bit ctx -> WF_Pat ctx (var x) Bit
*)
| wf_var  : forall x w ctx, SingletonCtx x w ctx -> WF_Pat ctx (var x) w
| wf_unit : WF_Pat ∅ unit One
| wf_pair : forall Γ1 Γ2 Γ w1 w2 p1 p2, 
            Valid Γ = Γ1 ⋓ Γ2 ->
            WF_Pat Γ1 p1 w1 -> WF_Pat Γ2 p2 w2 ->
            WF_Pat (Valid Γ) (pair p1 p2) (Tensor w1 w2)
.

(* Now immediate 
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
*)

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
  | unit,       One     => ∅
  | pair p1 p2, W1 ⊗ W2 => get_ctx p1 W1 ⋓ get_ctx p2 W2
  | _,          _       => Invalid
  end.
Close Scope default_scope.

Lemma wf_pat_unique : forall Γ p W,
      WF_Pat Γ p W -> Γ = (get_ctx p W).
Proof.
  induction 1; simpl.
  - apply ctx_octx. apply singleton_equiv. assumption.
  - reflexivity.
  - rewrite <- IHWF_Pat1, <- IHWF_Pat2. assumption.
Qed.


Fixpoint units (p : Pat) : bool :=
  match p with
  | unit => true
  | p1, p2 => units p1 && units p2
  | _ => false
  end.

Lemma shift_pat_units : forall p, units p = units (shift_pat p).
Proof. induction p; auto. simpl. rewrite IHp1, IHp2. reflexivity. Qed.

Lemma get_ctx_units : forall p W, units p = true ->
                             get_ctx p W = ∅ \/ get_ctx p W = Invalid.
Proof.
  induction p; intros W H; inversion H; subst.
  + destruct W; eauto.
  + destruct W; eauto.
    simpl.
    apply andb_prop in H1 as [H1 H2].
    destruct (IHp1 W1 H1) as [E1|E1], (IHp2 W2 H2) as [E2|E2]; rewrite E1, E2; auto.
Qed.

Lemma get_ctx_shift_units : forall p W, units p = true -> 
                             get_ctx p W = get_ctx (shift_pat p) W.
Proof. induction p.
       - simpl; intros; congruence. 
       - reflexivity. 
       - intros. destruct W; auto.
         simpl in H. apply andb_prop in H as [H1 H2].
         simpl.
         rewrite IHp1, IHp2; auto. 
Qed.

Lemma get_ctx_shift : forall p W, units p = false -> 
                             get_ctx (shift_pat p) W = cons_o None (get_ctx p W).
Proof.
  induction p; intros W Neq; trivial.
  + inversion Neq. 
  + destruct W; auto.
    simpl in *.
    destruct (units p1) eqn:U1, (units p2) eqn:U2.
    - inversion Neq.
    - rewrite IHp2; trivial.
      rewrite <- get_ctx_shift_units; trivial.
      destruct (get_ctx_units p1 W1) as [H | H]; trivial.
      rewrite H; destruct (get_ctx p2 W2); reflexivity.
      rewrite H; destruct (get_ctx p2 W2); reflexivity.
    - rewrite IHp1; trivial.
      rewrite <- get_ctx_shift_units; trivial.
      destruct (get_ctx_units p2 W2) as [H | H]; trivial.
      rewrite H; destruct (get_ctx p1 W1); rewrite 2 merge_nil_r; reflexivity.
      rewrite H; destruct (get_ctx p1 W1); reflexivity.
    - rewrite IHp1, IHp2; trivial.
      Search cons_o.
      rewrite cons_distr_merge; reflexivity.
Qed.

Lemma shift_valid : forall p W,
  {Γ : Ctx & get_ctx (shift_pat p) W = Valid Γ} -> 
  {Γ': Ctx & get_ctx p W = Valid Γ'}.
Proof.
  intros p W [Γ V].
  destruct (units p) eqn:Eq.
  - eapply get_ctx_shift_units in Eq.
    rewrite <- Eq in V.
    eauto.
  - eapply get_ctx_shift in Eq.
    rewrite Eq in V.
    destruct (get_ctx p W).
    inversion V.
    eauto.
Qed.    

Lemma shift_equiv : forall p W,
      WF_Pat (get_ctx (shift_pat p) W) (shift_pat p) W ->
      WF_Pat (get_ctx p W) p W.
Proof.
  induction p; intros W WF. 
  + simpl in *. inversion WF; subst. inversion H1; subst.
    constructor. assumption.
  + simpl in *. assumption.
  + specialize (shift_valid (p1,p2) W); intros V.
    destruct W; simpl in *; inversion WF. subst.
    destruct (get_ctx p1 W1 ⋓ get_ctx p2 W2) as [|Γ'] eqn:Eq.     
    - destruct V as [Γ' F]. eauto.
      inversion F.
    - econstructor.
      symmetry. apply Eq.
      apply IHp1. 
      specialize (wf_pat_unique _ _ _ H5). intros Eq2. rewrite <- Eq2. assumption.
      apply IHp2. 
      specialize (wf_pat_unique _ _ _ H6). intros Eq2. rewrite <- Eq2. assumption.
Qed.


Inductive Consistent_Pat : option Pat -> option WType -> Ctx -> Set :=
| Consistent_None_None : Consistent_Pat None None []
| Consistent_None_Some : forall W, Consistent_Pat None (Some W) [Some W]
| Consistent_Some_None : forall p, Consistent_Pat (Some p) None []
| Consistent_Some_Some : forall W p Γ, 
    get_ctx p W = Valid Γ -> WF_Pat Γ p W -> 
    Consistent_Pat (Some p) (Some W) Γ
.
Inductive Consistent_Ctx : Substitution -> Ctx -> Ctx -> Set :=
| Consistent_Nil  : forall σ, Consistent_Ctx σ [] []
| Consistent_Cons : forall σ (Γ Γ' Γ0 Γ0' : Ctx) w,
                    Consistent_Ctx (shift σ) Γ Γ' ->
                    Consistent_Pat (σ 0) w  Γ0 ->
                    Γ0 ⋓ Γ' = Valid Γ0' ->
                    Consistent_Ctx σ (w :: Γ) Γ0'
.

(* 
Inductive Consistent_Ctx : Substitution -> Ctx -> Ctx -> Set :=
| Consistent_Nil  : forall σ, Consistent_Ctx σ [] []
| Consistent_Γ_None : forall σ Γ Γ',
                    Consistent_Ctx (shift σ) Γ Γ' -> 
                    Consistent_Ctx σ (None :: Γ) Γ'
| Consistent_σ_None : forall σ Γ Γ' Γ'' (W : WType),
                      σ 0 = None ->
                      Consistent_Ctx (shift σ) Γ Γ' ->
                      Valid [Some W] ⋓ Γ' = Valid Γ'' ->
                      Consistent_Ctx σ (Some W :: Γ) Γ''
| Consistent_Some : forall σ Γ Γ' p W Γ_p Γ_p',
                    σ 0 = Some p ->
                    Consistent_Ctx (shift σ) Γ Γ' ->
                    get_ctx p W = Valid Γ_p ->
                    WF_Pat Γ_p p W ->
                    Γ' ⋓ Γ_p = Valid Γ_p' ->
                    Consistent_Ctx σ (Some W :: Γ) Γ_p'.
*)

(* Previously lower down. Can move later. *)
(* (cons_o None (get_ctx p W)) = (get_ctx (shift_pat p) W). *)
Program Fixpoint subst_ctx (σ : Substitution) (Γ : Ctx) : OCtx :=
  match Γ with
  | [] => ∅
  | None   :: Γ' => (subst_ctx (shift σ) Γ')
  | Some W :: Γ' => match σ 0 with
                    | None => Valid [Some W] ⋓ subst_ctx (shift σ) Γ'
                    | Some p => get_ctx p W  ⋓ subst_ctx (shift σ) Γ'
                    end
  end.
Definition subst_ctx_O (σ : Substitution) (Γ : OCtx) : OCtx :=
  match Γ with
  | Invalid => Invalid
  | Valid Γ => subst_ctx σ Γ
  end.

Lemma consistent_valid : forall σ Γ Γ',
      Consistent_Ctx σ Γ Γ' -> subst_ctx σ Γ = Valid Γ'.
Proof.
  intros σ Γ Γ' H.
  induction H; auto.
  inversion c; subst.
  * rewrite merge_nil_l in *. simpl. rewrite IHConsistent_Ctx; auto.
  * simpl. rewrite <- H1. rewrite <- e.
    rewrite IHConsistent_Ctx.
    destruct Γ' as [ | Γ']; auto.
  * simpl. rewrite merge_nil_l in *. rewrite <- e. auto.
  * simpl. rewrite <- H0. rewrite H1. rewrite IHConsistent_Ctx. auto.
Qed.

Lemma consistent_ctx_correct : forall σ Γ Γ',
      Consistent_Ctx σ Γ Γ' ->
      forall x p W, σ x = Some p -> 
                    lookup Γ x = Some W -> 
                    WF_Pat (get_ctx p W) p W.
Proof.
  induction 1; intros x p' W' eq_σ eq_Γ; [inversion eq_Γ | ].
  remember (σ 0) as p0.
  inversion c; subst.
  - destruct x as [ | x]; [inversion eq_Γ | ].
    simpl in eq_Γ.
    eapply IHConsistent_Ctx; [ | eauto].
    unfold shift; rewrite eq_σ; auto.
  - destruct x as [ | x]; simpl in eq_Γ.
    * rewrite eq_σ in H0; inversion H0.
    * eapply IHConsistent_Ctx; [ | eauto].
      unfold shift; rewrite eq_σ; auto.
  - destruct x as [ | x]; [inversion eq_Γ | ].
    simpl in eq_Γ.
    eapply IHConsistent_Ctx; [ | eauto].
    unfold shift; rewrite eq_σ; auto.
  - destruct x as [ | x]; simpl in eq_Γ.
    * inversion eq_Γ; subst.
      rewrite eq_σ in H2; inversion H2; subst.
      rewrite <- H0 in H1; auto.
    * eapply IHConsistent_Ctx; [ | eauto].
      unfold shift; rewrite eq_σ; auto.
Qed.

(*
  - inversion eq_Γ.
  - destruct x; [ inversion eq_Γ | ].
    simpl in eq_Γ.
    eapply IHConsistent_Ctx; eauto.
    unfold shift. rewrite eq_σ. auto.
  - destruct x.
    * inversion eq_Γ; subst.
      rewrite e in eq_σ. inversion eq_σ; subst.
    * simpl in eq_Γ.
      eapply IHConsistent_Ctx; eauto.
      unfold shift. rewrite eq_σ. auto.
  - destruct x.
    * inversion eq_Γ; subst.
      rewrite e in eq_σ. inversion eq_σ; subst.
      rewrite e0; auto.
    * simpl in eq_Γ.
      eapply IHConsistent_Ctx; eauto.
      unfold shift. rewrite eq_σ. auto.
Qed.*)

Definition Consistent_Ctx' σ Γ := {Γ' : Ctx & Consistent_Ctx σ Γ Γ'}.

Lemma consistent_ctx_unique : forall σ (Γ Γ1 Γ2 : Ctx),
      Consistent_Ctx σ Γ Γ1 -> Consistent_Ctx σ Γ Γ2 -> Γ1 = Γ2.
Admitted.

Lemma subst_ctx_split : forall (Γ Γ1 Γ2 : Ctx),
      Valid Γ = Γ1 ⋓ Γ2 ->
      forall σ Γ' Γ1' Γ2', 
      Consistent_Ctx σ Γ Γ' ->
      Consistent_Ctx σ Γ1 Γ1' ->
      Consistent_Ctx σ Γ2 Γ2' ->
       Valid Γ' = Γ1' ⋓ Γ2'.
Proof. 
  induction Γ as [|o Γ IHΓ] ; intros Γ1 Γ2 M σ Γ' Γ1' Γ2' C C1 C2.
  + inversion C; subst.
    destruct Γ1 as [ | o1 Γ1]; destruct Γ2 as [ | o2 Γ2]; try (inversion M; fail).
    * inversion C1; inversion C2; auto.
    * simpl in M. destruct o1; destruct o2; try (inversion M; fail);
        simpl in M; destruct (merge' Γ1 Γ2); inversion M. 
  + destruct Γ1 as [ | o1 Γ1]; destruct Γ2 as [ | o2 Γ2]; inversion M; subst.
(*      try rewrite merge_nil_l in *; try rewrite merge_nil_r in *; auto.*)
    * inversion C1. rewrite merge_nil_l in *. f_equal.
      eapply consistent_ctx_unique with (Γ1 := Γ') (Γ2 := Γ2'); eauto.
    * inversion C2; subst. rewrite merge_nil_r in *. f_equal.
      eapply consistent_ctx_unique; eauto.
    * symmetry in M; apply ctx_cons_inversion in M as [M Mo]; symmetry in M.
      inversion C; subst. rewrite <- H6.
      inversion C1; subst. rewrite <- H9.
      inversion C2; subst. rewrite <- H12.
      destruct o as [ | W]; destruct o1 as [ | W1]; destruct o2 as [ | W2];
        inversion Mo; subst;
        remember (σ 0) as p0 eqn:H_p0.
      - admit.
      - admit.
      - admit.
Admitted.



Lemma subst_ctx_O_merge : forall σ Γ1 Γ2, subst_ctx_O σ (Γ1 ⋓ Γ2) = subst_ctx_O σ Γ1 ⋓ subst_ctx_O σ Γ2.
Admitted.

Lemma consistent_split : forall σ Γ Γ',
      Consistent_Ctx σ Γ Γ' ->
      forall (Γ1 Γ2 : Ctx), Valid Γ = Γ1 ⋓ Γ2 ->
      {Γ1' : Ctx & Consistent_Ctx σ Γ1 Γ1'} * {Γ2' : Ctx & Consistent_Ctx σ Γ2 Γ2'}.
Proof.
  induction 1; intros Γ1 Γ2 M.
  - symmetry in M. apply merge_nil_inversion in M as [e1 e2].
    inversion e1; inversion e2.
    split; eexists; constructor.
  - destruct Γ1 as [|o1 Γ1'], Γ2 as [|o2 Γ2']; try solve [inversion M].
    * rewrite merge_nil_l in M.
      inversion M; subst.
      split; eexists; econstructor; eauto.
    * rewrite merge_nil_r in M.
      inversion M; subst.
      split; eexists; econstructor; eauto.
    * symmetry in M; apply ctx_cons_inversion in M as [M Mo]; symmetry in M.
      destruct o1, o2; inversion Mo; subst.
      destruct (IHConsistent_Ctx _ _ M) as [[Γ01 IH1] [Γ02 IH2]].
      split; eexists; econstructor; eauto. 
  - destruct Γ1 as [|o1 Γ1], Γ2 as [|o2 Γ2]; try solve [inversion M].
    * rewrite merge_nil_l in M.
      inversion M; subst.
      split; eexists; econstructor; eauto.
    * split; [ | exists []; constructor].
      rewrite merge_nil_r in M.
      inversion M; subst.
      eexists. eapply Consistent_σ_None; eauto.
    * symmetry in M; apply ctx_cons_inversion in M as [M Mo]; symmetry in M.
      destruct (IHConsistent_Ctx _ _ M) as [[Γ01 IH1] [Γ02 IH2]].
      destruct o1, o2; inversion Mo; subst. 
      + split; [ | eexists; apply Consistent_Γ_None]; eauto.
        assert (merge_valid : {Γ01' : Ctx & Valid [Some W] ⋓ Γ01 = Γ01'}). 
        {
          apply consistent_valid in H.
          apply consistent_valid in IH1. apply consistent_valid in IH2.
          assert (H' : subst_ctx_O (shift σ) Γ = Γ'); auto.
          rewrite M in H'.
          rewrite subst_ctx_O_merge in H'.
          simpl in H'.
          rewrite <- H' in e0.
          rewrite merge_assoc in e0.
          rewrite <- IH1.
          remember (Valid [Some W] ⋓ subst_ctx (shift σ) Γ1) as Γ01''.
          destruct Γ01'' as [ | Γ01'']; try (inversion e0; fail).
          exists Γ01''; auto.
        }
          
        destruct merge_valid as [Γ01' merge_valid]; exists Γ01'.
        eapply Consistent_σ_None; eauto.
      + split; eexists; [apply Consistent_Γ_None | eapply Consistent_σ_None]; eauto.
        admit. (* see assertion above *)
  - destruct Γ1 as [|o1 Γ1], Γ2 as [|o2 Γ2]; try solve [inversion M].
    * rewrite merge_nil_l in M.
      inversion M; subst.
      split; eexists; [ econstructor | eapply Consistent_Some]; eauto.
    * rewrite merge_nil_r in M.
      inversion M; subst.
      split; eexists; [ eapply Consistent_Some | econstructor]; eauto.
    * symmetry in M; apply ctx_cons_inversion in M as [M Mo]; symmetry in M.
      destruct (IHConsistent_Ctx _ _ M) as [[Γ01 IH1] [Γ02 IH2]].
      destruct o1, o2; inversion Mo; subst. 
      + split; eexists; [eapply Consistent_Some | apply Consistent_Γ_None]; eauto.
        admit.
      + split; eexists; [apply Consistent_Γ_None | eapply Consistent_Some]; eauto.
        admit.
Qed.

Lemma consistent_merge : forall Γ1 Γ2 Γ σ,
      Consistent_Ctx σ Γ1 -> Consistent_Ctx σ Γ2 ->
      Γ1 ⋓ Γ2 = Valid Γ ->  Consistent_Ctx σ Γ.
Proof.
  induction Γ1 as [ | [W1 | ]].
  + intros Γ2 Γ σ H H0 H1.
    rewrite merge_nil_l in H1; subst. 
    apply ctx_octx in H1.
    subst; assumption.
  + intros Γ2 Γ σ H H0 H1.
    destruct Γ2.
    - rewrite merge_nil_r in H1; subst. 
      apply ctx_octx in H1.
      subst; assumption.
    - inversion H1.
      destruct o; inversion H3.
      destruct (merge' Γ1 Γ2) as [|Γ']. inversion H3.
      rewrite <- H4 in H1.
      apply ctx_octx in H3.
      rewrite <- H3.
      inversion H; subst.
      inversion H0; subst.
      econstructor; eauto.
      eapply IHΓ1; eauto.
      apply ctx_cons_inversion in H1 as [M Mo]; auto.
  + intros Γ2 Γ σ H H0 H1.
    destruct Γ2.
    - rewrite merge_nil_r in H1; subst. 
      apply ctx_octx in H1.
      subst; assumption.
    - inversion H1.
      destruct o; inversion H3.
      * destruct (merge' Γ1 Γ2) as [|Γ']. inversion H3.
        rewrite <- H4 in H1.
        apply ctx_octx in H3.
        rewrite <- H3.
        inversion H; subst.
        inversion H0; subst.
        econstructor; eauto.
        eapply IHΓ1; eauto.
        apply ctx_cons_inversion in H1 as [M Mo]; auto.
      * destruct (merge' Γ1 Γ2) as [|Γ']. inversion H3.
        rewrite <- H4 in H1.
        apply ctx_octx in H3.
        rewrite <- H3.
        inversion H; subst.
        inversion H0; subst.
        econstructor; eauto.
        eapply IHΓ1; eauto.
        apply ctx_cons_inversion in H1 as [M Mo]; auto.
Qed.

(*
Definition subst_ctx' σ Γ := 
  match Γ with
  | Valid Γ' => subst_ctx σ Γ'
  | Invalid => Invalid
  end.

Hint Unfold subst_ctx': auto.
*)



(* I cannot believe this existed. cf. get_ctx_shift above... 
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
*)

Lemma singleton_get_ctx : forall x W Γ,
      SingletonCtx x W Γ ->
      forall σ p, Consistent_Ctx σ Γ ->
                σ x = Some p -> 
                subst_ctx σ Γ = get_ctx p W.
Proof.
  induction 1; intros σ p consistent σ_eq; simpl; try rewrite σ_eq.
  - inversion consistent; subst. monoid.
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
Proof. induction 1; simpl; auto. Qed.

Lemma consistent_singleton : forall x W Γ σ,
      SingletonCtx x W Γ ->
      Consistent_Ctx σ Γ ->
      WF_Pat (subst_ctx σ Γ) (subst_pat' σ (var x)) W.
Proof.
  intros x W Γ σ singleton consistent.
  destruct (σ x) as [p0' | ] eqn:Eq; simpl; rewrite Eq.
  - erewrite singleton_get_ctx; eauto.
    eapply consistent_ctx_correct; eauto.
    apply singleton_lookup; auto.
  - edestruct singleton_consistent_lookup as [p pf]; eauto.
    rewrite pf in *. inversion Eq.
Qed.

(*
Lemma consistent_valid : forall σ Ω, Consistent_Ctx σ Ω ->
                                exists Γ', subst_ctx σ Ω = Valid Γ'.
Proof.
  intros σ Ω H.
  induction H; eauto.
  - exists []. reflexivity.
  - destruct IHConsistent_Ctx.
    simpl.
    rewrite e.

    Search subst_ctx.
    erewrite singleton_get_ctx; eauto.
    eauto.
*)

Lemma wf_subst_pat : forall Ω p0 W, WF_Pat (Valid Ω) p0 W
                  -> forall σ,
                     Consistent_Ctx σ Ω ->
                     WF_Pat (subst_ctx σ Ω) (subst_pat' σ p0) W.
Proof.
  intros Ω p W WF.
  remember (Valid Ω) as Ω' eqn:Eq.
  revert Eq. 
  revert Ω.
  induction WF; intros Ω Eq σ H. 
  - apply ctx_octx in Eq; subst.
    apply consistent_singleton; subst; auto.
  - apply ctx_octx in Eq; subst.
    simpl. constructor.
  - apply ctx_octx in Eq; subst.
    simpl.
    destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try solve [inversion e].
    destruct consistent_split with (σ:=σ) (Γ1:=Γ1) (Γ2:=Γ2) (Γ:=Ω)
        as [consistent1 consistent2]; auto.
    


    inversion H; subst.
    * symmetry in e.
      apply merge_nil_inversion' in e as [Eq1 Eq2]; subst.
      econstructor; eauto; simpl; auto.
    * simpl.

econstructor; eauto.


    destruct (subst_ctx σ Ω) eqn:Eq.
    * inversion Eq.

    destruct Ω.
    * simpl. econstructor; auto.      
      symmetry in e.
      apply merge_nil_inversion' in e.
      intuition; subst; auto.
    * simpl. 

    Search subst_ctx.

    erewrite subst_ctx_split; eauto.

    destruct (subst_ctx σ Ω).
        
    erewrite singleton_get_ctx; eauto.
    econstructor.


    eapply wf_pair with (Γ := subst_ctx σ Ω).

    econstructor; eauto.
    unfold subst_ctx'.
    apply subst_OCtx_split; auto.
Qed.


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

