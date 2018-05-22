Require Export HOASCircuits.
Require Import Monoid.

(***********)
(** OCtxs **)
(***********)

Module OCtx.

Inductive OCtx := 
| Invalid : OCtx 
| Valid : Ctx -> OCtx.

Definition size_octx (Γ : OCtx) : nat :=
  match Γ with
  | Invalid => 0
  | Valid Γ' => size_ctx Γ'
  end.

Lemma ctx_octx : forall Γ Γ', Valid Γ = Valid Γ' <-> Γ = Γ'.
Proof. intuition; congruence. Defined.

Definition merge_wire (o1 o2 : option VType) : OCtx :=
  match o1, o2 with
  | None, o2 => Valid [o2]
  | Some v, None => Valid [Some v]
  | _, _ => Invalid
  end.

Fixpoint merge' (Γ1 Γ2 : Ctx) : OCtx :=
  match Γ1, Γ2 with
  | [], _ => Valid Γ2
  | _, [] => Valid Γ1
  | o1 :: Γ1', o2 :: Γ2' => match merge_wire o1 o2 with
                           | Invalid => Invalid
                           | Valid Γ0 => match merge' Γ1' Γ2' with
                                        | Invalid => Invalid
                                        | Valid Γ' => Valid (Γ0 ++ Γ')
                                        end
                           end
  end.                            

Definition merge (Γ1 Γ2 : OCtx) : OCtx :=
  match Γ1, Γ2 with
  | Valid Γ1', Valid Γ2' => merge' Γ1' Γ2'
  | _, _ => Invalid
  end. 

(* Merge will generally be opaque outside of this file *)
Lemma merge_shadow : merge = fun Γ1 Γ2 => 
  match Γ1 with
  | Invalid => Invalid
  | Valid Γ1' => match Γ2 with
                | Invalid => Invalid
                | Valid Γ2' => merge' Γ1' Γ2'
                end
  end. Proof. reflexivity. Qed.
Ltac unlock_merge := rewrite merge_shadow in *.

Notation "∅" := (Valid []).
Infix "⋓" := merge (left associativity, at level 50).

Coercion Valid : Ctx >-> OCtx.

(*******************)
(** Facts about ⋓ **)
(*******************)

Lemma merge_merge' : forall (Γ1 Γ2 : Ctx), Γ1 ⋓ Γ2 = (merge' Γ1 Γ2).
Proof. reflexivity. Defined.

(* Note that the reverse is not always true - we would need to 
   check validity and not-emptyness of the contexts *)
Lemma merge_cancel_l : forall Γ Γ1 Γ2 , Γ1 = Γ2 -> Γ ⋓ Γ1 = Γ ⋓ Γ2.
Proof. intros; subst; reflexivity. Defined.

Lemma merge_cancel_r : forall Γ Γ1 Γ2 , Γ1 = Γ2 -> Γ1 ⋓ Γ = Γ2 ⋓ Γ.
Proof. intros; subst; reflexivity. Defined.

Lemma merge_I_l : forall Γ, Invalid ⋓ Γ = Invalid. Proof. reflexivity. Defined.

Lemma merge_I_r : forall Γ, Γ ⋓ Invalid = Invalid. Proof. destruct Γ; reflexivity.
Defined.

Lemma merge_valid : forall (Γ1 Γ2 : OCtx) (Γ : Ctx), 
  Γ1 ⋓ Γ2 = Valid Γ ->
  {Γ1' : Ctx & Γ1 = Valid Γ1'} * {Γ2' : Ctx & Γ2 = Valid Γ2'}. 
Proof.
  intros Γ1 Γ2 Γ M.
  destruct Γ1 as [|Γ1'], Γ2 as [|Γ2']; inversion M.
  eauto.
Defined.

Lemma merge_invalid_iff : forall (o1 o2 : option VType) (Γ1 Γ2 : Ctx), 
  Valid (o1 :: Γ1) ⋓ Valid (o2 :: Γ2) = Invalid <-> 
  merge_wire o1 o2 = Invalid \/ Γ1 ⋓ Γ2 = Invalid.
Proof.
  intros o1 o2 Γ1 Γ2.
  split.  
  + intros H.
    destruct o1, o2; auto; right; simpl in H.    
    - rewrite <- merge_merge' in H.
      destruct (Γ1 ⋓ Γ2); trivial.
      inversion H.
    - rewrite <- merge_merge' in H.
      destruct (Γ1 ⋓ Γ2); trivial.
      inversion H.
    - rewrite <- merge_merge' in H.
      destruct (Γ1 ⋓ Γ2); trivial.
      inversion H.
  + intros H.
    inversion H.
    simpl. rewrite H0; reflexivity.
    simpl.
    destruct (merge_wire o1 o2); trivial.
    rewrite merge_merge' in H0.
    rewrite H0.
    reflexivity.
Defined.

Lemma merge_nil_l : forall Γ, ∅ ⋓ Γ = Γ. Proof. destruct Γ; reflexivity. Defined.

Lemma merge_nil_r : forall Γ, Γ ⋓ ∅ = Γ. 
Proof. destruct Γ; trivial. destruct c; trivial. Defined. 

Lemma merge_comm : forall Γ1 Γ2, Γ1 ⋓ Γ2 = Γ2 ⋓ Γ1. 
Proof.
  intros Γ1 Γ2.
  destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; trivial.
  generalize dependent Γ2.
  induction Γ1. 
  + destruct Γ2; trivial.
  + destruct Γ2; trivial.
    simpl.
    unfold merge in IHΓ1. 
    rewrite IHΓ1.
    destruct a, o; reflexivity.
Defined.    

Lemma merge_assoc : forall Γ1 Γ2 Γ3, Γ1 ⋓ (Γ2 ⋓ Γ3) = Γ1 ⋓ Γ2 ⋓ Γ3. 
Proof.
  intros Γ1 Γ2 Γ3.
  destruct Γ1 as [|Γ1], Γ2 as [|Γ2], Γ3 as [|Γ3]; repeat (rewrite merge_I_r); trivial.
  generalize dependent Γ3. generalize dependent Γ1.
  induction Γ2 as [| o2 Γ2']. 
  + intros. rewrite merge_nil_l, merge_nil_r; reflexivity.
  + intros Γ1 Γ3.
    destruct Γ1 as [|o1 Γ1'], Γ3 as [| o3 Γ3'] ; trivial.
    - rewrite 2 merge_nil_l.
      reflexivity.
    - rewrite 2 merge_nil_r.
      reflexivity.
    - destruct o1, o2, o3; trivial.
      * simpl. destruct (merge' Γ2' Γ3'); reflexivity.
      * simpl. destruct (merge' Γ1' Γ2'), (merge' Γ2' Γ3'); reflexivity.
      * simpl. destruct (merge' Γ1' Γ2') eqn:M12, (merge' Γ2' Γ3') eqn:M23.
        reflexivity.
        rewrite <- merge_merge' in *.
        rewrite <- M23.
        rewrite IHΓ2'.
        rewrite M12. 
        reflexivity.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        reflexivity.
        destruct (merge' Γ1' c0) eqn:M123.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        assumption.
        simpl.
        rewrite <- merge_merge' in *.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23, M123.
        reflexivity.
      * simpl. destruct (merge' Γ1' Γ2'), (merge' Γ2' Γ3'); reflexivity.
      * simpl. destruct (merge' Γ1' Γ2') eqn:M12, (merge' Γ2' Γ3') eqn:M23.
        reflexivity.
        rewrite <- merge_merge' in *.
        rewrite <- M23.
        rewrite IHΓ2'.
        rewrite M12. 
        reflexivity.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        reflexivity.
        destruct (merge' Γ1' c0) eqn:M123.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        assumption.
        simpl.
        rewrite <- merge_merge' in *.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23, M123.
        reflexivity.
      * simpl. destruct (merge' Γ1' Γ2') eqn:M12, (merge' Γ2' Γ3') eqn:M23.
        reflexivity.
        rewrite <- merge_merge' in *.
        rewrite <- M23.
        rewrite IHΓ2'.
        rewrite M12. 
        reflexivity.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        reflexivity.
        destruct (merge' Γ1' c0) eqn:M123.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        assumption.
        simpl.
        rewrite <- merge_merge' in *.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23, M123.
        reflexivity.
      * simpl. destruct (merge' Γ1' Γ2') eqn:M12, (merge' Γ2' Γ3') eqn:M23.
        reflexivity.
        rewrite <- merge_merge' in *.
        rewrite <- M23.
        rewrite IHΓ2'.
        rewrite M12. 
        reflexivity.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        reflexivity.
        destruct (merge' Γ1' c0) eqn:M123.
        rewrite <- merge_merge' in *.
        symmetry. apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23.
        assumption.
        simpl.
        rewrite <- merge_merge' in *.
        rewrite <- M12.
        rewrite <- IHΓ2'.
        rewrite M23, M123.
        reflexivity.
Defined.

Definition cons_o (o : option VType) (Γ : OCtx) : OCtx :=
  match Γ with
  | Invalid => Invalid
  | Valid Γ' => Valid (o :: Γ')
  end.

Lemma cons_distr_merge : forall Γ1 Γ2,
  cons_o None (Γ1 ⋓ Γ2) = cons_o None Γ1 ⋓ cons_o None Γ2.
Proof. destruct Γ1; destruct Γ2; simpl; auto. Defined.

Lemma merge_nil_inversion' : forall (Γ1 Γ2 : Ctx), Γ1 ⋓ Γ2 = ∅ -> (Γ1 = []) * (Γ2 = []).
Proof.
  induction Γ1 as [ | o Γ1]; intros Γ2; try inversion 1; auto.
  destruct Γ2 as [ | o' Γ2]; try solve [inversion H1].
  destruct o, o', (merge' Γ1 Γ2); inversion H1. 
Defined.

Lemma merge_nil_inversion : forall (Γ1 Γ2 : OCtx), Γ1 ⋓ Γ2 = ∅ -> (Γ1 = ∅) * (Γ2 = ∅).
Proof.
  intros Γ1 Γ2 eq.
  destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try solve [inversion eq].
  apply merge_nil_inversion' in eq.
  intuition; congruence.
Defined.

Lemma ctx_cons_inversion : forall (Γ Γ1 Γ2 : Ctx) o o1 o2,
      Valid (o1 :: Γ1) ⋓ Valid (o2 :: Γ2) = Valid (o :: Γ) ->
      (Γ1 ⋓ Γ2 = Valid Γ) * (merge_wire o1 o2 = Valid [o]).
Proof.
  intros Γ Γ1 Γ2 o o1 o2 H.
  inversion H.
  destruct (merge_wire o1 o2) eqn:Eq1. inversion H1.
  rewrite <- merge_merge' in H1.
  destruct (Γ1 ⋓ Γ2) eqn:Eq2. inversion H1.
  destruct o1, o2; simpl in Eq1. inversion Eq1.
  - apply ctx_octx in Eq1. rewrite <- Eq1 in *.
    simpl in H1.
    inversion H1; subst; auto.
  - apply ctx_octx in Eq1. rewrite <- Eq1 in *.
    simpl in H1.
    inversion H1; subst; auto.
  - apply ctx_octx in Eq1. rewrite <- Eq1 in *.
    simpl in H1.
    inversion H1; subst; auto.
Defined.

(**************)
(** Validity **)
(**************)

Definition is_valid (Γ : OCtx) : Prop := exists Γ', Γ = Valid Γ'.

Lemma valid_valid : forall Γ, is_valid (Valid Γ). Proof. intros. exists Γ. reflexivity. Defined.

Lemma valid_empty : is_valid ∅. Proof. unfold is_valid; eauto. Defined.

Lemma not_valid : not (is_valid Invalid). Proof. intros [Γ F]; inversion F. Defined.

Lemma valid_split_basic : forall Γ1 Γ2, is_valid (Γ1 ⋓ Γ2) -> is_valid Γ1 /\ is_valid Γ2.
Proof.
  intros Γ1 Γ2 V.
  unfold is_valid in *.
  destruct V as [Γ' V].
  apply merge_valid in V. destruct V as [[Γ1' E1] [Γ2' E2]]. 
  eauto.
Defined.

Lemma valid_cons : forall (o1 o2 : option VType) (Γ1 Γ2 : Ctx), 
  is_valid (Valid (o1 :: Γ1) ⋓ Valid (o2 :: Γ2)) <-> 
  (is_valid (merge_wire o1 o2) /\ is_valid (Γ1 ⋓ Γ2)).
Proof.
  intros o1 o2 Γ1 Γ2. split.
  - intros [Γ V].
    inversion V.
    destruct (merge_wire o1 o2). inversion H0.
    simpl. destruct (merge' Γ1 Γ2). inversion H0.
    unfold is_valid; split; eauto.
  - intros [[W Vo] [Γ V]].
    simpl in *.
    rewrite Vo, V.
    unfold is_valid; eauto.
Defined.


Lemma valid_join : forall Γ1 Γ2 Γ3, is_valid (Γ1 ⋓ Γ2) -> is_valid (Γ1 ⋓ Γ3) -> is_valid (Γ2 ⋓ Γ3) -> 
                               is_valid (Γ1 ⋓ Γ2 ⋓ Γ3).
Proof.
  destruct Γ1 as [|Γ1]. intros Γ2 Γ3 [Γ12 V12]; inversion V12.
  induction Γ1 as [|o1 Γ1].
  + intros Γ2 Γ3 V12 V13 V23. rewrite merge_nil_l. assumption. 
  + intros Γ2 Γ3 V12 V13 V23. 
    destruct Γ2 as [|Γ2], Γ3 as [|Γ3]; try solve [inversion V23; inversion H].
    destruct Γ2 as [|o2 Γ2], Γ3 as [|o3 Γ3]; try (rewrite merge_nil_r in *; auto).
    destruct o1, o2, o3; try solve [inversion V12; inversion H];
                         try solve [inversion V13; inversion H];    
                         try solve [inversion V23; inversion H].
    - apply valid_cons in V12 as [_ [Γ12 V12]].
      apply valid_cons in V13 as [_ [Γ13 V13]].
      apply valid_cons in V23 as [_ [Γ23 V23]].
      destruct (IHΓ1 (Valid Γ2) (Valid Γ3)) as [Γ V123]; unfold is_valid; eauto.
      exists (Some v :: Γ). 
      simpl in *. rewrite V12.
      simpl in *. rewrite V12 in V123. simpl in V123. rewrite V123.
      reflexivity.
    - apply valid_cons in V12 as [_ [Γ12 V12]].
      apply valid_cons in V13 as [_ [Γ13 V13]].
      apply valid_cons in V23 as [_ [Γ23 V23]].
      destruct (IHΓ1 (Valid Γ2) (Valid Γ3)) as [Γ V123]; unfold is_valid; eauto.
      exists (Some v :: Γ). 
      simpl in *. rewrite V12.
      simpl in *. rewrite V12 in V123. simpl in V123. rewrite V123.
      reflexivity.
    - apply valid_cons in V12 as [_ [Γ12 V12]].
      apply valid_cons in V13 as [_ [Γ13 V13]].
      apply valid_cons in V23 as [_ [Γ23 V23]].
      destruct (IHΓ1 (Valid Γ2) (Valid Γ3)) as [Γ V123]; unfold is_valid; eauto.
      exists (Some v :: Γ). 
      simpl in *. rewrite V12.
      simpl in *. rewrite V12 in V123. simpl in V123. rewrite V123.
      reflexivity.
    - apply valid_cons in V12 as [_ [Γ12 V12]].
      apply valid_cons in V13 as [_ [Γ13 V13]].
      apply valid_cons in V23 as [_ [Γ23 V23]].
      destruct (IHΓ1 (Valid Γ2) (Valid Γ3)) as [Γ V123]; unfold is_valid; eauto.
      exists (None :: Γ). 
      simpl in *. rewrite V12.
      simpl in *. rewrite V12 in V123. simpl in V123. rewrite V123.
      reflexivity.
Defined.

Lemma valid_split : forall Γ1 Γ2 Γ3, is_valid (Γ1 ⋓ Γ2 ⋓ Γ3) -> 
                                is_valid (Γ1 ⋓ Γ2) /\ is_valid (Γ1 ⋓ Γ3) /\ is_valid (Γ2 ⋓ Γ3).
Proof.
  intros Γ1 Γ2 Γ3 [Γ V].
  unfold is_valid.  
  intuition.
  + destruct (Γ1 ⋓ Γ2); [inversion V | eauto]. 
  + rewrite (merge_comm Γ1 Γ2), <- merge_assoc in V.
    destruct (Γ1 ⋓ Γ3); [rewrite merge_I_r in V; inversion V | eauto]. 
  + rewrite <- merge_assoc in V.
    destruct (Γ2 ⋓ Γ3); [rewrite merge_I_r in V; inversion V | eauto]. 
Defined. 

Ltac valid_invalid_absurd := try (absurd (is_valid Invalid); 
                                  [apply not_valid | auto]; fail).


Lemma size_octx_merge : forall (Γ1 Γ2 : OCtx), is_valid (Γ1 ⋓ Γ2) ->
                       size_octx (Γ1 ⋓ Γ2) = (size_octx Γ1 + size_octx Γ2)%nat.
Proof.
  intros Γ1 Γ2 valid.
  destruct Γ1 as [ | Γ1];
  destruct Γ2 as [ | Γ2];
    valid_invalid_absurd.
  revert Γ2 valid.
  induction Γ1 as [ | [W1 | ] Γ1]; intros Γ2 valid; 
    [rewrite merge_nil_l; auto | | ];
  (destruct Γ2 as [ | [W2 | ] Γ2]; [rewrite merge_nil_r; auto | |]);
  [ absurd (is_valid Invalid); auto; apply not_valid | | |].
  - specialize IHΓ1 with Γ2.
    simpl in *.
    destruct (merge' Γ1 Γ2) as [ | Γ] eqn:H; 
      [absurd (is_valid Invalid); auto; apply not_valid | ].
    simpl in *. rewrite IHΓ1; auto. apply valid_valid.
  - specialize IHΓ1 with Γ2.
    simpl in *.
    destruct (merge' Γ1 Γ2) as [ | Γ] eqn:H; 
      [absurd (is_valid Invalid); auto; apply not_valid | ].
    simpl in *. rewrite IHΓ1; auto. apply valid_valid.
  - specialize IHΓ1 with Γ2.
    simpl in *.
    destruct (merge' Γ1 Γ2) as [ | Γ] eqn:H; 
      [absurd (is_valid Invalid); auto; apply not_valid | ].
    simpl in *. rewrite IHΓ1; auto. apply valid_valid.
Defined.


(**********************************)
(* Equivalence of Merge and merge *)
(**********************************)

Lemma merge_wire_ind_fun : forall o1 o2 o,
    Merge_Wire o1 o2 o -> merge_wire o1 o2 = Valid [o].
Proof. induction 1; auto. Qed.

Lemma merge_ind_fun : forall Γ Γ1 Γ2,
    Γ == Γ1 ∙ Γ2 ->
    Valid Γ = Valid Γ1 ⋓ Valid Γ2.
Proof.
  intros.
  induction H; subst.
  - rewrite merge_nil_l. easy.
  - rewrite merge_nil_r. easy.
  - inversion m; subst.
    + simpl in *. rewrite <- IHMerge. easy.
    + simpl in *. rewrite <- IHMerge. easy.
    + simpl in *. rewrite <- IHMerge. easy.
Qed.

 
Lemma merge_wire_fun_ind : forall o1 o2 o,
    merge_wire o1 o2 = Valid [o] -> Merge_Wire o1 o2 o.
Proof.
  intros [w1 | ] [w2 | ] [w | ]; simpl; inversion 1; constructor.
Qed.

Lemma merge_fun_ind : forall Γ1 Γ2 Γ,
    Valid Γ = Valid Γ1 ⋓ Valid Γ2 ->
    Γ == Γ1 ∙ Γ2.
Proof.
  intros Γ1 Γ2 Γ.
  gen Γ1 Γ2.
  induction Γ; intros.
  - symmetry in H.
    apply merge_nil_inversion in H as [E1 E2]. subst.
    inversion E1. inversion E2.
    constructor.
  - destruct Γ1, Γ2.
    + inversion H.
    + simpl in H. inversion H; subst. constructor.
    + rewrite merge_nil_r in H. inversion H; subst. constructor.
    + simpl in H.
      destruct o, o0. 
      * simpl in H; symmetry in H; inversion H.
      * simpl in H.
        destruct (merge' Γ1 Γ2) as [|Γ'] eqn:E. symmetry in H; inversion H.
        inversion H; subst. 
        repeat constructor.
        apply IHΓ; auto.
      * simpl in H.
        destruct (merge' Γ1 Γ2) as [|Γ'] eqn:E. symmetry in H; inversion H.
        inversion H; subst. 
        repeat constructor.
        apply IHΓ; auto.
      * simpl in H.
        destruct (merge' Γ1 Γ2) as [|Γ'] eqn:E. symmetry in H; inversion H.
        inversion H; subst. 
        repeat constructor.
        apply IHΓ; auto.
Qed.

(* ⋓, ∅, and Invalid form a partial commutative monoid *)
Instance PCM_OCtx : PCM OCtx :=
  { one := ∅
  ; zero := Invalid
  ; m := merge
  }.

Instance PCM_Laws_OCtx : PCM_Laws OCtx :=
  { M_unit  := merge_nil_r
  ; M_assoc := merge_assoc
  ; M_comm  := merge_comm
  ; M_absorb := merge_I_r
  }.

Instance Translate_OCtx : Translate OCtx OCtx := 
  { translate := fun x => x }.

Lemma test_monoid : Valid (singleton 4 BIT) ⋓ Valid (singleton 5 QUBIT) = 
                    Valid (singleton 5 QUBIT) ⋓ Valid (singleton 4 BIT).
Proof. 
  let A := type_of_goal in
  match goal with
  | [ |- m ?a1 ?ev = ?a2 ] => (* evar case *)
    is_evar ev;
    let e1 := reify A a1 in
    let e2 := reify A a2 in
    change ((⟨e1⟩ : A) ev = (⟨e2⟩ : A));
    repeat rewrite flatten_correct; auto;
    simpl_args
  | [ |- ?a1 = ?a2 ] => (* non-evar case *)
    let e1 := reify A a1 in
    let e2 := reify A a2 in
    change ((⟨e1⟩ : A) = (⟨e2⟩ : A));
    repeat rewrite flatten_correct; auto;
    simpl_args  
  end.


monoid.


(** Typechecking Tactic **)

(* Prevent compute from unfolding important fixpoints *)
Open Scope circ_scope.
Opaque wproj.
Global Opaque merge.
Global Opaque Ctx.
Global Opaque is_valid.

Fixpoint pair_circ' {W1 W2} (p : Pat W1) (c2 : Circuit W2) : Circuit (W1 ⊗ W2) :=
  match c2 with
  | output p2   => output (pair p p2)
  | gate g p1 f => gate g p1 (fun p2 => pair_circ' p (f p2))
  | lift p1 f   => lift p1 (fun x => pair_circ' p (f x))
  end.
Fixpoint pair_circ {W1 W2} (c1 : Circuit W1) (c2 : Circuit W2) : Circuit (W1 ⊗ W2) :=
  match c1 with
  | output p1   => pair_circ' p1 c2
  | gate g p1 f => gate g p1 (fun p2 => pair_circ (f p2) c2)
  | lift p f    => lift p (fun b => pair_circ (f b) c2)
  end.
Notation "( x , y , .. , z )" := (pair_circ .. (pair_circ x y) .. z) (at level 0) : circ_scope.



Delimit Scope circ_scope with qc.

(* Automation *)

Ltac goal_has_evars := 
  match goal with 
  [|- ?G ] => has_evars G
  end.

Ltac invert_patterns := 
  repeat match goal with
  | [ p : Pat One |- _ ] => dependent destruction p
  | [ p : Pat Qubit |- _] => dependent destruction p
  | [ p : Pat Bit |- _] => dependent destruction p
  | [ p : Pat (_ ⊗ _) |- _ ] => dependent destruction p
  | [ H : Types_Pat ?Γ () |- _ ]           => is_var Γ; inversion H; subst
  | [ H : Types_Pat ?Γ (qubit _) |- _ ]    => is_var Γ; inversion H; subst
  | [ H : Types_Pat ?Γ (bit _)   |- _ ]    => is_var Γ; inversion H; subst
  | [ H : Types_Pat ?Γ (pair _ _) |- _ ]   => is_var Γ; dependent destruction H
  end.

Create HintDb typed_db.

Ltac type_check_once := 
  intros;
  try match goal with 
  | [|- Typed_Box _ ]           => solve [eauto with typed_db] (* extensible *)
  | [|- @Typed_Box  ?W1 ?W2 ?c] => unfold Typed_Box in *; try unfold c
  end;
  intros;
  simpl in *;
  subst; 
  invert_patterns;
  repeat match goal with 
  (* Should break this down by case - in lift case, 
     need to choose bit or qubit as appropriate *)
  | [ b : bool |- _ ]              => destruct b 
  | [ H : _ == _ ∙ _ |- _ ]     => destruct H
  | [ |- @Types_Circuit _ _ _ ] => econstructor; type_check_once

  | [ |- @Types_Circuit _ _ (if ?b then _ else _) ]
                                => destruct b; type_check_once

  (* compose_typing : specify goal. *)                                  
  | [ |- @Types_Circuit _ _ _ ] =>  eapply compose_typing; type_check_once 

  | [ H : forall a b, Types_Pat _ _ -> Types_Circuit _ _ |- Types_Circuit _ _] 
                                => apply H; type_check_once

  | [ H : @Types_Pat _ _ ?p |- @Types_Pat _ _ ?p ] 
                                => exact H
  | [ H : @Types_Pat ?Γ1 _ ?p |- @Types_Pat ?Γ2 _ ?p ] 
                                   (* in case they don't line up exactly *)
                                => replace Γ2 with Γ1; [exact H | monoid]

  | [ |- Types_Pat _ _ ]        => econstructor; type_check_once
  | [ |- ?Γ == ?Γ1 ∙ ?Γ2 ]      => has_evars (Γ1 ⋓ Γ2 ⋓ Γ)
  | [ |- _ == _ ∙ _ ]           => solve_merge
  end; 
  (* Runs monoid iff a single evar appears in context *)
  match goal with 
  | [|- is_valid ?Γ] => tryif (has_evar Γ)   
                        then (idtac (*"can't validate"; print_goal*))
                        else (idtac (*"validate"; print_goal*); validate)
  | [|- ?G ]         => tryif (has_evars G)  
                        then (idtac (*"can't monoid"; print_goal*))
                        else (idtac (*"monoid"; print_goal*); monoid)
  end.

(* Useful for debugging *)
Ltac type_check_num := 
  let pre := numgoals in idtac "Goals before: " pre "";
  [> type_check_once..];
  let post := numgoals in idtac "Goals after: " post "";
  tryif (guard post < pre) then type_check_num else idtac "done".

(* Easiest solution *)

Ltac type_check := let n := numgoals in do n [> type_check_once..].
