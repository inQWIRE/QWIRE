Require Export Prelim.
Require Export Monoid.
Open Scope list_scope.

(*** Context Definitions ***)

(** Types **)
Inductive WType := Qubit | Bit | One | Tensor : WType -> WType -> WType.
Notation " W1 ⊗ W2 " := (Tensor W1 W2) (at level 40, left associativity)
                     : circ_scope.

Open Scope circ_scope.
Fixpoint size_wtype (W : WType) : nat := 
  match W with
  | One => 0
  | Qubit => 1
  | Bit => 1
  | W1 ⊗ W2 => size_wtype W1 + size_wtype W2
  end.

(* Coq interpretations of wire types *)
Fixpoint interpret (w:WType) : Set :=
  match w with
    | Qubit => bool
    | Bit   => bool 
    | One   => unit
    | w1 ⊗ w2 => (interpret w1) * (interpret w2)
  end.

(* Large tensor product. Right associative with a trailing One  *)
Fixpoint NTensor (n : nat) (W : WType) := 
  match n with 
  | 0    => One
  | S n' => W ⊗ NTensor n' W
  end.

Infix "⨂" := NTensor (at level 30) : circ_scope.

Lemma size_ntensor : forall n W, size_wtype (n ⨂ W) = (n * size_wtype W)%nat.
Proof.
  intros n W.
  induction n; trivial.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Close Scope circ_scope.


(** Variables **)
Definition Var := nat.
Definition Ctx := list (option WType).

Inductive OCtx := 
| Invalid : OCtx 
| Valid : Ctx -> OCtx.

Lemma ctx_octx : forall Γ Γ', Valid Γ = Valid Γ' <-> Γ = Γ'.
Proof. intuition; congruence. Defined.

(* The size of a context is the number of wires it holds *)
Fixpoint size_ctx (Γ : Ctx) : nat :=
  match Γ with
  | [] => 0
  | None :: Γ' => size_ctx Γ'
  | Some _ :: Γ' => S (size_ctx Γ')
  end.
Definition size_octx (Γ : OCtx) : nat :=
  match Γ with
  | Invalid => 0
  | Valid Γ' => size_ctx Γ'
  end.

Lemma size_ctx_size_octx : forall (Γ : Ctx), size_ctx Γ = size_octx (Valid Γ).
Proof. easy. Qed.

Lemma size_ctx_app : forall (Γ1 Γ2 : Ctx),
      size_ctx (Γ1 ++ Γ2) = (size_ctx Γ1 + size_ctx Γ2)%nat.
Proof.
  induction Γ1; intros; simpl; auto.
  destruct a; trivial.
  rewrite IHΓ1; easy.
Qed.


(**********************)
(* Singleton Contexts *)
(**********************)

Inductive SingletonCtx : Var -> WType -> Ctx -> Prop :=
| SingletonHere : forall w, SingletonCtx 0 w [Some w]
| SingletonLater : forall x w Γ, SingletonCtx x w Γ -> SingletonCtx (S x) w (None::Γ).

Inductive SingletonOCtx x w : OCtx -> Prop :=
| SingletonValid : forall Γ, SingletonCtx x w Γ -> SingletonOCtx x w (Valid Γ).

Lemma Singleton_size : forall x w Γ, SingletonCtx x w Γ -> size_ctx Γ = 1%nat.
Proof. induction 1; auto. Qed.

Fixpoint singleton (x : Var) (W : WType) : Ctx :=
  match x with
  | O => [Some W]
  | S x => None :: singleton x W
  end.

Lemma singleton_singleton : forall x W,
      SingletonCtx x W (singleton x W).
Proof.
  induction x; intros W.
  - constructor. 
  - simpl. constructor. apply IHx.
Defined.   

Lemma singleton_equiv : forall x W Γ,
      SingletonCtx x W Γ -> Γ = singleton x W.
Proof.
  induction 1; trivial.
  simpl. rewrite IHSingletonCtx. reflexivity.
Defined.

Lemma singleton_size : forall x w, size_ctx (singleton x w) = 1%nat.
Proof. induction x; auto. Qed.

(***********)
(* Merging *)
(***********)

Definition merge_wire (o1 o2 : option WType) : OCtx :=
  match o1, o2 with
  | None, o2 => Valid [o2]
  | Some w1, None => Valid [Some w1]
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

(*** Properties of ⋓ ***)


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

(*
Lemma merge_valid : forall (Γ1 Γ2 : OCtx) (Γ : Ctx), 
  Γ1 ⋓ Γ2 = Valid Γ ->
  (exists Γ1', Γ1 = Valid Γ1') /\ (exists Γ2', Γ2 = Valid Γ2'). 
Proof.
  intros Γ1 Γ2 Γ M.
  destruct Γ1 as [|Γ1'], Γ2 as [|Γ2']; inversion M.
  eauto.
Qed.
*)

Lemma merge_valid : forall (Γ1 Γ2 : OCtx) (Γ : Ctx), 
  Γ1 ⋓ Γ2 = Valid Γ ->
  {Γ1' : Ctx & Γ1 = Valid Γ1'} * {Γ2' : Ctx & Γ2 = Valid Γ2'}. 
Proof.
  intros Γ1 Γ2 Γ M.
  destruct Γ1 as [|Γ1'], Γ2 as [|Γ2']; inversion M.
  eauto.
Defined.

Lemma merge_invalid_iff : forall (o1 o2 : option WType) (Γ1 Γ2 : Ctx), 
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



Definition cons_o (o : option WType) (Γ : OCtx) : OCtx :=
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

Lemma merge_singleton_append : forall W (Γ : Ctx), 
        Γ ⋓ (singleton (length Γ) W) = Valid (Γ ++ [Some W]). 
Proof. 
  induction Γ.
  - simpl. reflexivity. 
  - simpl in *.
    destruct a; simpl; rewrite IHΓ; reflexivity.
Qed.

Lemma merge_offset : forall (n : nat) (Γ1 Γ2 Γ : Ctx), Valid Γ = Γ1 ⋓ Γ2 ->
  Valid (repeat None n ++ Γ1) ⋓ Valid (repeat None n ++ Γ2) = 
  Valid (repeat None n ++ Γ).
Proof.
  intros n Γ1 Γ2 Γ H.
  induction n.
  - simpl. auto.
  - simpl in *.
    rewrite IHn.
    reflexivity.
Qed.


(*** OContexts are a PCM ***)

(* Partial Commutative Monoids *)
Instance PCM_OCtx : PCM OCtx :=
  { one := ∅;
    zero := Invalid;
    m := merge
  }.

Instance PCM_Laws_OCtx : PCM_Laws OCtx :=
  { M_unit   := merge_nil_r
  ; M_assoc  := merge_assoc
  ; M_comm   := merge_comm
  ; M_absorb := merge_I_r
  }.

Hint Resolve PCM_OCtx.
Hint Resolve PCM_Laws_OCtx.

(*** Validity ***)

Definition is_valid (Γ : OCtx) : Prop := exists Γ', Γ = Valid Γ'.

Record valid_merge Γ1 Γ2 Γ :=
  { pf_valid : is_valid Γ
  ; pf_merge : Γ = Γ1 ⋓ Γ2 }.

Notation "Γ == Γ1 ∙ Γ2" := (valid_merge Γ1 Γ2 Γ) (at level 20).

Lemma valid_valid : forall Γ, is_valid (Valid Γ). Proof. intros. exists Γ. reflexivity. Defined.

Lemma valid_empty : is_valid ∅. Proof. unfold is_valid; eauto. Defined.

Lemma not_valid : not (is_valid Invalid). Proof. intros [Γ F]; inversion F. Defined.

Lemma valid_l : forall Γ1 Γ2, is_valid (Γ1 ⋓ Γ2) -> is_valid Γ1.
Proof.
  intros Γ1 Γ2 V.
  unfold is_valid in *.
  destruct V as [Γ' V].
  apply merge_valid in V as [[Γ1'] [Γ2']].
  eauto.
Defined.

Lemma valid_r : forall Γ1 Γ2, is_valid (Γ1 ⋓ Γ2) -> is_valid Γ2.
Proof.
  intros Γ1 Γ2 V.
  unfold is_valid in *.
  destruct V as [Γ' V].
  apply merge_valid in V as [[Γ1'] [Γ2']].
  eauto.
Defined.

Lemma valid_cons : forall (o1 o2 : option WType) (Γ1 Γ2 : Ctx), 
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
      exists (Some w :: Γ). 
      simpl in *. rewrite V12.
      simpl in *. rewrite V12 in V123. simpl in V123. rewrite V123.
      reflexivity.
    - apply valid_cons in V12 as [_ [Γ12 V12]].
      apply valid_cons in V13 as [_ [Γ13 V13]].
      apply valid_cons in V23 as [_ [Γ23 V23]].
      destruct (IHΓ1 (Valid Γ2) (Valid Γ3)) as [Γ V123]; unfold is_valid; eauto.
      exists (Some w :: Γ). 
      simpl in *. rewrite V12.
      simpl in *. rewrite V12 in V123. simpl in V123. rewrite V123.
      reflexivity.
    - apply valid_cons in V12 as [_ [Γ12 V12]].
      apply valid_cons in V13 as [_ [Γ13 V13]].
      apply valid_cons in V23 as [_ [Γ23 V23]].
      destruct (IHΓ1 (Valid Γ2) (Valid Γ3)) as [Γ V123]; unfold is_valid; eauto.
      exists (Some w :: Γ). 
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

Lemma size_octx_merge : forall (Γ1 Γ2 : OCtx), is_valid (Γ1 ⋓ Γ2) ->
                       size_octx (Γ1 ⋓ Γ2) = (size_octx Γ1 + size_octx Γ2)%nat.
Proof.
  intros Γ1 Γ2 V.
  destruct Γ1 as [ | Γ1], Γ2 as [ | Γ2]; try apply not_valid in V; try easy.
  revert Γ2 V.
  induction Γ1 as [ | [W1 | ] Γ1]; intros Γ2 V; 
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

(**************************)
(* Basic validity Tactics *)
(**************************)

Ltac simplify_invalid := repeat rewrite merge_I_l in *;
                         repeat rewrite merge_I_r in *.

Ltac invalid_contradiction :=
  (* don't want any of the proofs to be used in conclusion *)
  absurd False; [ inversion 1 | ]; 
  repeat match goal with
  | [ H : ?Γ == ?Γ1 ∙ ?Γ2 |- _ ] => destruct H
  end;
  subst; simplify_invalid;
  match goal with
  | [ H : is_valid Invalid  |- _ ] => apply (False_rect _ (not_valid H))
  | [ H : Valid _ = Invalid |- _ ] => inversion H
  end.      

(**********************************)
(* Inductive predicate for proofs *)
(**********************************)

Inductive merge_o {A : Set} : option A -> option A -> option A -> Set :=
| merge_None : merge_o None None None
| merge_Some_l : forall w, merge_o (Some w) None (Some w)
| merge_Some_r : forall w, merge_o None (Some w) (Some w).

    
Inductive merge_ind : OCtx -> OCtx -> OCtx -> Set :=
| m_nil_l : forall Γ, merge_ind ∅ (Valid Γ) (Valid Γ)
| m_nil_r : forall Γ, merge_ind (Valid Γ) ∅ (Valid Γ)
| m_cons  : forall o1 o2 o Γ1 Γ2 Γ,
    merge_o o1 o2 o ->
    merge_ind (Valid Γ1) (Valid Γ2) (Valid Γ) ->
    merge_ind (Valid (o1 :: Γ1)) (Valid (o2 :: Γ2)) (Valid (o :: Γ)).

Lemma merge_o_ind_fun : forall o1 o2 o,
    merge_o o1 o2 o -> merge_wire o1 o2 = Valid [o].
Proof. induction 1; auto. Qed.

Lemma merge_ind_fun : forall Γ1 Γ2 Γ,
    merge_ind Γ1 Γ2 Γ ->
    Γ == Γ1 ∙ Γ2.
Proof.
  induction 1.
  * split; [apply valid_valid | auto ].
  * split; [apply valid_valid | rewrite merge_nil_r; auto ].
  * destruct IHmerge_ind.
    split; [apply valid_valid | ].
    simpl. erewrite merge_o_ind_fun; [ | eauto].
    unfold merge in pf_merge0.
    rewrite <- pf_merge0.
    auto.
Qed.

Lemma merge_o_fun_ind : forall o1 o2 o,
    merge_wire o1 o2 = Valid [o] -> merge_o o1 o2 o.
Proof.
  intros [w1 | ] [w2 | ] [w | ]; simpl; inversion 1; constructor.
Qed.

Lemma merge_fun_ind : forall Γ1 Γ2 Γ,
    Γ == Γ1 ∙ Γ2 ->
    merge_ind Γ1 Γ2 Γ.
Proof.
  intros [ | Γ1] [ | Γ2] [ | Γ]; intros; try invalid_contradiction.
  generalize dependent Γ.
  generalize dependent Γ2.
  induction Γ1 as [ | o1 Γ1]; intros Γ2 Γ [pf_valid pf_merge].
  * simpl in pf_merge. rewrite pf_merge. constructor.
  * destruct Γ2 as [ | o2 Γ2].
    + rewrite merge_nil_r in pf_merge.
      rewrite pf_merge.
      constructor.
    + destruct o1 as [w1 | ], o2 as [w2 | ].
      - simpl in *. invalid_contradiction.
      - simpl in pf_merge.
        destruct (merge' Γ1 Γ2) as [ | Γ'] eqn:H_Γ'; [invalid_contradiction | ].
        rewrite pf_merge.
        constructor; [apply merge_o_fun_ind; auto | ].
        apply IHΓ1.
        split; [apply valid_valid | auto].
      - simpl in pf_merge.
        destruct (merge' Γ1 Γ2) as [ | Γ'] eqn:H_Γ'; [invalid_contradiction | ].
        rewrite pf_merge.
        constructor; [apply merge_o_fun_ind; auto | ].
        apply IHΓ1.
        split; [apply valid_valid | auto].
      - simpl in pf_merge.
        destruct (merge' Γ1 Γ2) as [ | Γ'] eqn:H_Γ'; [invalid_contradiction | ].
        rewrite pf_merge.
        constructor; [apply merge_o_fun_ind; auto | ].
        apply IHΓ1.
        split; [apply valid_valid | auto].
Qed.

Lemma merge_intersection : forall Γ1 Γ2 Γ3 Γ4,
  is_valid (Γ1 ⋓ Γ2) ->
  (Γ1 ⋓ Γ2) = (Γ3 ⋓ Γ4) ->
  { Γ13 : OCtx & { Γ14 : OCtx & { Γ23 : OCtx & { Γ24 : OCtx &
  Γ1 == Γ13 ∙ Γ14 /\ Γ2 == Γ23 ∙ Γ24 /\ Γ3 == Γ13 ∙ Γ23 /\ Γ4 == Γ14 ∙ Γ24}}}}.
Proof.
  intros Γ1 Γ2 Γ3 Γ4 V M.  
  assert (H : (Γ1 ⋓ Γ2) == Γ3 ∙ Γ4). constructor; assumption. 
  clear M V.
  apply merge_fun_ind in H.
  remember (Γ1 ⋓ Γ2) as Γ. 
  generalize dependent Γ2.
  generalize dependent Γ1.
  induction H. 
  - intros Γ1 Γ2.
    exists ∅, Γ1, ∅, Γ2. 
    repeat split; try apply valid_valid.
    destruct Γ1; [invalid_contradiction|apply valid_valid].
    rewrite merge_nil_l; reflexivity.
    destruct Γ2; [invalid_contradiction| apply valid_valid].
    rewrite merge_nil_l; reflexivity.
    assumption.
  - intros Γ1 Γ2.
    exists Γ1, ∅, Γ2, ∅. 
    repeat split; try apply valid_valid.
    destruct Γ1; [invalid_contradiction|apply valid_valid].
    rewrite merge_nil_r; reflexivity.
    destruct Γ2; [invalid_contradiction| apply valid_valid].
    rewrite merge_nil_r; reflexivity.
    assumption.
  - rename Γ1 into Γ3. rename Γ2 into Γ4. rename o1 into o3. rename o2 into o4.
    intros Γ1 Γ2 M.
    destruct Γ1 as [|Γ1]. invalid_contradiction.
    destruct Γ2 as [|Γ2]. invalid_contradiction.
    destruct Γ1 as [|o1 Γ1], Γ2 as [|o2 Γ2]. 
    + inversion M.
    + rewrite merge_nil_l in M. inversion M. subst.
      exists ∅, ∅, (Valid (o3 :: Γ3)), (Valid (o4 :: Γ4)).
      repeat split; try apply valid_valid.      
      apply merge_ind_fun.
      constructor; assumption.
    + rewrite merge_nil_r in M. inversion M. subst.
      exists (Valid (o3 :: Γ3)), (Valid (o4 :: Γ4)), ∅, ∅.
      repeat split; try apply valid_valid.      
      apply merge_ind_fun.
      constructor; assumption.
    + assert (M12 : (Valid (o :: Γ) == Valid (o1 :: Γ1) ∙ Valid (o2 :: Γ2))).
      constructor. apply valid_valid. assumption.
      clear M.
      apply merge_fun_ind in M12.
      inversion M12. subst. clear M12.
      destruct (IHmerge_ind (Valid Γ1) (Valid Γ2)) as [Γ13 [Γ14 [Γ23 [Γ24 pf]]]].
      apply merge_ind_fun in H7 as [V M]. assumption.
      destruct pf as [pf1 [pf2 [pf3 pf4]]].
      destruct Γ13 as [|Γ13]. invalid_contradiction.
      destruct Γ14 as [|Γ14]. invalid_contradiction.
      destruct Γ23 as [|Γ23]. invalid_contradiction.
      destruct Γ24 as [|Γ24]. invalid_contradiction.
      destruct pf1 as [_ M1], pf2 as [_ M2], pf3 as [_ M3], pf4 as [_ M4].
      simpl in *.
      inversion m; subst; inversion H3; subst.
      * exists (Valid (None :: Γ13)), (Valid (None :: Γ14)), 
          (Valid (None :: Γ23)), (Valid (None :: Γ24)).
        repeat split; try apply valid_valid; simpl.         
        rewrite <- M1; reflexivity.
        rewrite <- M2; reflexivity.
        rewrite <- M3; reflexivity.
        rewrite <- M4; reflexivity.
      * exists (Valid (Some w :: Γ13)), (Valid (None :: Γ14)), 
          (Valid (None :: Γ23)), (Valid (None :: Γ24)).
        repeat split; try apply valid_valid; simpl.         
        rewrite <- M1; reflexivity.
        rewrite <- M2; reflexivity.
        rewrite <- M3; reflexivity.
        rewrite <- M4; reflexivity.
      * exists (Valid (None :: Γ13)), (Valid (None :: Γ14)), 
          (Valid (Some w :: Γ23)), (Valid (None :: Γ24)).
        repeat split; try apply valid_valid; simpl.         
        rewrite <- M1; reflexivity.
        rewrite <- M2; reflexivity.
        rewrite <- M3; reflexivity.
        rewrite <- M4; reflexivity.
      * exists (Valid (None :: Γ13)), (Valid (Some w :: Γ14)), 
          (Valid (None :: Γ23)), (Valid (None :: Γ24)).
        repeat split; try apply valid_valid; simpl.         
        rewrite <- M1; reflexivity.
        rewrite <- M2; reflexivity.
        rewrite <- M3; reflexivity.
        rewrite <- M4; reflexivity.
      * exists (Valid (None :: Γ13)), (Valid (None :: Γ14)), 
          (Valid (None :: Γ23)), (Valid (Some w :: Γ24)).
        repeat split; try apply valid_valid; simpl.         
        rewrite <- M1; reflexivity.
        rewrite <- M2; reflexivity.
        rewrite <- M3; reflexivity.
        rewrite <- M4; reflexivity.
Qed.        



(*** Disjointness ***)

(* I don't think we use these. If not we should get rid of them *)

Definition Disjoint Γ1 Γ2 : Prop := 
  match Γ1, Γ2 with
  | Invalid, _ => True
  | _, Invalid => True
  | Valid _, Valid _ => is_valid (Γ1 ⋓ Γ2)
  end.
Lemma disjoint_nil_r : forall Γ, Disjoint Γ ∅.
Proof.
  destruct Γ as [ | Γ]; [exact I | ].
  unfold Disjoint. rewrite merge_nil_r. exists Γ. reflexivity.
Defined.


Lemma disjoint_valid : forall Γ1 Γ2, Disjoint Γ1 Γ2 -> is_valid Γ1 -> is_valid Γ2 -> is_valid (Γ1 ⋓ Γ2).
Proof.
  intros Γ1 Γ2 disj [Γ1' valid1] [Γ2' valid2].
  rewrite valid1 in *; rewrite valid2 in *; auto. 
Defined.

Lemma disjoint_merge : forall Γ Γ1 Γ2,
                       Disjoint Γ Γ1 -> Disjoint Γ Γ2 -> Disjoint Γ (Γ1 ⋓ Γ2).
Proof.
  intros Γ Γ1 Γ2 disj1 disj2.
  remember (Γ1 ⋓ Γ2) as Γ'.
  destruct Γ as [ | Γ]; [exact I | ].
  destruct Γ' as [ | Γ']; [exact I | ].
  assert (valid0 : is_valid Γ). { apply valid_valid. }
  assert (valid1 : is_valid Γ1). 
    { destruct Γ1 as [ | Γ1]; [inversion HeqΓ' | ]. apply valid_valid. }
  assert (valid2 : is_valid Γ2).
    { destruct Γ2 as [ | Γ2]; [rewrite merge_I_r in *; inversion HeqΓ' | ]. apply valid_valid. }
  assert (valid1' : is_valid (Γ ⋓ Γ1)). { apply disjoint_valid; auto. }
  assert (valid2' : is_valid (Γ ⋓ Γ2)). { apply disjoint_valid; auto. }
  unfold Disjoint.
  rewrite HeqΓ'.
  rewrite merge_assoc.
  apply valid_join; auto.
  exists Γ'; auto.
Defined.


Lemma disjoint_split : forall Γ1 Γ2 Γ, is_valid Γ1 -> is_valid Γ2 -> 
                                  Disjoint Γ1 Γ2 -> Disjoint (Γ1 ⋓ Γ2) Γ 
                                  -> Disjoint Γ1 Γ /\ Disjoint Γ2 Γ.
Proof.
  intros Γ1 Γ2 Γ [Γ1' valid1] [Γ2' valid2] disj disj'.
  subst. unfold Disjoint in disj.
  destruct Γ as [ | Γ]; [split; exact I | ].
  unfold Disjoint.
  destruct disj as [Γ' is_valid].
  rewrite is_valid in disj'.
  unfold Disjoint in disj'.
  rewrite <- is_valid in disj'.
  apply valid_split in disj'.
  destruct disj' as [H1 [H2 H3]]; split; auto.
Defined.


(**************************)
(* Extra helper functions *)
(**************************)

Definition xor_option {a} (o1 : option a) (o2 : option a) : option a :=
  match o1, o2 with
  | Some a1, None => Some a1
  | None, Some a2 => Some a2
  | _   , _       => None
  end.

(* index into an OCtx *)
Fixpoint index (Γ : OCtx) (i : nat) : option WType :=
  match Γ with
  | Invalid => None
  | Valid Γ' => maybe (Γ' !! i) None
  end.


Lemma index_invalid : forall i, index Invalid i = None.
Proof.
  auto.
Qed.
Lemma index_empty : forall i, index ∅ i = None.
Proof.
  intros.
  simpl. 
  rewrite nth_nil.
  auto.
Qed.

Lemma singleton_index : forall x w Γ,
      SingletonCtx x w Γ ->
      index Γ x = Some w.
Proof.
  induction 1; simpl; auto.
Qed.

(********************)
(* Empty Contexts *)
(********************)

Inductive empty_ctx : Ctx -> Prop :=
| empty_nil : empty_ctx []
| empty_cons : forall Γ, empty_ctx Γ -> empty_ctx (None :: Γ)
.

Lemma empty_ctx_size : forall Γ, empty_ctx Γ -> size_ctx Γ = 0%nat.
Proof. induction 1; auto. Qed.


Lemma eq_dec_empty_ctx : forall Γ, {empty_ctx Γ} + {~empty_ctx Γ}.
Proof.
  intros.
  induction Γ.
  - left; constructor.
  - destruct a.
    + right. easy.
    + destruct IHΓ.
      * left; constructor; easy.
      * right. intros F. apply n. inversion F. easy.
Qed.

Lemma merge_empty : forall (Γ Γ1 Γ2 : Ctx),
  Γ == Γ1 ∙ Γ2 ->
  empty_ctx Γ ->
  empty_ctx Γ1 /\ empty_ctx Γ2.
Proof.
  intros Γ Γ1 Γ2 M E.
  apply merge_fun_ind in M.
  dependent induction M.
  - split; trivial; constructor.
  - split; trivial; constructor.
  - inversion E; subst.
    inversion m; subst.
    specialize (IHM Γ0 Γ3 Γ4 eq_refl eq_refl eq_refl H0) as [EΓ3 EΓ4].
    split; constructor; easy.
Qed.



(********************)
(* Trimmed Contexts *)
(********************)

(* Removes Nones from end *)
Fixpoint trim (Γ : Ctx) : Ctx :=
  match Γ with
  | [] => []
  | None :: Γ' => match trim Γ' with
                  | [] => []
                  | Γ''  => None :: Γ''
                  end
  | Some w :: Γ' => Some w :: trim Γ'
  end.

Definition otrim (Γ : OCtx) :=
  match Γ with
  | Invalid => Invalid
  | Valid Γ => Valid (trim Γ)
  end.

Lemma trim_otrim : forall (Γ : Ctx), Valid (trim Γ) = otrim Γ.
Proof. easy. Qed. 

Lemma size_ctx_trim : forall Γ, size_ctx (trim Γ) = size_ctx Γ.
Proof.
  induction Γ; auto.
  destruct a; simpl.
  rewrite IHΓ; easy.
  simpl.
  destruct (trim Γ); easy.
Qed.  

Lemma size_octx_trim : forall Γ, size_octx (trim Γ) = size_octx Γ.
Proof. apply size_ctx_trim. Qed.


Lemma index_trim : forall Γ i,    
    index (trim Γ) i = index Γ i.
Proof.
  induction Γ as [ | [w | ] Γ]; intros i.
  * simpl. auto.
  * simpl. destruct i; simpl; auto.
    apply IHΓ.
  * simpl. remember (trim Γ) as Γ'.
    destruct Γ' as [ | o Γ']; auto.
    + rewrite nth_nil.
      destruct i; simpl; auto. 
      simpl in IHΓ. 
      rewrite <- IHΓ.
      rewrite nth_nil.
      auto.
    + destruct i; simpl; auto.
      apply IHΓ.
Qed.

Lemma trim_empty : forall Γ, empty_ctx Γ -> trim Γ = [].
Proof.
  induction 1; simpl; auto.
  rewrite IHempty_ctx; auto.
Qed.

Lemma trim_non_empty : forall Γ, ~ empty_ctx Γ -> trim Γ <> [].
Proof.
  intros Γ NE.
  induction Γ.
  - contradict NE. constructor.
  - destruct a. 
    + simpl. easy. 
    + simpl. 
      destruct (trim Γ).
      * apply IHΓ.
        intros F.
        apply NE.
        constructor; easy.
      * easy. 
Qed.

Lemma trim_cons_non_empty : forall o Γ, ~ empty_ctx Γ ->
                              trim (o :: Γ) = o :: trim Γ.
Proof.
  intros o Γ H.  
  destruct o; trivial.
  simpl.
  apply trim_non_empty in H.
  destruct (trim Γ); easy. 
Qed.


Lemma trim_valid : forall (Γ : OCtx), is_valid Γ <-> is_valid (otrim Γ).
Proof.
  destruct Γ as [|Γ].
  - simpl. easy.
  - simpl. split; intros; apply valid_valid.
Qed.

(* I'm sure there's a more succint way to prove this. Maybe use cons_o? *)
Lemma trim_merge_dist : forall Γ1 Γ2, otrim Γ1 ⋓ otrim Γ2 = otrim (Γ1 ⋓ Γ2).
Proof.
  destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try (simpl; easy).
  gen Γ2.
  induction Γ1 as [|o1 Γ1 IH].
  - intros Γ2. easy. 
  - intros Γ2.
    destruct Γ2 as [|o2 Γ2].
    rewrite 2 merge_nil_r. easy.
    specialize (IH Γ2).
    destruct (eq_dec_empty_ctx Γ1) as [E1 | NE1];
    destruct (eq_dec_empty_ctx Γ2) as [E2 | NE2].
    + repeat rewrite <- trim_otrim in *.
      apply trim_empty in E1.
      apply trim_empty in E2.
      rewrite E1, E2 in *.
      rewrite merge_nil_l in *.
      destruct o1, o2.
      * simpl. easy.
      * simpl. rewrite E1, E2. simpl in IH. 
        destruct (merge' Γ1 Γ2). inversion IH.
        simpl in *.
        inversion IH.
        easy.
      * simpl. rewrite E1, E2. simpl in IH. 
        destruct (merge' Γ1 Γ2). inversion IH.
        simpl in *.
        inversion IH.
        easy.
      * simpl. rewrite E1, E2. simpl in IH.
        destruct (merge' Γ1 Γ2). inversion IH.
        simpl in *.
        inversion IH.
        easy.
    + repeat rewrite <- trim_otrim in *.
      apply trim_empty in E1.
      rewrite E1 in *.
      rewrite merge_nil_l in *.
      eapply trim_cons_non_empty in NE2.
      rewrite NE2 in *.
      destruct o1, o2.
      * simpl. easy.
      * simpl in *. 
        rewrite E1; simpl.
        destruct (merge' Γ1 Γ2) eqn:M. inversion IH.
        simpl. inversion IH. easy.
      * simpl in *.
        rewrite E1. simpl.
        destruct (merge' Γ1 Γ2) eqn:M. inversion IH.
        simpl. inversion IH. easy.
      * simpl. simpl in IH.
        rewrite E1. simpl. 
        destruct (merge' Γ1 Γ2) eqn:M. inversion IH.
        simpl. inversion IH.
        simpl in *.
        destruct (trim Γ2). inversion NE2.
        easy.
    + repeat rewrite <- trim_otrim in *.
      apply trim_empty in E2.
      rewrite E2 in *.
      rewrite merge_nil_r in *.
      eapply trim_cons_non_empty in NE1.
      rewrite NE1 in *.
      destruct o1, o2.
      * simpl. easy.
      * simpl in *. 
        rewrite E2; simpl.
        destruct (merge' Γ1 Γ2) eqn:M. inversion IH.
        simpl. inversion IH. easy.
      * simpl in *.
        rewrite E2. simpl.
        destruct (merge' Γ1 Γ2) eqn:M. inversion IH.
        rewrite <- merge_merge'. rewrite merge_nil_r. 
        simpl. inversion IH. easy.
      * simpl. simpl in IH.
        rewrite E2. simpl. 
        destruct (merge' Γ1 Γ2) eqn:M. inversion IH.
        simpl. inversion IH.
        simpl in *.
        destruct (trim Γ1). inversion NE1.
        easy.
    + repeat rewrite <- trim_otrim in *.
      eapply trim_cons_non_empty in NE1.
      rewrite NE1 in *.
      eapply trim_cons_non_empty in NE2.
      rewrite NE2 in *.
      destruct o1, o2.
      * simpl. easy.
      * simpl in *. 
        rewrite IH.
        destruct (merge' Γ1 Γ2). easy.
        simpl.
        easy.
      * simpl in *. 
        rewrite IH.
        destruct (merge' Γ1 Γ2). easy.
        simpl.
        easy.
      * simpl in *.
        rewrite IH.
        destruct (merge' Γ1 Γ2) eqn:E. easy.
        simpl in *.
        destruct (trim c).
        destruct (trim Γ1). inversion NE1. 
        destruct (trim Γ2). inversion NE2.
        simpl in IH. destruct (merge_wire o o0) eqn:EW. inversion IH.
        destruct (merge' c0 c1) eqn:E'. inversion IH.
        destruct o, o0;
        simpl in EW; inversion EW as [S]; rewrite <- S in IH; inversion IH.
        easy.
Qed.

Lemma trim_merge : forall Γ Γ1 Γ2, Γ == Γ1 ∙ Γ2 ->
                              otrim Γ == otrim Γ1 ∙ otrim Γ2.
Proof.
  intros Γ Γ1 Γ2 M.
  apply merge_fun_ind in M.
  induction M.
  - split. 
    simpl; apply valid_valid. 
    rewrite merge_nil_l; easy.
  - split. 
    simpl; apply valid_valid. 
    rewrite merge_nil_r; easy.
  - split.
    simpl. apply valid_valid.
    destruct (eq_dec_empty_ctx Γ).
    + apply merge_ind_fun in M.
      specialize (merge_empty _ _ _ M e) as [E1 E2]. 
      inversion m; subst; simpl.
      * repeat rewrite trim_empty; easy.
      * repeat rewrite trim_empty; easy.
      * repeat rewrite trim_empty; easy.
    + apply trim_non_empty in n.
      destruct IHM as [V IHM].
      inversion m; subst; simpl in *.
      * destruct (trim Γ) eqn:E. easy.
        destruct (trim Γ1) eqn:E1, (trim Γ2) eqn:E2; 
          simpl in *; inversion IHM; easy.
      * destruct (trim Γ1) eqn:E1, (trim Γ2) eqn:E2; 
          simpl in *; inversion IHM; easy.
      * destruct (trim Γ1) eqn:E1, (trim Γ2) eqn:E2; 
          simpl in *; inversion IHM; easy.
Qed.        

(* length is the actual length of the underlying list, as opposed to size, which
 * is the number of Some entries in the list 
 *)
Definition octx_length (Γ : OCtx) : nat :=
  match Γ with
  | Invalid => O
  | Valid ls => length ls
  end.


(* property of merge *)

Lemma merge_dec Γ1 Γ2 : is_valid (Γ1 ⋓ Γ2) + {Γ1 ⋓ Γ2 = Invalid}.
Proof.
  induction Γ1 as [ | Γ1]; [ right; auto | ].
  destruct  Γ2 as [ | Γ2]; [ right; auto | ].
  revert Γ2; induction Γ1 as [ | o1 Γ1]; intros Γ2.
  { simpl. left. apply valid_valid. }
  destruct Γ2 as [ | o2 Γ2]. 
  { simpl. left. apply valid_valid. }
  destruct (IHΓ1 Γ2) as [IH | IH].
  - destruct o1 as [ | W1]; destruct o2 as [ | W2]; simpl in *. 
    { right; auto. }
    { left; destruct (merge' Γ1 Γ2); auto. apply valid_valid. }
    { left; destruct (merge' Γ1 Γ2); auto. apply valid_valid. }
    { left; destruct (merge' Γ1 Γ2); auto. apply valid_valid. }    
  - right. simpl in *. rewrite IH. destruct (merge_wire o1 o2); auto.
Defined.

(* Patterns and Gates *)

Open Scope circ_scope.
Inductive Pat : WType ->  Set :=
| unit : Pat One
| qubit : Var -> Pat Qubit
| bit : Var -> Pat Bit
| pair : forall {W1 W2}, Pat W1 -> Pat W2 -> Pat (W1 ⊗ W2).


Fixpoint pat_to_list {w} (p : Pat w) : list Var :=
  match p with
  | unit => []
  | qubit x => [x]
  | bit x => [x]
  | pair p1 p2 => pat_to_list p1 ++ pat_to_list p2
  end.


Fixpoint pat_map {w} (f : Var -> Var) (p : Pat w) : Pat w :=
  match p with
  | unit => unit
  | qubit x => qubit (f x)
  | bit x => bit (f x)
  | pair p1 p2 => pair (pat_map f p1) (pat_map f p2)
  end.


Reserved Notation "Γ ⊢ p ':Pat'" (at level 30).

Inductive Types_Pat : OCtx -> forall {W : WType}, Pat W -> Set :=
| types_unit : ∅ ⊢ unit :Pat
| types_qubit : forall x Γ, SingletonCtx x Qubit Γ ->  Γ ⊢ qubit x :Pat
| types_bit : forall x Γ, SingletonCtx x Bit Γ -> Γ ⊢ bit x :Pat
| types_pair : forall Γ1 Γ2 Γ w1 w2 (p1 : Pat w1) (p2 : Pat w2),
        is_valid Γ 
      -> Γ = Γ1 ⋓ Γ2
      -> Γ1 ⊢ p1 :Pat
      -> Γ2 ⊢ p2 :Pat
      -> Γ  ⊢ pair p1 p2 :Pat
where "Γ ⊢ p ':Pat'" := (@Types_Pat Γ _ p).

Lemma pat_ctx_valid : forall Γ W (p : Pat W), Γ ⊢ p :Pat -> is_valid Γ.
Proof. intros Γ W p TP. unfold is_valid. inversion TP; eauto. Qed.

Lemma octx_wtype_size : forall w (p : Pat w) (Γ : OCtx),
      Γ ⊢ p:Pat -> size_wtype w = size_octx Γ.
Proof.
  intros w p Γ H.
  dependent induction H; simpl; auto.
  * apply Singleton_size in s. easy. 
  * apply Singleton_size in s. easy. 
  * subst.
    rewrite size_octx_merge; auto.
Qed.

Lemma ctx_wtype_size : forall w (p : Pat w) (Γ : Ctx),
      Γ ⊢ p:Pat -> size_wtype w = size_ctx Γ.
Proof.
  intros w p Γ H.
  replace (size_ctx Γ) with (size_octx Γ) by easy.
  eapply octx_wtype_size; apply H.
Qed.

Lemma size_wtype_length : forall {w} (p : Pat w),
    length (pat_to_list p) = size_wtype w.
Proof.
  induction p; simpl; auto.
  rewrite app_length.
  rewrite IHp1, IHp2.
  auto.
Qed.

Open Scope circ_scope.
Inductive Unitary : WType -> Set := 
  | _H         : Unitary Qubit 
  | _X         : Unitary Qubit
  | _Y         : Unitary Qubit
  | _Z         : Unitary Qubit
  | _R_        : R -> Unitary Qubit 
  | ctrl      : forall {W} (U : Unitary W), Unitary (Qubit ⊗ W) 
  | bit_ctrl  : forall {W} (U : Unitary W), Unitary (Bit ⊗ W).

(* Additional gate notations *)
Notation CNOT := (ctrl _X).
Notation CCNOT := (ctrl (ctrl _X)).

Notation _S := (_R_ (PI / 2)). 
Notation _T := (_R_ (PI / 4)). (* π / 8 gate *)

Fixpoint trans {W} (U : Unitary W) : Unitary W :=
  match U with
  | _R_ ϕ       => _R_ (- ϕ)
  | ctrl U'     => ctrl (trans U')
  | bit_ctrl U' => bit_ctrl (trans U')
  | U'          => U' (* our other unitaries are their own adjoints *)
  end.

Inductive Gate : WType -> WType -> Set := 
  | U : forall {W} (u : Unitary W), Gate W W
  | BNOT     : Gate Bit Bit
  | init0   : Gate One Qubit
  | init1   : Gate One Qubit
  | new0    : Gate One Bit
  | new1    : Gate One Bit
  | meas    : Gate Qubit Bit
  | measQ   : Gate Qubit Qubit
  | discard : Gate Bit One
  | assert0 : Gate Qubit One
  | assert1 : Gate Qubit One.

Coercion U : Unitary >-> Gate.
Close Scope circ_scope.


(*** Automation ***)

Ltac PCMize := 
  simpl translate in *;
  try replace merge with m by auto;
  try replace ∅ with ⊤ by auto;
  try replace Invalid with ⊥ by auto.

Ltac unPCMize := 
  simpl translate in *;
  simpl m in *;
  simpl ⊤ in *;
  simpl ⊥ in *.

(* Port of the monoid tactic to OCtxs *)
Ltac monoid := PCMize; try Monoid.monoid.

(* Validate tactic *)
Ltac validate :=
  unPCMize;
  repeat ((*idtac "validate";*) match goal with
  (* Pattern contexts are valid *)
  | [H : Types_Pat _ _ |- _ ]    => apply pat_ctx_valid in H
  (* Solve trivial *)
  | [|- is_valid (Valid _)]                    => apply valid_valid
  | [H : is_valid ?Γ |- is_valid ?Γ ]          => exact H
  | [H: is_valid (?Γ1 ⋓ ?Γ2) |- is_valid ?Γ1 ] => eapply valid_l; exact H
  | [H: is_valid (?Γ1 ⋓ ?Γ2) |- is_valid ?Γ2 ] => eapply valid_r; exact H
  | [H: is_valid (?Γ1 ⋓ ?Γ2) |- is_valid (?Γ2 ⋓ ?Γ1) ] => rewrite merge_comm; exact H
  (* Remove nils *)
  | [|- context [∅ ⋓ ?Γ] ]             => rewrite (merge_nil_l Γ)
  | [|- context [?Γ ⋓ ∅] ]             => rewrite (merge_nil_r Γ)
  (* Reduce hypothesis to binary disjointness *)
  | [H: is_valid (?Γ1 ⋓ (?Γ2 ⋓ ?Γ3)) |- _ ] => rewrite (merge_assoc Γ1 Γ2 Γ3) in H
  | [H: is_valid (?Γ1 ⋓ ?Γ2 ⋓ ?Γ3) |- _ ]   => apply valid_split in H as [? [? ?]]
  (* Reduce goal to binary disjointness *)
  | [|- is_valid (?Γ1 ⋓ (?Γ2 ⋓ ?Γ3)) ] => rewrite (merge_assoc Γ1 Γ2 Γ3)
  | [|- is_valid (?Γ1 ⋓ ?Γ2 ⋓ ?Γ3) ]   => apply valid_join; validate
  end).

Ltac has_evars term := 
  match term with
    | ?L = ?R         => has_evars (L ⋓ R)
    | ?L == ?R1 ∙ ?R2 => has_evars (L ⋓ R1 ⋓ R2)
    | ?Γ1 ⋓ ?Γ2       => has_evar Γ1; has_evar Γ2
    | ?Γ1 ⋓ ?Γ2       => has_evars Γ1
    | ?Γ1 ⋓ ?Γ2       => has_evars Γ2
  end.

Ltac goal_evars :=
  match goal with
  | [ |- ?g ] => has_evars g
  end.

(* Proofs about merge relation *)
Ltac solve_merge :=
  match goal with 
  | [ |- ?g ] => has_evars g
  | [ |- _  ] => 
    repeat match goal with
    | [ H : _ == _ ∙ _ |- _ ] => destruct H
    end;
    subst;
    repeat match goal with
    | [ |- _ == _ ∙ _ ] => split
    | [ |- is_valid _ ] => validate
    | [ |- _ = _ ] => monoid
    end
  end.

(*** Constructing Typed Patterns ***)

Fixpoint mk_typed_bit (Γ : Ctx) : Pat Bit * Ctx :=
  match Γ with 
  | []           => (bit O, [Some Bit])
  | None :: Γ'   => (bit O, [Some Bit])
  | Some W :: Γ' => let (p,Γ'') := mk_typed_bit Γ' in
                   match p with
                   | bit n => (bit (S n), None :: Γ'')
                   end
  end.

Fixpoint mk_typed_qubit (Γ : Ctx) : Pat Qubit * Ctx :=
  match Γ with 
  | []           => (qubit O, [Some Qubit])
  | None :: Γ'   => (qubit O, [Some Qubit])
  | Some W :: Γ' => let (p,Γ'') := mk_typed_qubit Γ' in
                   match p with
                   | qubit n => (qubit (S n), None :: Γ'')
                   end
  end.
  
(* Opaque Dummy Values *)
Definition dummy_ctx : Ctx. exact []. Qed.

Definition dummy_pat {W} : Pat W.
induction W.
- exact (qubit O).
- exact (bit O).
- exact unit.
- constructor; auto.
Qed.

Fixpoint mk_typed_pat (W : WType) (Γ : Ctx) {struct W} : Pat W * Ctx :=
  match W with
  | One   => (unit, [])
  | Bit   => mk_typed_bit Γ                             
  | Qubit   => mk_typed_qubit Γ                             
  | Tensor W1 W2 => let (p1,Γ1) := mk_typed_pat W1 Γ in
              let Γ1' := (Γ ⋓ Γ1) in 
              let (p2,Γ2) := match Γ1' with 
                             | Invalid => (dummy_pat, dummy_ctx)
                             | Valid Γ1'' => mk_typed_pat W2 Γ1''
                             end in
              match Valid Γ1 ⋓ Valid Γ2 with
              | Invalid    => (dummy_pat, dummy_ctx)
              | Valid Γ12  => ((pair p1 p2), Γ12)
              end
  end.

Lemma typed_pat_merge_valid : forall W Γ Γ' (p : Pat W),
  (p, Γ') = mk_typed_pat W Γ ->
  is_valid (Γ ⋓ Γ').
Proof.
  induction W.
  - induction Γ; intros Γ' p H.
    simpl. validate.
    destruct a.
    + simpl in H.
      dependent destruction p.
      destruct (mk_typed_qubit Γ) as [p1 Γ1] eqn:E1.
      dependent destruction p1.
      inversion H; subst.
      symmetry in E1.
      simpl in IHΓ.
      specialize (IHΓ _ _ E1). 
      simpl in *.
      destruct (merge' Γ Γ1). invalid_contradiction.      
      validate.
    + simpl in *.
      inversion H; subst.
      replace (merge' Γ []) with (Valid Γ ⋓ ∅) by easy.
      rewrite merge_nil_r.
      validate.
  - induction Γ; intros Γ' p H.
    simpl. validate.
    destruct a.
    + simpl in H.
      dependent destruction p.
      destruct (mk_typed_bit Γ) as [p1 Γ1] eqn:E1.
      dependent destruction p1.
      inversion H; subst.
      symmetry in E1.
      simpl in IHΓ.
      specialize (IHΓ _ _ E1). 
      simpl.
      destruct (merge' Γ Γ1). invalid_contradiction.
      validate.
    + simpl in H.
      inversion H; subst.
      simpl.
      replace (merge' Γ []) with (Valid Γ ⋓ ∅) by easy.
      rewrite merge_nil_r.
      validate.
  - intros Γ Γ' p H.
    simpl in H.
    inversion H.
    rewrite merge_nil_r.
    validate.
  - intros Γ Γ' p H.
    simpl in H.
    destruct (mk_typed_pat W1 Γ) as [p1 Γ1] eqn:E1.
    symmetry in E1.    
    destruct (IHW1 _ _ _ E1) as [Γ1' M1].
    simpl in M1. rewrite M1 in H.
    destruct (mk_typed_pat W2 Γ1') as [p2 Γ2] eqn:E2.
    symmetry in E2.    
    destruct (IHW2 _ _ _ E2) as [Γ2' M2].
    simpl in M2. 
    replace (merge' Γ Γ1) with (Γ ⋓ Γ1) in M1 by easy.
    replace (merge' Γ1' Γ2) with (Γ1' ⋓ Γ2) in M2 by easy.
    assert (V2 : is_valid (Γ1' ⋓ Γ2)). rewrite M2; validate.    
    assert (V12 : is_valid (Γ1 ⋓ Γ2)). rewrite <- M1 in V2; validate.
    simpl in V12.
    destruct (merge' Γ1 Γ2) as [|Γ12] eqn:E12. invalid_contradiction.
    inversion H; subst.
    replace (merge' Γ1 Γ2) with (Γ1 ⋓ Γ2) in E12 by easy.
    symmetry in M1, M2, E12.
    rewrite M1, E12 in *.
    validate.
Qed.  

Lemma typed_bit_typed : forall Γ p Γ', (p, Γ') = mk_typed_bit Γ ->
                                   Γ' ⊢ p:Pat.
Proof.
  induction Γ as [|o Γ].
  - intros p Γ' H. simpl in H. inversion H; subst. constructor.
    apply singleton_singleton.
  - intros p Γ' H.
    destruct o.
    + dependent destruction p.
      simpl in H. destruct (mk_typed_bit Γ) as [p Γ'']. 
      dependent destruction p. inversion H. subst.
      specialize (IHΓ (bit v) Γ'' eq_refl). 
      inversion IHΓ; subst.
      constructor.
      constructor.
      easy.
    + simpl in H.
      inversion H; subst.
      constructor.
      constructor.
Qed.

Lemma typed_qubit_typed : forall Γ p Γ', (p, Γ') = mk_typed_qubit Γ ->
                                              Γ' ⊢ p:Pat.
Proof.
  induction Γ as [|o Γ].
  - intros p Γ' H. simpl in H. inversion H; subst. constructor.
    apply singleton_singleton.
  - intros p Γ' H.
    destruct o.
    + dependent destruction p.
      simpl in H. destruct (mk_typed_qubit Γ) as [p Γ'']. 
      dependent destruction p. inversion H. subst.
      specialize (IHΓ (qubit v) Γ'' eq_refl). 
      inversion IHΓ; subst.
      constructor.
      constructor.
      easy.
    + simpl in H.
      inversion H; subst.
      constructor.
      constructor.
Qed.

Lemma typed_pat_typed : forall W Γ (p : Pat W) Γ', 
  (p, Γ') = mk_typed_pat W Γ ->
  Γ' ⊢ p:Pat.
Proof.
  induction W; intros Γ p Γ' H.
  - eapply (typed_qubit_typed Γ); easy. 
  - eapply (typed_bit_typed Γ); easy. 
  - dependent destruction p.
    simpl in H. inversion H; subst.
    constructor.
  - simpl in H.
    destruct (mk_typed_pat W1 Γ) as [p1 Γ1] eqn:E1.
    symmetry in E1.
    destruct (merge' Γ Γ1) as [|Γ1'] eqn:M1. 
      apply typed_pat_merge_valid in E1. 
      simpl in E1. rewrite M1 in E1. invalid_contradiction.
    destruct (mk_typed_pat W2 Γ1') as [p2 Γ2] eqn:E2.
    symmetry in E2.
    destruct (merge' Γ1 Γ2) as [|Γ12] eqn:M2. 
      apply typed_pat_merge_valid in E2. 
      rewrite <- M1 in E2. replace (merge' Γ Γ1) with (Γ ⋓ Γ1) in E2 by easy.
      validate. simpl in H2. rewrite M2 in H2. invalid_contradiction.
    inversion H.
    rewrite <- M2.
    replace (merge' Γ1 Γ2) with (Γ1 ⋓ Γ2) in * by easy.
    econstructor.
    rewrite M2. validate.
    reflexivity.
    eapply IHW1. apply E1.
    eapply IHW2. apply E2.
Qed.

