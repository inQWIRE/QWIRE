Require Import Arith.
Require Import List.
Import ListNotations.
Open Scope list_scope.

(*** Context Definitions ***)

Inductive WType := Qubit | Bit | One | Tensor : WType -> WType -> WType.

Notation "W1 ⊗ W2" := (Tensor W1 W2) (at level 1, left associativity): circ_scope.

Open Scope circ_scope.

(* Coq interpretations of wire types *)
Fixpoint interpret (w:WType) : Set :=
  match w with
    | Qubit => bool
    | Bit => bool 
    | One => Datatypes.unit
    | w1 ⊗ w2 => (interpret w1) * (interpret w2)
  end.

Definition Var := nat.
Definition Ctx := list (option WType).
(* Definition OCtx := option Ctx. *)

Inductive OCtx := 
| Invalid : OCtx 
| Valid : Ctx -> OCtx.


Inductive EmptyCtx : Ctx -> Set :=
| EmptyNil : EmptyCtx []
| EmptyCons : forall Γ, EmptyCtx Γ -> EmptyCtx (None :: Γ)
.

Inductive SingletonCtx : Var -> WType -> Ctx -> Set :=
| SingletonHere : forall w Γ, EmptyCtx Γ -> SingletonCtx 0 w (Some w :: Γ)
| SingletonLater : forall x w ctx, SingletonCtx x w ctx -> SingletonCtx (S x) w (None::ctx)
.

Inductive Equiv : Ctx -> Ctx -> Set :=
| EquivEmpty : forall Γ1 Γ2, EmptyCtx Γ1 -> EmptyCtx Γ2 -> Equiv Γ1 Γ2
| EquivCons  : forall o Γ1 Γ2, Equiv Γ1 Γ2 -> Equiv (o :: Γ1) (o :: Γ2)
.

Lemma empty_singleton_absurd : forall x W Γ A,
      SingletonCtx x W Γ -> EmptyCtx Γ -> A.
Proof.
  intros x W Γ A sing empty.
  revert x W sing A.
  induction empty; intros x W sing A.
  - inversion sing.
  - inversion sing; subst. eapply IHempty; eauto.
Qed.

Lemma equiv_empty : forall Γ1 Γ2, Equiv Γ1 Γ2 -> EmptyCtx Γ1 -> EmptyCtx Γ2.
Proof.
  induction 1; intros empty; auto.
  inversion empty; subst.
  constructor. 
  apply IHEquiv; auto.
Qed.

Lemma equiv_singleton : forall Γ1 Γ2 x W,
      Equiv Γ1 Γ2 -> SingletonCtx x W Γ1 -> SingletonCtx x W Γ2.
Proof.
  intros Γ1 Γ2 x W equiv sing. revert x W sing.
  induction equiv; intros x W sing.
  - eapply empty_singleton_absurd; eauto.
  - inversion sing; subst.
    * constructor. eapply equiv_empty; eauto.
    * constructor. apply IHequiv. auto.
Qed.



Fixpoint singleton (x : Var) (W : WType) : Ctx :=
  match x with
  | O => [Some W]
  | S x => None :: singleton x W
  end.

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

Notation "∅" := (Valid []).
Infix "⋓" := merge (left associativity, at level 50).
Coercion Valid : Ctx >-> OCtx.

(*** Facts about ⋓ ***)

Lemma merge_merge' : forall (Γ1 Γ2 : Ctx), Γ1 ⋓ Γ2 = (merge' Γ1 Γ2).
Proof. reflexivity. Qed.

(* Note that the reverse is not always true - we would need to 
   check validity and not-emptyness of the contexts *)
Lemma merge_cancel_l : forall Γ Γ1 Γ2 , Γ1 = Γ2 -> Γ ⋓ Γ1 = Γ ⋓ Γ2.
Proof. intros; subst; reflexivity. Qed.

Lemma merge_cancel_r : forall Γ Γ1 Γ2 , Γ1 = Γ2 -> Γ1 ⋓ Γ = Γ2 ⋓ Γ.
Proof. intros; subst; reflexivity. Qed.

Lemma merge_I_l : forall Γ, Invalid ⋓ Γ = Invalid. Proof. reflexivity. Qed.

Lemma merge_I_r : forall Γ, Γ ⋓ Invalid = Invalid. Proof. destruct Γ; reflexivity. Qed.

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
Qed.

Lemma merge_nil_l : forall Γ, ∅ ⋓ Γ = Γ. Proof. destruct Γ; reflexivity. Qed.

Lemma merge_nil_r : forall Γ, Γ ⋓ ∅ = Γ. 
Proof. destruct Γ; trivial. destruct c; trivial. Qed. 

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
Qed.    

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
Qed.

(*** Semi-ring ***)

(*** Automation ***)

(* Assumes at most one evar *)
Ltac monoid := 
  try match goal with
  | [ |- ?Γ1 = ?Γ2 ] => has_evar Γ1; symmetry
  end;
  repeat (
  repeat (rewrite <- merge_assoc); 
  match goal with
  | [ |- ?Γ = ?Γ ]                  => reflexivity
  | [ |- ?Γ1 = ?Γ2 ]                => is_evar Γ2; reflexivity
  (* remove nils *)
  | [ |- context[?Γ ⋓ ∅] ]          => rewrite (merge_nil_r Γ)
  | [ |- context[∅ ⋓ ?Γ] ]          => rewrite (merge_nil_l Γ)
  (* move evar to far right *)
  | [ |- _ = ?Γ ⋓ ?Γ' ]             => is_evar Γ; rewrite (merge_comm Γ Γ')
  (* solve nil evars *)
  | [ |- ?Γ = ?Γ ⋓ _ ]              => rewrite merge_nil_r; reflexivity  
  (* cycle and apply merge_cancel_l *)
  | [ |- ?Γ ⋓ _ = ?Γ ⋓ _ ]          => apply merge_cancel_l
  | [ |- ?Γ1 ⋓ ?Γ1' = ?Γ ⋓ _ ]      => rewrite (merge_comm Γ1 Γ1')
(*| [ |- context[?Γ] = ?Γ ⋓ _ ]     => move_left Γ *)
  end).

(*
Ltac move_left Γ :=
  try match goal with
      | [ |- Γ ⋓ _ = _ ] => return
      | [ |- context[Γ] ⋓ _ = _ ] => 
      | [ |- _ ⋓ context[Γ] = _ ] => 
*)

Lemma test1 : forall x y z, x ⋓ y ⋓ z = z ⋓ x ⋓ y.
Proof. intros. monoid. Qed.

Lemma test2 : forall x, x ⋓ ∅ = x.
Proof. intros. monoid. Qed.

Lemma test21 : forall x, x ⋓ ∅ = x ⋓ ∅.
Proof. intros. monoid. Qed.

Lemma test3 : forall w x y z, x ⋓ (y ⋓ z) ⋓ w = w ⋓ z ⋓ (x ⋓ y).
Proof. intros. monoid. Qed.

Lemma test4 : forall w x y z, x ⋓ (y ⋓ ∅ ⋓ z) ⋓ w = w ⋓ z ⋓ (x ⋓ y).
Proof. intros. monoid. Qed.

Inductive Eqq {A} : A -> A -> Prop := 
| eqq : forall x, Eqq x x.

Lemma create_evar : forall A (x x' y z : A) f, Eqq x x' -> f y x = z -> f y x' = z.
Proof. intros. inversion H; subst. reflexivity. Qed.

Lemma test_evar_ctx : forall x y z, x ⋓ y ⋓ z = z ⋓ x ⋓ y.
Proof. intros. eapply create_evar. 2: monoid. constructor. Qed.


(* Extra helper functions *)
Definition xor_option {a} (o1 : option a) (o2 : option a) : option a :=
  match o1, o2 with
  | Some a1, None => Some a1
  | None, Some a2 => Some a2
  | _   , _       => None
  end.

Definition cons_o (o : option WType) (Γ : OCtx) : OCtx :=
  match Γ with
  | Invalid => Invalid
  | Valid Γ' => Valid (o :: Γ')
  end.

Fixpoint index (ls : OCtx) (i : nat) : option WType :=
  match ls with
  | Invalid => None
  | Valid [] => None
  | Valid (h :: t) => match i with
              | O => h
              | S i => index (Valid t) i
              end
  end.


Definition lengthO (ls : OCtx) : nat :=
  match ls with
  | Invalid => O
  | Valid ls => length ls
  end.

Lemma eta_OCtx : forall (Ω : OCtx),
                 match Ω with
                 | Invalid => Invalid
                 | Valid Ω' => Ω'
                 end = Ω.
Admitted.

Inductive EquivO : OCtx -> OCtx -> Set :=
| EquivInvalid : EquivO Invalid Invalid
| EquivValid : forall Γ1 Γ2, Equiv Γ1 Γ2 -> EquivO (Valid Γ1) (Valid Γ2)
.

Lemma equiv_refl : forall Γ, Equiv Γ Γ.
Admitted.
Lemma equivO_refl : forall Γ, EquivO Γ Γ.
Admitted.

Lemma equivO_symm : forall Γ1 Γ2, EquivO Γ1 Γ2 -> EquivO Γ2 Γ1.
Admitted.

Lemma equiv_merge_empty : forall Γ1 Γ2, EmptyCtx Γ2 -> EquivO Γ1 (Γ1 ⋓ Γ2).
Admitted.

Inductive Merge_option : option WType -> option WType -> option WType -> Set :=
| MergeNone : Merge_option None None None
| MergeSomeL : forall a, Merge_option (Some a) None (Some a)
| MergeSomeR : forall a, Merge_option None (Some a) (Some a)
.

Inductive Merge : Ctx -> Ctx -> Ctx -> Set :=
| MergeEmptyL : forall Γ1 Γ2 Γ, 
               EmptyCtx Γ1 -> Equiv Γ2 Γ -> Merge Γ1 Γ2 Γ
| MergeEmptyR : forall Γ1 Γ2 Γ, 
               EmptyCtx Γ2 -> Equiv Γ1 Γ -> Merge Γ1 Γ2 Γ
| MergeCons : forall o1 o2 o Γ1 Γ2 Γ,
              Merge_option o1 o2 o -> Merge Γ1 Γ2 Γ -> 
              Merge (o1 :: Γ1) (o2 :: Γ2) (o :: Γ)
.
Inductive MergeO : OCtx -> OCtx -> OCtx -> Set :=
| MergeInvalidL : forall Γ1 Γ, Equiv Γ1 Γ -> MergeO Γ1 Invalid Γ
| MergeInvalidR : forall Γ2 Γ, Equiv Γ2 Γ -> MergeO Invalid Γ2 Γ
| MergeValid : forall Γ1 Γ2 Γ, Merge Γ1 Γ2 Γ -> MergeO Γ1 Γ2 Γ
.

Lemma MergeOEmptyL : forall Γ1 Γ2 Γ,
      EmptyCtx Γ1 -> EquivO Γ2 Γ -> MergeO Γ1 Γ2 Γ.
Admitted.
Lemma MergeOEmptyR : forall Γ1 Γ2 Γ,
      EmptyCtx Γ2 -> EquivO Γ1 Γ -> MergeO Γ1 Γ2 Γ.
Admitted.
Lemma MergeOCons : forall o1 o2 o Γ1 Γ2 Γ,
                   Merge_option o1 o2 o -> 
                   MergeO Γ1 Γ2 Γ ->
                   MergeO (cons_o o1 Γ1) (cons_o o2 Γ2) (cons_o o Γ).
Admitted.

Lemma merge_merge : forall (Γ1 Γ2 Γ : Ctx), Γ1 ⋓ Γ2 = Valid Γ -> Merge Γ1 Γ2 Γ.
Proof.
  induction Γ1 as [ | o1 Γ1]; intros Γ2 Γ merge.
  - inversion merge; subst. apply MergeEmptyL; [constructor | apply equiv_refl].
  - destruct Γ2 as [ | o2 Γ2].
    * inversion merge. apply MergeEmptyR; [constructor | apply equiv_refl].
    * destruct o1 as [W1 | ]; destruct o2 as [W2 | ]; 
      simpl in *; try (inversion merge; fail);
      try (remember (merge' Γ1 Γ2) as Γ';
        destruct Γ' as [ | Γ' ]; try (inversion merge; fail);
        inversion merge; subst;
        constructor; [constructor | apply IHΓ1; auto]).
Qed.

Lemma merge_merge_inv : forall (Γ1 Γ2 Γ : Ctx), Merge Γ1 Γ2 Γ -> Γ1 ⋓ Γ2 = Valid Γ.
Admitted.

Lemma equiv_split : forall Γ1 Γ2 Γ Γ',
      Merge Γ1 Γ2 Γ ->
      Equiv Γ Γ' ->
      {Γ1' : Ctx & {Γ2' : Ctx & Merge Γ1' Γ2' Γ' * Equiv Γ1 Γ1' * Equiv Γ2 Γ2'}}%type.
Admitted.

Lemma Ctx_nil_inversion' : forall (Γ1 Γ2 : Ctx), Γ1 ⋓ Γ2 = ∅ -> (Γ1 = []) * (Γ2 = []).
Proof.
  induction Γ1 as [ | o Γ1]; intros Γ2; try inversion 1; auto.
  destruct Γ2 as [ | o' Γ2]; try inversion H1.
  destruct o; destruct o'; simpl in *; try inversion H. 
  remember (merge' Γ1 Γ2) as Γ0. destruct Γ0; try inversion H3.
  remember (merge' Γ1 Γ2) as Γ0. destruct Γ0; try inversion H3.
  remember (merge' Γ1 Γ2) as Γ0. destruct Γ0; try inversion H3.
Qed.

Lemma Ctx_nil_inversion : forall (Γ1 Γ2 : OCtx), Γ1 ⋓ Γ2 = ∅ -> (Γ1 = ∅) * (Γ2 = ∅).
Proof.
  intros Γ1 Γ2 eq.
  destruct Γ1 as [ | Γ1]; try (inversion eq; fail).
  destruct Γ2 as [ | Γ2]; try (inversion eq; fail).
  destruct Ctx_nil_inversion' with (Γ1 := Γ1) (Γ2 := Γ2) as [eq1 eq2]; auto.
  inversion eq1; inversion eq2; auto.
Qed.


Lemma Ctx_cons_inversion : forall Γ1 Γ2 o Γ,
      Γ1 ⋓ Γ2 = Valid (o :: Γ) ->
      {o1 : option WType & {o2 : option WType & {Γ1' : Ctx & {Γ2' : Ctx 
      & (Γ1 = Valid (o1 :: Γ1')) * (Γ2 = Valid (o2 :: Γ2')) * (Γ1' ⋓ Γ2' = Valid Γ)
        * (merge_wire o1 o2 = Valid [o])}}}}%type.
Admitted.


