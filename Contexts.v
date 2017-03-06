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

Inductive SingletonCtx : Var -> WType -> Ctx -> Set :=
| SingletonHere : forall w, SingletonCtx 0 w (Some w :: [])
| SingletonLater : forall x w ctx, SingletonCtx x w ctx -> SingletonCtx (S x) w (None::ctx)
.

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

(* Here we attempt to show that OCtx's with merge and the function below form a 
   semi-ring, despite the unfortunate reality that they do not.

   This allows us to use Coq's powerful Ring tactic, which should ignore the 
   Ctx_mul function below, as we never use it. *)

Require Import Ring.
Require Import Omega.

Fixpoint Ctx_mul (Γ1 Γ2 : OCtx) := 
  match Γ1, Γ2 with
  | Invalid, _ => Γ2
  | _, Invalid => Γ1
  | _, _       => Valid []
  end.

Infix "⋒" := Ctx_mul (at level 50, no associativity).

Lemma Ctx_mul_1_l : forall n, Invalid ⋒ n = n. Proof. reflexivity. Qed.
Lemma Ctx_mul_0_l : forall n, ∅ ⋒ n = ∅.       Proof. destruct n; reflexivity. Qed.
Lemma Ctx_mul_sym : forall n m, n ⋒ m = m ⋒ n. Proof. destruct n, m; reflexivity. Qed.
Lemma Ctx_mul_assoc : forall n m p, n ⋒ (m ⋒ p) = (n ⋒ m) ⋒ p. 
Proof. destruct m, n, p; reflexivity. Qed.
Lemma Ctx_distr_l : forall n m p, (n ⋓ m) ⋒ p = (n ⋒ p) ⋓ (m ⋒ p).
Proof. intros. destruct n, m, p; simpl; trivial. (* so close! *) Admitted. 

Definition ring_proof := (mk_srt ∅ Invalid merge Ctx_mul eq merge_nil_l merge_comm merge_assoc Ctx_mul_1_l Ctx_mul_0_l Ctx_mul_sym Ctx_mul_assoc Ctx_distr_l).

Check ring_proof.

Add Ring lin_contexts : ring_proof.

Lemma test1 : forall x y z, x ⋓ y ⋓ z = z ⋓ x ⋓ y.
Proof. intros. ring. Qed.

Lemma test2 : forall x, x ⋓ ∅ = x.
Proof. intros. ring. Qed.

Lemma test21 : forall x, x ⋓ ∅ = x ⋓ ∅.
Proof. intros. ring. Qed.

Lemma test3 : forall w x y z, x ⋓ (y ⋓ z) ⋓ w = w ⋓ z ⋓ (x ⋓ y).
Proof. intros. ring. Qed.

Lemma test4 : forall w x y z, x ⋓ (y ⋓ ∅ ⋓ z) ⋓ w = w ⋓ z ⋓ (x ⋓ y).
Proof. intros. ring. Qed.

Inductive Eqq {A} : A -> A -> Prop := 
| eqq : forall x, Eqq x x.

Lemma create_evar : forall A (x x' y z : A) f, Eqq x x' -> f y x = z -> f y x' = z.
Proof. intros. inversion H; subst. reflexivity. Qed.

Lemma test_evar_nat : forall x y z, (x + y + z = z + x + y)%nat.
Proof. intros. eapply create_evar. (*Focus 2. ring. Fails.*) constructor. ring. Qed.

Lemma test_evar_ctx : forall x y z, x ⋓ y ⋓ z = z ⋓ x ⋓ y.
Proof. intros. eapply create_evar. (*Focus 2. ring. Fails.*) constructor. ring. Qed.

(*** Automation ***)

Ltac ring_solve := intros; compute in *; subst; try ring.

Ltac merge_solve := 
  intros;
  compute in *;
  subst;
  repeat match goal with 
  | [ |- ?Γ = ?Γ ]                  => reflexivity 
  | [ |- context[?Γ ⋓ ∅] ]          => rewrite (merge_nil_r Γ)
  | [ |- context[∅ ⋓ ?Γ] ]          => rewrite (merge_nil_l Γ)
  | [ |- ?Γ ⋓ _ = ?Γ  ]             => apply merge_nil_r
  | [ |- _ ⋓ ?Γ = ?Γ ]              => apply merge_nil_l
  | [ |- ?Γ = ?Γ ⋓ _ ]              => rewrite merge_nil_r; reflexivity
  | [ |- ?Γ = _ ⋓ ?Γ ]              => rewrite merge_nil_l; reflexivity
  | [ |- ?Γ ⋓ _ = ?Γ ⋓ _ ]          => apply merge_cancel_l
  | [ |- ?Γ ⋓ _ = ?Γ' ⋓ ?Γ ⋓ _ ]    => rewrite (merge_comm Γ' Γ)
  (* These are too precise, will make general rules *)
  | [ |- ?Γ ⋓ ?Γ1 ⋓ _ = ?Γ ⋓ ?Γ2 ⋓ _ ] => rewrite (merge_assoc Γ Γ1), 
                                        (merge_assoc Γ Γ2); idtac "assoc right 0"
  | [ |- ?Γ1 ⋓ ?Γ ⋓ _ = ?Γ2 ⋓ ?Γ ⋓ _ ] => rewrite (merge_comm Γ1 Γ), (merge_comm Γ2 Γ);
                                       rewrite (merge_assoc Γ Γ1), (merge_assoc Γ Γ2);
                                       idtac "assoc right 1"
  | [ |- ?Γ ⋓ ?Γ1 ⋓ _ = ?Γ2 ⋓ ?Γ ⋓ _ ] => rewrite (merge_comm Γ2 Γ); 
                                       rewrite (merge_assoc Γ Γ1), (merge_assoc Γ Γ2);
                                       idtac "assoc right 2"
  | [ |- ?Γ1 ⋓ ?Γ ⋓ _ = ?Γ ⋓ ?Γ2 ⋓ _ ] => rewrite (merge_comm Γ1 Γ);
                                       rewrite (merge_assoc Γ Γ1), (merge_assoc Γ Γ2);
                                       idtac "assoc right 3"
  | [ |- ?Γ ⋓ _ = _ ⋓ ?Γ ]          => apply merge_comm (* danger? *)
  | [ |- _ ⋓ ?Γ = ?Γ ⋓ _ ]          => apply merge_comm (* danger? *)
  | [ |- ?Γ1 = ?Γ2 ]                => is_evar Γ1; reflexivity
  | [ |- ?Γ1 = ?Γ2 ]                => is_evar Γ2; reflexivity
  | [ |- ?Γ1 ⋓ (?Γ2 ⋓ ?Γ3) = _ ]    => rewrite <- (merge_assoc Γ1 Γ2 Γ3); 
                                     idtac "rassoc lhs"
  | [ |- _ = ?Γ1 ⋓ (?Γ2 ⋓ ?Γ3) ]    => rewrite <- (merge_assoc Γ1 Γ2 Γ3); 
                                     idtac "rassoc rhs"
  end.
