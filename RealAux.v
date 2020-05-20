Require Export Reals.
Require Import Psatz.

(******************************************)
(** Relevant lemmas from Rcomplements.v. **)
(******************************************)

Open Scope R_scope.

Lemma Rle_minus_l : forall a b c,(a - c <= b <-> a <= b + c). Proof. intros. lra. Qed.
Lemma Rlt_minus_r : forall a b c,(a < b - c <-> a + c < b). Proof. intros. lra. Qed.
Lemma Rlt_minus_l : forall a b c,(a - c < b <-> a < b + c). Proof. intros. lra. Qed.
Lemma Rle_minus_r : forall a b c,(a <= b - c <-> a + c <= b). Proof. intros. lra. Qed.
Lemma Rminus_le_0 : forall a b, a <= b <-> 0 <= b - a. Proof. intros. lra. Qed.
Lemma Rminus_lt_0 : forall a b, a < b <-> 0 < b - a. Proof. intros. lra. Qed.

(* Automation *)

Lemma Rminus_unfold : forall r1 r2, (r1 - r2 = r1 + -r2). Proof. reflexivity. Qed.
Lemma Rdiv_unfold : forall r1 r2, (r1 / r2 = r1 */ r2). Proof. reflexivity. Qed.

Hint Rewrite Rminus_unfold Rdiv_unfold Ropp_0 Ropp_involutive Rplus_0_l Rplus_0_r 
             Rmult_0_l Rmult_0_r Rmult_1_l Rmult_1_r : R_db.
Hint Rewrite <- Ropp_mult_distr_l Ropp_mult_distr_r : R_db.
Hint Rewrite Rinv_l Rinv_r sqrt_sqrt using lra : R_db.

Notation "√ n" := (sqrt n) (at level 20) : R_scope.

(* Useful Lemmas *)

Lemma Rmult_div_assoc : forall (x y z : R), x * (y / z) = x * y / z.
Proof. intros. unfold Rdiv. rewrite Rmult_assoc. reflexivity. Qed.

Lemma Rmult_div : forall r1 r2 r3 r4 : R, r2 <> 0 -> r4 <> 0 -> 
  r1 / r2 * (r3 / r4) = r1 * r3 / (r2 * r4). 
Proof. intros. unfold Rdiv. rewrite Rinv_mult_distr; trivial. lra. Qed.

Lemma Rdiv_cancel :  forall r r1 r2 : R, r1 = r2 -> r / r1 = r / r2.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Rsum_nonzero : forall r1 r2 : R, r1 <> 0 \/ r2 <> 0 -> r1 * r1 + r2 * r2 <> 0. 
Proof.
  intros.
  replace (r1 * r1)%R with (r1 ^ 2)%R by lra.
  replace (r2 * r2)%R with (r2 ^ 2)%R by lra.
  specialize (pow2_ge_0 (r1)). intros GZ1.
  specialize (pow2_ge_0 (r2)). intros GZ2.
  destruct H.
  - specialize (pow_nonzero r1 2 H). intros NZ. lra.
  - specialize (pow_nonzero r2 2 H). intros NZ. lra.
Qed.

(****************)
(* Square Roots *)
(****************)

Lemma pow2_sqrt : forall x:R, 0 <= x -> (√ x) ^ 2 = x.
Proof. intros; simpl; rewrite Rmult_1_r, sqrt_def; auto. Qed.

Lemma sqrt_pow : forall (r : R) (n : nat), (0 <= r)%R -> (√ (r ^ n) = √ r ^ n)%R.
Proof.
  intros r n Hr.
  induction n.
  simpl. apply sqrt_1.
  rewrite <- 2 tech_pow_Rmult.
  rewrite sqrt_mult_alt by assumption.
  rewrite IHn. reflexivity.
Qed.

Lemma pow2_sqrt2 : (√ 2) ^ 2 = 2.
Proof. apply pow2_sqrt; lra. Qed.

Lemma pown_sqrt : forall (x : R) (n : nat), 
  0 <= x -> √ x ^ (S (S n)) = x * √ x ^ n.
Proof.
  intros. simpl. rewrite <- Rmult_assoc. rewrite sqrt_sqrt; auto.
Qed.  

Lemma sqrt_neq_0_compat : forall r : R, 0 < r -> √ r <> 0.
Proof. intros. specialize (sqrt_lt_R0 r). lra. Qed.

Lemma sqrt_inv : forall (r : R), 0 < r -> √ (/ r) = (/ √ r)%R.
Proof.
  intros.
  replace (/r)%R with (1/r)%R by lra.
  rewrite sqrt_div_alt, sqrt_1 by lra.
  lra.
Qed.  

Lemma sqrt2_inv : √ (/ 2) = (/ √ 2)%R.
Proof. apply sqrt_inv; lra. Qed.  

Lemma sqrt_sqrt_inv : forall (r : R), 0 < r -> (√ r * √ / r)%R = 1.
Proof. 
  intros. 
  rewrite sqrt_inv; trivial. 
  rewrite Rinv_r; trivial. 
  apply sqrt_neq_0_compat; easy.
Qed.

Lemma sqrt2_sqrt2_inv : (√ 2 * √ / 2)%R = 1.
Proof. apply sqrt_sqrt_inv. lra. Qed.

Lemma sqrt2_inv_sqrt2 : ((√ / 2) * √ 2)%R = 1.
Proof. rewrite Rmult_comm. apply sqrt2_sqrt2_inv. Qed.

Lemma sqrt2_inv_sqrt2_inv : ((√ / 2) * (√ / 2) = /2)%R.
Proof. 
  rewrite sqrt2_inv. field_simplify. 
  rewrite pow2_sqrt2. easy. 
  apply sqrt_neq_0_compat; lra. 
Qed.

(* Automation *)
Ltac R_field_simplify := repeat field_simplify_eq [pow2_sqrt2 sqrt2_inv].
Ltac R_field := R_field_simplify; easy.
