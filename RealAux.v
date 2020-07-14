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


Lemma Rpow_le1: forall (x : R) (n : nat), 0 <= x <= 1 -> x ^ n <= 1.
Proof.
  intros; induction n.
  - simpl; lra.
  - simpl.
    rewrite <- Rmult_1_r.
    apply Rmult_le_compat; try lra.
    apply pow_le; lra.
Qed.
    
(* The other side of Rle_pow, needed below *)
Lemma Rle_pow_le1: forall (x : R) (m n : nat), 0 <= x <= 1 -> (m <= n)%nat -> x ^ n <= x ^ m.
Proof.
  intros x m n [G0 L1] L.
  remember (n - m)%nat as p.
  replace n with (m+p)%nat in * by lia.
  clear -G0 L1.
  rewrite pow_add.
  rewrite <- Rmult_1_r.
  apply Rmult_le_compat; try lra.
  apply pow_le; trivial.
  apply pow_le; trivial.
  apply Rpow_le1; lra.
Qed.

(****************)
(* Square Roots *)
(****************)

Lemma pow2_sqrt : forall x:R, 0 <= x -> (√ x) ^ 2 = x.
Proof. intros; simpl; rewrite Rmult_1_r, sqrt_def; auto. Qed.

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

Lemma sqrt2_div2 : (√ 2 / 2)%R = (1 / √ 2)%R.
Proof.
   field_simplify_eq; try (apply sqrt_neq_0_compat; lra).
   rewrite pow2_sqrt2; easy.
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

(* Trigonometry *)

Lemma sin_upper_bound_aux : forall x : R, 0 < x < 1 -> sin x <= x.
Proof.
  intros x H.
  specialize (SIN_bound x) as B.
    destruct (SIN x) as [_ B2]; try lra.
    specialize PI2_1 as PI1. lra.
    unfold sin_ub, sin_approx in *.
    simpl in B2.
    unfold sin_term at 1 in B2.
    simpl in B2.
    unfold Rdiv in B2.
    rewrite Rinv_1, Rmult_1_l, !Rmult_1_r in B2.
    (* Now just need to show that the other terms are negative... *)
    assert (sin_term x 1 + sin_term x 2 + sin_term x 3 + sin_term x 4 <= 0); try lra.
    unfold sin_term.
    remember (INR (fact (2 * 1 + 1))) as d1.
    remember (INR (fact (2 * 2 + 1))) as d2.
    remember (INR (fact (2 * 3 + 1))) as d3.
    remember (INR (fact (2 * 4 + 1))) as d4.
    assert (0 < d1) as L0.
    { subst. apply lt_0_INR. apply lt_O_fact. }
    assert (d1 <= d2) as L1.
    { subst. apply le_INR. apply fact_le. simpl; lia. }
    assert (d2 <= d3) as L2.
    { subst. apply le_INR. apply fact_le. simpl; lia. }
    assert (d3 <= d4) as L3.
    { subst. apply le_INR. apply fact_le. simpl; lia. }
    simpl.    
    ring_simplify.
    assert ( - (x * (x * (x * 1)) / d1) + x * (x * (x * (x * (x * 1)))) / d2 <= 0).
    rewrite Rplus_comm.
    apply Rle_minus.
    field_simplify; try lra.
    assert (x ^ 5 <= x ^ 3).
    { apply Rle_pow_le1; try lra; try lia. }
    apply Rmult_le_compat; try lra.
    apply pow_le; lra.
    left. apply Rinv_0_lt_compat. lra.
    apply Rinv_le_contravar; lra.
    unfold Rminus.
    assert (- (x * (x * (x * (x * (x * (x * (x * 1)))))) / d3) +
            x * (x * (x * (x * (x * (x * (x * (x * (x * 1)))))))) / d4 <= 0).
    rewrite Rplus_comm.
    apply Rle_minus.
    field_simplify; try lra.
    assert (x ^ 9 <= x ^ 7).
    { apply Rle_pow_le1; try lra; try lia. }
    apply Rmult_le_compat; try lra.
    apply pow_le; lra.
    left. apply Rinv_0_lt_compat. lra.
    apply Rinv_le_contravar; lra.
    lra.
Qed.

Lemma sin_upper_bound : forall x : R, Rabs (sin x) <= Rabs x.
Proof.
  intros x.  
  specialize (SIN_bound x) as B.
  destruct (Rlt_or_le (Rabs x) 1).
  (* abs(x) > 1 *)
  2:{ apply Rabs_le in B. lra. }
  destruct (Rtotal_order x 0) as [G | [E| L]].
  - (* x < 0 *)
    rewrite (Rabs_left x) in * by lra.
    rewrite (Rabs_left (sin x)).
    2:{ apply sin_lt_0_var; try lra.
        specialize PI2_1 as PI1.
        lra. }
    rewrite <- sin_neg.
    apply sin_upper_bound_aux.
    lra.
  - (* x = 0 *)
    subst. rewrite sin_0. lra.
  - rewrite (Rabs_right x) in * by lra.
    rewrite (Rabs_right (sin x)).
    2:{ apply Rle_ge.
        apply sin_ge_0; try lra.
        specialize PI2_1 as PI1. lra. }
    apply sin_upper_bound_aux; lra.
Qed.    


Hint Rewrite sin_0 sin_PI4 sin_PI2 sin_PI cos_0 cos_PI4 cos_PI2 cos_PI sin_neg cos_neg : trig_db.
