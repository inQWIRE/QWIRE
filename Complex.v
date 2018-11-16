(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.

---------------------------------------------------------------

This version modified to work without SSReflect,
or any other dependencies, as part of the QWIRE project
by Robert Rand and Jennifer Paykin (June 2017).

*)

Require Import Prelim.
Open Scope R_scope.


(******************************************)
(** Relevant lemmas from Rcomplements.v. **)
(******************************************)

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
             




(*********************)
(** Complex Numbers **)
(*********************)

(** This file defines complex numbers [C] as [R * R]. Operations are
given, and [C] is proved to be a field, a normed module, and a
complete space. *)

(** * The set of complex numbers *)

Definition C := (R * R)%type.

Definition RtoC (x : R) : C := (x,0).
Coercion RtoC : R >-> C.

Lemma RtoC_inj : forall (x y : R),
  RtoC x = RtoC y -> x = y.
Proof.
  intros x y H.
  now apply (f_equal (@fst R R)) in H.
Qed.

Lemma Ceq_dec (z1 z2 : C) : { z1 = z2 } + { z1 <> z2 }.
Proof.
  destruct z1 as [x1 y1].
  destruct z2 as [x2 y2].
  destruct (Req_EM_T x1 x2) as [Eqx | Neqx]; [| right; congruence].
  destruct (Req_EM_T y1 y2) as [Eqy | Neqy]; [subst; auto | right; congruence].
Qed.

(** ** Constants and usual functions *)

(** 0 and 1 for complex are defined as [RtoC 0] and [RtoC 1] *)
Definition Ci : C := (0,1).

(** *** Arithmetic operations *)

Definition Cplus (x y : C) : C := (fst x + fst y, snd x + snd y).
Definition Copp (x : C) : C := (-fst x, -snd x).
Definition Cminus (x y : C) : C := Cplus x (Copp y).
Definition Cmult (x y : C) : C := (fst x * fst y - snd x * snd y, fst x * snd y + snd x * fst y).
Definition Cinv (x : C) : C := (fst x / (fst x ^ 2 + snd x ^ 2), - snd x / (fst x ^ 2 + snd x ^ 2)).
Definition Cdiv (x y : C) : C := Cmult x (Cinv y).


Delimit Scope C_scope with C.
Local Open Scope C_scope.

Infix "+" := Cplus : C_scope.
Notation "- x" := (Copp x) : C_scope.
Infix "-" := Cminus : C_scope.
Infix "*" := Cmult : C_scope.
Notation "/ x" := (Cinv x) : C_scope.
Infix "/" := Cdiv : C_scope.


(* Added exponentiation *)
Fixpoint Cpow (c : C) (n : nat) : C :=  
  match n with
  | 0%nat => 1
  | S n' => c * Cpow c n'
  end.

Infix "^" := Cpow : C_scope.

(** *** Other usual functions *)

Definition Re (z : C) : R := fst z.

Definition Im (z : C) : R := snd z.

Definition Cmod (x : C) : R := sqrt (fst x ^ 2 + snd x ^ 2).

Definition Cconj (x : C) : C := (fst x, (- snd x)%R).

Notation "a ^*" := (Cconj a) (at level 10).


Lemma Cmod_0 : Cmod 0 = R0.
Proof.
unfold Cmod.
simpl.
rewrite Rmult_0_l, Rplus_0_l.
apply sqrt_0.
Qed.
Lemma Cmod_1 : Cmod 1 = R1.
Proof.
unfold Cmod.
simpl.
rewrite Rmult_0_l, Rplus_0_r, 2!Rmult_1_l.
apply sqrt_1.
Qed.

Lemma Cmod_opp : forall x, Cmod (-x) = Cmod x.
Proof.
unfold Cmod.
simpl.
intros x.
apply f_equal.
ring.
Qed.

Lemma Cmod_triangle : forall x y, Cmod (x + y) <= Cmod x + Cmod y.
Proof.
  intros x y ; unfold Cmod.
  apply Rsqr_incr_0_var.
  apply Rminus_le_0.
  unfold Rsqr ; simpl ; ring_simplify.
  unfold pow. 
  rewrite ?Rmult_1_r.
  rewrite ?sqrt_sqrt ; ring_simplify.
  replace (-2 * fst x * fst y - 2 * snd x * snd y)%R with (- (2 * (fst x * fst y + snd x * snd y)))%R by ring.
  rewrite Rmult_assoc, <- sqrt_mult.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rmult_le_compat_l.
  apply Rlt_le, Rlt_0_2.
  apply Rsqr_incr_0_var.
  apply Rminus_le_0.
  unfold Rsqr; rewrite ?sqrt_sqrt ; ring_simplify.
  replace (fst x ^ 2 * snd y ^ 2 - 2 * fst x * snd x * fst y * snd y +
    snd x ^ 2 * fst y ^ 2)%R with ( (fst x * snd y - snd x * fst y)^2)%R
    by ring.
  apply pow2_ge_0.
  repeat apply Rplus_le_le_0_compat ; apply Rmult_le_pos ; apply pow2_ge_0.
  apply sqrt_pos.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  replace (fst x ^ 2 + 2 * fst x * fst y + fst y ^ 2 + snd x ^ 2 + 2 * snd x * snd y + snd y ^ 2)%R
    with ((fst x + fst y)^2 + (snd x + snd y)^2)%R by ring.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply sqrt_pos.
Qed.

Lemma Cmod_mult : forall x y, Cmod (x * y) = (Cmod x * Cmod y)%R.
Proof.
  intros x y.
  unfold Cmod.
  rewrite <- sqrt_mult.
  apply f_equal ; simpl ; ring.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
Qed.

Lemma Rmax_Cmod : forall x,
  Rmax (Rabs (fst x)) (Rabs (snd x)) <= Cmod x.
Proof.
  intros [x y]; simpl.
  rewrite <- !sqrt_Rsqr_abs.
  apply Rmax_case ; apply sqrt_le_1_alt, Rminus_le_0 ;
  unfold Rsqr; simpl ; ring_simplify ; try apply pow2_ge_0; auto.
Qed.
Lemma Cmod_2Rmax : forall x,
  Cmod x <= sqrt 2 * Rmax (Rabs (fst x)) (Rabs (snd x)).
Proof.
  intros [x y]; apply Rmax_case_strong; intros H0;
  rewrite <- !sqrt_Rsqr_abs ;
  rewrite <- ?sqrt_mult ;
  try (apply Rle_0_sqr; auto);
  try (apply Rlt_le, Rlt_0_2; auto) ;
  apply sqrt_le_1_alt ; simpl ; [ rewrite Rplus_comm | ] ;
  unfold Rsqr ; apply Rle_minus_r ; ring_simplify ;
  apply Rsqr_le_abs_1 in H0 ; unfold pow; rewrite !Rmult_1_r; auto.
Qed.

(** ** C is a field *)

Lemma RtoC_plus (x y : R) : RtoC (x + y) = RtoC x + RtoC y.
Proof.
  unfold RtoC, Cplus ; simpl.
  rewrite Rplus_0_r; auto.
Qed.

Lemma RtoC_opp (x : R) : RtoC (- x) = - RtoC x.
Proof.
  unfold RtoC, Copp ; simpl.
  rewrite Ropp_0; auto.
Qed.

Lemma RtoC_minus (x y : R) : RtoC (x - y) = RtoC x - RtoC y.
Proof. unfold Cminus; rewrite <- RtoC_opp, <- RtoC_plus; auto. Qed.

Lemma RtoC_mult (x y : R) : RtoC (x * y) = RtoC x * RtoC y.
Proof.
  unfold RtoC, Cmult ; simpl.
  apply injective_projections ; simpl ; ring.
Qed.

Lemma RtoC_inv (x : R) : (x <> 0)%R -> RtoC (/ x) = / RtoC x.
Proof. intros Hx. apply injective_projections ; simpl ; field ; auto. Qed.

Lemma RtoC_div (x y : R) : (y <> 0)%R -> RtoC (x / y) = RtoC x / RtoC y.
Proof. intros Hy. apply injective_projections ; simpl ; field ; auto. Qed.


Lemma Cplus_comm (x y : C) : x + y = y + x.
Proof. apply injective_projections ; simpl ; apply Rplus_comm. Qed.

Lemma Cplus_assoc (x y z : C) : x + (y + z) = (x + y) + z.
Proof. apply injective_projections ; simpl ; apply sym_eq, Rplus_assoc. Qed.

Lemma Cplus_0_r (x : C) : x + 0 = x.
Proof. apply injective_projections ; simpl ; apply Rplus_0_r. Qed.

Lemma Cplus_0_l (x : C) : 0 + x = x.
Proof. apply injective_projections ; simpl ; apply Rplus_0_l. Qed.

Lemma Cplus_opp_r (x : C) : x + -x = 0.
Proof. apply injective_projections ; simpl ; apply Rplus_opp_r. Qed.

Lemma Copp_plus_distr (z1 z2 : C) : - (z1 + z2) = (- z1 + - z2).
Proof. apply injective_projections ; apply Ropp_plus_distr; auto. Qed.

Lemma Copp_minus_distr (z1 z2 : C) : - (z1 - z2) = z2 - z1.
Proof. apply injective_projections ; apply Ropp_minus_distr; auto. Qed.

Lemma Cmult_comm (x y : C) : x * y = y * x.
Proof. apply injective_projections ; simpl ; ring. Qed.

Lemma Cmult_assoc (x y z : C) : x * (y * z) = (x * y) * z.
Proof. apply injective_projections ; simpl ; ring. Qed.

Lemma Cmult_0_r (x : C) : x * 0 = 0.
Proof. apply injective_projections ; simpl ; ring. Qed.

Lemma Cmult_0_l (x : C) : 0 * x = 0.
Proof. apply injective_projections ; simpl ; ring. Qed.

Lemma Cmult_1_r (x : C) : x * 1 = x.
Proof. apply injective_projections ; simpl ; ring. Qed.

Lemma Cmult_1_l (x : C) : 1 * x = x.
Proof. apply injective_projections ; simpl ; ring. Qed.

Lemma Cinv_r (r : C) : r <> 0 -> r * /r = 1.
Proof.
  intros H.
  apply injective_projections ; simpl ; field.
  contradict H.
  apply Rplus_sqr_eq_0 in H.
  apply injective_projections ; simpl ; apply H.
  contradict H.
  apply Rplus_sqr_eq_0 in H.
  apply injective_projections ; simpl ; apply H.
Qed.

Lemma Cinv_l (r : C) : r <> 0 -> /r * r = 1.
Proof.
intros Zr.
rewrite Cmult_comm.
now apply Cinv_r.
Qed.

Lemma Cmult_plus_distr_l (x y z : C) : x * (y + z) = x * y + x * z.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.

Lemma Cmult_plus_distr_r (x y z : C) : (x + y) * z = x * z + y * z.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.

(* I'll be leaving out mixins and Canonical Structures :
Definition C_AbelianGroup_mixin :=
  AbelianGroup.Mixin _ _ _ _ Cplus_comm Cplus_assoc Cplus_0_r Cplus_opp_r.

Canonical C_AbelianGroup :=
  AbelianGroup.Pack C C_AbelianGroup_mixin C.
*)

Lemma Copp_0 : Copp 0 = 0.
Proof. apply injective_projections; simpl ; ring. Qed.

Lemma Cmod_m1 : Cmod (Copp 1) = 1.
Proof. rewrite Cmod_opp. apply Cmod_1. Qed.

Lemma Cmod_eq_0 : forall x, Cmod x = 0 -> x = 0.
Proof.
  intros x H.
  unfold Cmod, pow in H.
  rewrite 2!Rmult_1_r, <- sqrt_0 in H.
  apply sqrt_inj in H.
  apply Rplus_sqr_eq_0 in H.
  now apply injective_projections.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  apply Rle_refl.
Qed.

Lemma Cmod_ge_0 : forall x, 0 <= Cmod x.
Proof.
  intros x.
  apply sqrt_pos.
Qed.

Lemma Cmod_gt_0 :
  forall (x : C), x <> 0 <-> 0 < Cmod x.
Proof.
  intros x ; split; intro Hx.
  destruct (Cmod_ge_0 x); auto.
  apply sym_eq, Cmod_eq_0 in H. tauto.
  contradict Hx.
  apply Rle_not_lt, Req_le.
  rewrite Hx, Cmod_0; auto.
Qed.

Lemma Cmod_R : forall x : R, Cmod x = Rabs x.
Proof.
  intros x.
  unfold Cmod.
  simpl.
  rewrite Rmult_0_l, Rplus_0_r, Rmult_1_r.
  apply sqrt_Rsqr_abs.
Qed.

Lemma Cmod_inv : forall x : C, x <> 0 -> Cmod (/ x) = Rinv (Cmod x).
Proof.
  intros x Zx.
  apply Rmult_eq_reg_l with (Cmod x).
  rewrite <- Cmod_mult.
  rewrite Rinv_r.
  rewrite Cinv_r.
  rewrite Cmod_R.
  apply Rabs_R1.
  exact Zx.
  contradict Zx.
  now apply Cmod_eq_0.
  contradict Zx.
  now apply Cmod_eq_0.
Qed.

Lemma Cmod_div (x y : C) : y <> 0 -> Cmod (x / y) = Rdiv (Cmod x) (Cmod y).
Proof.
  intro Hy.
  unfold Cdiv.
  rewrite Cmod_mult.
  rewrite Cmod_inv; auto.
Qed.

Lemma Cmult_neq_0 (z1 z2 : C) : z1 <> 0 -> z2 <> 0 -> z1 * z2 <> 0.
Proof.
  intros Hz1 Hz2 Hz.
  assert (Cmod (z1 * z2) = 0).
  rewrite Hz, Cmod_0; auto.
  rewrite Cmod_mult in H.
  apply Rmult_integral in H ; destruct H.
  now apply Hz1, Cmod_eq_0.
  now apply Hz2, Cmod_eq_0.
Qed.

Lemma Cminus_eq_contra : forall r1 r2 : C, r1 <> r2 -> r1 - r2 <> 0.
Proof.
  intros ; contradict H ; apply injective_projections ;
  apply Rminus_diag_uniq.
  now apply (f_equal (@fst R R)) in H.
  now apply (f_equal (@snd R R)) in H.
Qed.

Lemma C_field_theory : field_theory (RtoC 0) (RtoC 1) Cplus Cmult Cminus Copp Cdiv Cinv eq.
Proof.
constructor.
constructor.
exact Cplus_0_l.
exact Cplus_comm.
exact Cplus_assoc.
exact Cmult_1_l.
exact Cmult_comm.
exact Cmult_assoc.
exact Cmult_plus_distr_r.
easy.
exact Cplus_opp_r.
intros H.
injection H.
exact R1_neq_R0.
easy.
apply Cinv_l.
Qed.

Add Field C_field_field : C_field_theory.

(** Added Lemmas for QWIRE *)

(** Notations *)

Notation C0 := (RtoC 0). 
Notation C1 := (RtoC 1).
Notation C2 := (RtoC 2).
Notation "√ n" := (sqrt n) (at level 20).

Lemma RtoC_pow : forall r n, (RtoC r) ^ n = RtoC (r ^ n).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite RtoC_mult.
    reflexivity.
Qed.

Lemma c_proj_eq : forall (c1 c2 : C), fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.  
Proof. intros c1 c2 H1 H2. destruct c1, c2. simpl in *. subst. reflexivity. Qed.

Ltac clra := eapply c_proj_eq; simpl; lra.

Lemma Copp_mult_distr_r : forall c1 c2 : C, - (c1 * c2) = c1 * - c2.
Proof. intros; clra. Qed.
Lemma Copp_mult_distr_l : forall c1 c2 : C, - (c1 * c2) = - c1 * c2.
Proof. intros; clra. Qed.
Lemma Cplus_opp_l : forall c : C, - c + c = 0. Proof. intros; clra. Qed.
Lemma Cdouble : forall c : C, 2 * c = c + c. Proof. intros; clra. Qed.
Lemma Copp_involutive: forall c : C, - - c = c. Proof. intros; clra. Qed.

Lemma C0_imp : forall c : C, c <> 0 -> (fst c <> 0 \/ snd c <> 0)%R.  
Proof. intros c H. destruct c. simpl.
       destruct (Req_EM_T r 0), (Req_EM_T r0 0); subst; intuition. Qed.
Lemma C0_fst : forall (c : C), fst c <> 0 -> c <> 0. 
Proof. intros c. intros N E. apply N. rewrite E. reflexivity. Qed.
Lemma C0_snd : forall (c : C), snd c <> 0 -> c <> 0. 
Proof. intros c. intros N E. apply N. rewrite E. reflexivity. Qed.

Lemma Rmult_div : forall r1 r2 r3 r4 : R, r2 <> 0 -> r4 <> 0 -> 
                                     (r1 / r2 * (r3 / r4) = r1 * r3 / (r2 * r4))%R. 
Proof. intros. unfold Rdiv. rewrite Rinv_mult_distr; trivial. lra. Qed.

Lemma Rdiv_cancel :  forall r r1 r2 : R, (r1 = r2 -> r / r1 = r / r2)%R.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Rsum_nonzero : forall r1 r2 : R, (r1 <> 0 \/ r2 <> 0 -> r1 * r1 + r2 * r2 <> 0)%R. 
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

Lemma Cinv_mult_distr : forall c1 c2 : C, c1 <> 0 -> c2 <> 0 -> / (c1 * c2) = / c1 * / c2.
Proof.
  intros.
  apply c_proj_eq.
  - simpl.
    repeat rewrite Rmult_1_r.
    rewrite Rmult_div.
    rewrite Rmult_div.
    rewrite Rmult_opp_opp.
    unfold Rminus.
    rewrite <- RIneq.Ropp_div.
    rewrite <- Rdiv_plus_distr.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_plus_distr_l.
    apply Rdiv_cancel.
    lra.
    * apply Rsum_nonzero. apply C0_imp in H. assumption.
    * apply Rsum_nonzero. apply C0_imp in H0. assumption.
    * apply Rsum_nonzero. apply C0_imp in H. assumption.
    * apply Rsum_nonzero. apply C0_imp in H0. assumption.
  - simpl.    
    repeat rewrite Rmult_1_r.
    rewrite Rmult_div.
    rewrite Rmult_div.
    unfold Rminus.
    rewrite <- Rdiv_plus_distr.
    repeat rewrite Rmult_plus_distr_r.
    repeat rewrite Rmult_plus_distr_l.
    repeat rewrite <- Ropp_mult_distr_r.
    repeat rewrite <- Ropp_mult_distr_l.
    repeat rewrite <- Ropp_plus_distr.
    apply Rdiv_cancel.
    lra.
    * apply Rsum_nonzero. apply C0_imp in H. assumption.
    * apply Rsum_nonzero. apply C0_imp in H0. assumption.
    * apply Rsum_nonzero. apply C0_imp in H. assumption.
    * apply Rsum_nonzero. apply C0_imp in H0. assumption.
Qed.

Lemma Csqrt_sqrt : forall x : R, 0 <= x -> ((RtoC (√ x)) * (RtoC (√ x)) = (RtoC x))%C.
Proof. intros. eapply c_proj_eq; simpl; try rewrite sqrt_sqrt; lra. Qed.

(* Lemmas about Conjugates *)

Lemma Cconj_R : forall r : R, r^* = r.         Proof. intros; clra. Qed.
Lemma Cconj_0 : 0^* = 0.                  Proof. clra. Qed.
Lemma Cconj_opp : forall C, (- C)^* = - (C^*). Proof. reflexivity. Qed.
Lemma Cconj_rad2 : (/ √2)^* = / √2.       Proof. clra. Qed.
Lemma Cplus_div2 : /2 + /2 = 1.           Proof. clra. Qed.
Lemma Cconj_involutive : forall c, (c^*)^* = c. Proof. intros; clra. Qed.
Lemma Cconj_plus_distr : forall (x y : C), (x + y)^* = x^* + y^*. Proof. intros; clra. Qed.
Lemma Cconj_mult_distr : forall (x y : C), (x * y)^* = x^* * y^*. Proof. intros; clra. Qed.

Lemma Cmult_conj_real : forall (c : C), snd (c * c^*) = 0.
Proof.
  intros c.
  unfold Cconj.
  unfold Cmult.
  simpl.
  rewrite <- Ropp_mult_distr_r.
  rewrite Rmult_comm.
  rewrite Rplus_opp_l.
  reflexivity.
Qed.  
  

Lemma square_rad2 : /√2 * /√2 = /2. 
Proof. 
  eapply c_proj_eq; simpl; try lra.
  autorewrite with R_db. 
  rewrite Rmult_assoc.
  rewrite (Rmult_comm (/2) _).
  repeat rewrite <- Rmult_assoc.
  rewrite sqrt_def; lra.
Qed.

Lemma Cpow_nonzero : forall (r : R) (n : nat), (r <> 0 -> r ^ n <> C0)%C. 
Proof.
  intros.
  rewrite RtoC_pow. 
  apply C0_fst. 
  apply pow_nonzero. 
  lra.
Qed.

(* e^(iθ) *)
Definition Cexp (θ : R) : C := (cos θ, sin θ).

Lemma eulers_identity : Cexp PI = -1.
Proof. unfold Cexp. rewrite cos_PI, sin_PI. easy. Qed.

Lemma eulers_identity2 : Cexp (PI/2) = Ci.
Proof. unfold Cexp. rewrite cos_PI2, sin_PI2. easy. Qed.


(*
Definition Cexp' (θ : R) : C := cos θ + Ci * (sin θ).
Lemma Cexp_eq : forall θ, Cexp θ = Cexp' θ. Proof. intros. clra. Qed.
*)

(**************)
(* Automation *)
(**************)

Lemma Cminus_unfold : forall c1 c2, (c1 - c2 = c1 + -c2)%C. Proof. reflexivity. Qed.
Lemma Cdiv_unfold : forall c1 c2, (c1 / c2 = c1 */ c2)%C. Proof. reflexivity. Qed.

(* Intentionally very limited tactic. Could have it call Cpow_nonzero 
   and similar lemmas if we wanted to make it stronger *)
Ltac nonzero := apply C0_fst; specialize Rlt_sqrt2_0; intros; simpl; Psatz.lra.

Hint Rewrite Cminus_unfold Cdiv_unfold Cconj_R Cconj_opp Cconj_rad2 
     square_rad2 Cplus_div2
     Cplus_0_l Cplus_0_r Cplus_opp_r Cplus_opp_l Copp_0  Copp_involutive
     Cmult_0_l Cmult_0_r Cmult_1_l Cmult_1_r : C_db.

Hint Rewrite <- Copp_mult_distr_l Copp_mult_distr_r Cdouble : C_db.
Hint Rewrite Csqrt_sqrt using Psatz.lra : C_db.
Hint Rewrite Cinv_l Cinv_r using nonzero : C_db.
(* Previously in the other direction *)
Hint Rewrite Cinv_mult_distr using nonzero : C_db.

(* Light rewriting db *)
Hint Rewrite Cplus_0_l Cplus_0_r Cmult_0_l Cmult_0_r Copp_0 
             Cconj_R Cmult_1_l Cmult_1_r : C_db_light.

(* Distributing db *)
Hint Rewrite Cmult_plus_distr_l Cmult_plus_distr_r Copp_plus_distr Copp_mult_distr_l Copp_involutive : Cdist_db.


Ltac Csimpl := 
  repeat match goal with
  | _ => rewrite Cmult_0_l
  | _ => rewrite Cmult_0_r
  | _ => rewrite Cplus_0_l
  | _ => rewrite Cplus_0_r
  | _ => rewrite Cmult_1_l
  | _ => rewrite Cmult_1_r
  | _ => rewrite Cconj_R
  end.

(* We might want these back at some point
Ltac Rsimpl := 
  simpl;
  unfold Rminus;
  unfold Rdiv;
  repeat (
    try rewrite Ropp_0;
    try rewrite Ropp_involutive;
    try rewrite Rplus_0_l;
    try rewrite Rplus_0_r;
    try rewrite Rmult_0_l;
    try rewrite Rmult_0_r;
    try rewrite Rmult_1_l;
    try rewrite Rmult_1_r;
    try rewrite <- Ropp_mult_distr_l;
    try rewrite <- Ropp_mult_distr_r;
    try (rewrite Rinv_l; [|lra]);
    try (rewrite Rinv_r; [|lra]);
    try (rewrite sqrt_sqrt; [|lra])).

Ltac Rsolve := repeat (Rsimpl; try group_radicals); lra.

Ltac Csolve := eapply c_proj_eq; simpl; Rsolve.
*)


(* Seems like this could loop forever *)
Ltac group_radicals := 
  repeat (
  match goal with
    | [ |- context[(?r1 * √ ?r2)%R] ] => rewrite (Rmult_comm r1 (√r2)) 
    | [ |- context[(?r1 * (√ ?r2 * ?r3))%R] ] => rewrite <- (Rmult_assoc _ (√ r2) _)
    | [ |- context[((√?r * ?r1) + (√?r * ?r2))%R ] ] => 
        rewrite <- (Rmult_plus_distr_l r r1 r2)
  end).


