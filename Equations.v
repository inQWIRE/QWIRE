Require Import HOASCircuits.
Require Import Prelim.
Require Import Denotation.
Require Import TypeChecking.
Require Import HOASLib.
Require Import SemanticLib.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

(* Note: All of these circuits should in principle end with an arbitrary circuit -
         here I'm just outputting the mentioned (qu)bits *)

Open Scope circ_scope.  

(** Equality 1: X; meas = meas; NOT **)

Definition X_meas : Box Qubit Bit := X ;; meas.
Lemma X_meas_WT : Typed_Box X_meas.
Proof. type_check. Qed.


Definition meas_NOT : Box Qubit Bit := meas ;; BNOT.

Lemma meas_NOT_WT : Typed_Box meas_NOT.
Proof. type_check. Qed.

Lemma NOT_meas_comm : X_meas ≡ meas_NOT.
Proof.
  matrix_denote.
  intros ρ b M.
  Msimpl.
  

  rewrite M; trivial; omega.
  rewrite C; trivial; omega.
Qed.  



(** Equation 7': meas q; lift x <- p; new x = meas q **)

Definition meas_lift_new : Box Qubit Bit :=
  box_ q ⇒ 
    let_ b ← meas $ q;
    lift_ x ← b; 
    new x $ ().
Lemma meas_lift_new_WT : Typed_Box meas_lift_new.
Proof. type_check. Qed.

Lemma meas_lift_new_new : meas_lift_new ≡ boxed_gate meas.
Proof. 
  intros ρ safe M.
  repeat (autounfold with den_db; intros; simpl).
  specialize (WF_Mixed _ M); intros WFρ.
  Msimpl.
  solve_matrix.
Qed.
  
