Require Export Bool.
Require Export Arith.
Require Export Reals.
Require Export Psatz.
Require Export Omega.
Require Export Program.
Require Export List.
Require Export Psatz.

Export ListNotations.


(* A bit of useful reflection from Software Foundations Vol 3 *)

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.  apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

