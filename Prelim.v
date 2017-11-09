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


(* Lists *)


(* Precondition: x must appear in li *)
Fixpoint lookup (x : nat) (li : list nat) : nat :=
  match li with
  | nil => 0
  | y :: ys => if x =? y then 0 else S (lookup x ys)
  end.

(*
Fixpoint index {A} (i : nat) (li : list A) : option A :=
  match i, li with
  | _, nil => None
  | 0, x :: _ => Some x
  | S i', _ :: li' => index i' li'
  end.
*)
Notation "l !! i" := (nth_error l i) (at level 20).

Fixpoint remove_at {A} (i : nat) (ls : list A) :=
  match i, ls with
  | _   ,[]        => []
  | 0   , _ :: ls' => ls'
  | S i', a :: ls' => a :: remove_at i' ls'
  end.

Fixpoint update_at {A} (ls : list A) (i : nat) (a : A) : list A :=
  match ls, i with
  | []      , _    => []
  | _ :: ls', 0    => a :: ls'
  | b :: ls', S i' => b :: update_at ls' i' a
  end.



Fixpoint Injective {A} (ls : list A) :=
  match ls with
  | [] => True
  | x :: ls' => ~ In x ls' /\ Injective ls'
  end.
  
Lemma nth_nil : forall {A} x, ([] : list A) !! x = None.
Proof.
  destruct x; auto.
Qed.

(* option type *)


Definition maybe {A} (o : option A) (default : A) : A :=
  match o with
  | Some a => a
  | None => default
  end.
