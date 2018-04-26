Require Import Datatypes.
Require Export TypeChecking.
Import ListNotations.
Open Scope list_scope.
Open Scope circ_scope.

Definition apply_box {w1 w2} (b : Box w1 w2) (c : Circuit w1) : Circuit w2 :=
  let_ x ← c;
  unbox b x.
Notation "b $ c" := (apply_box b c)  (right associativity, at level 10) : circ_scope.
Coercion output : Pat >-> Circuit.
 
Definition id_circ {W} : Box W W :=
  box_ p ⇒ (output p).
Lemma id_circ_WT : forall W, Typed_Box (@id_circ W).
Proof. type_check. Qed.

Definition boxed_gate {W1 W2} (g : Gate W1 W2) : Box W1 W2 := 
  box_ p ⇒ 
    gate_ p2 ← g @ p;
    output p2.
Coercion boxed_gate : Gate >-> Box.

Lemma boxed_gate_WT {W1 W2} (g : Gate W1 W2) : Typed_Box (boxed_gate g).
Proof. type_check. Qed.

(***********************)
(* Structural circuits *)
(***********************)

Definition init (b : bool) : Box One Qubit :=
  if b then init1 else init0.
Lemma init_WT : forall b, Typed_Box (init b).
Proof. destruct b; type_check. Defined.

Definition inSeq {w1 w2 w3} (c1 : Box w1 w2) (c2 : Box w2 w3): Box w1 w3 :=
  box_ p1 ⇒ 
    let_ p2 ← unbox c1 p1;
    unbox c2 p2.
Notation "b ;; b'" := (inSeq b b') (right associativity, at level 9) : circ_scope.
Notation "b' · b" := (inSeq b b') (right associativity, at level 9) : circ_scope.
Lemma inSeq_WT : forall W1 W2 W3 (c1 : Box W1 W2) (c2 : Box W2 W3), 
                 Typed_Box c1 -> Typed_Box c2 -> Typed_Box (c2 · c1).
Proof. type_check. Qed.

Definition inPar {w1 w2 w1' w2'} 
                 (c1 : Box w1 w2) (c2 : Box w1' w2') : Box (w1 ⊗ w1') (w2 ⊗ w2'):=
  box_ p12 ⇒ 
    let_ (p1,p2) ← output p12; 
    let_ p1'     ← unbox c1 p1;
    let_ p2'     ← unbox c2 p2; 
    output (p1',p2').
Notation "b1 || b2" := (inPar b1 b2).
Lemma inPar_WT : forall W1 W1' W2 W2' (c1 : Box W1 W2) (c2 : Box W1' W2'), 
  Typed_Box c1 -> Typed_Box c2 ->
  Typed_Box (c1 || c2).
Proof. type_check. Qed.

Fixpoint units (n : nat) : Pat (n ⨂ One) := 
  match n with
  | O => unit
  | S n' => (unit, units n')
  end. 
Lemma types_units : forall n, Types_Pat ∅ (units n).
Proof. induction n; type_check. Qed.
Notation "(())" := (units _) (at level 8).

(* Can also just use (init b) #n $ (()) *)
Fixpoint initMany (b : bool) (n : nat) : Box One (n ⨂ Qubit):= 
  match n with 
  | 0    => id_circ
  | S n' => box_ () ⇒ 
           let_ q  ← unbox (init b) ();
           let_ qs ← unbox (initMany b n') ();
           output (q, qs)
  end.
Lemma initMany_WT : forall b n, Typed_Box (initMany b n).
Proof. induction n; type_check. Qed.

Fixpoint inSeqMany (n : nat) {W} (c : Box W W) : Box W W:= 
  match n with
  | 0 => id_circ
  | S n' => inSeq c (inSeqMany n' c)
  end.
Lemma inSeqMany_WT : forall n W (c : Box W W), 
      Typed_Box c -> Typed_Box (inSeqMany n c).
Proof. intros. induction n as [ | n']; type_check. Qed.

Fixpoint inParMany (n : nat) {W W'} (c : Box W W') : Box (n ⨂ W) (n ⨂ W') := 
  match n with 
  | 0    => id_circ
  | S n' => inPar c (inParMany n' c)
  end.
Lemma inParMany_WT : forall n W W' (c : Box W W'), Typed_Box c  -> 
                                 Typed_Box (inParMany n c).
Proof. intros. induction n as [ | n']; type_check. Qed.       

Notation "g # n" := (inParMany n g) (at level 8).

Hint Resolve types_units id_circ_WT boxed_gate_WT init_WT inSeq_WT inPar_WT 
     initMany_WT inSeqMany_WT inParMany_WT : typed_db.

Close Scope circ_scope.