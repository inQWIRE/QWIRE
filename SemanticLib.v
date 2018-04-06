Require Import HOASLib.
Require Import Denotation.
Require Import TypeChecking.

Open Scope matrix_scope.

(* ---------------------------------------*)
(*--------- Boxed Circuit Specs ----------*)
(* ---------------------------------------*)


Lemma X_spec : forall (b : bool), ⟦boxed_gate X⟧ (bool_to_matrix b) = bool_to_matrix (¬ b).
Proof. ket_denote. destruct b; unfold bool_to_ket; simpl; Msimpl; easy. Qed.

Lemma init0_spec : ⟦boxed_gate init0⟧ (Id (2^0)) = |0⟩⟨0|.
Proof. matrix_denote. Msimpl. reflexivity. Qed.

Lemma init1_spec : ⟦boxed_gate init1⟧ (Id (2^0)) = |1⟩⟨1|.
Proof. matrix_denote. Msimpl. reflexivity. Qed.

Lemma assert0_spec : ⟦boxed_gate assert0⟧ |0⟩⟨0| = Id 1. 
Proof.  
  matrix_denote.
  Msimpl.
  solve_matrix.
  bdestruct (S (S x) <? 1). omega.
  rewrite andb_false_r.
  reflexivity.
Qed.

Lemma assert1_spec : ⟦boxed_gate assert1⟧ |1⟩⟨1| = Id 1. 
Proof.  
  matrix_denote.
  Msimpl.
  solve_matrix.
  bdestruct (S (S x) <? 1). omega.
  rewrite andb_false_r.
  reflexivity.
Qed.

Lemma init_spec : forall b, ⟦init b⟧ (Id (2^0)) = bool_to_matrix b.
Proof. destruct b; [apply init1_spec | apply init0_spec]. Qed.

Lemma assert_spec : forall b, ⟦assert b⟧ (bool_to_matrix b) = Id 1.
Proof. destruct b; [apply assert1_spec | apply assert0_spec]. Qed.


(* -----------------------------------------*)
(*--------- Reversible Circuit Specs -------*)
(* -----------------------------------------*)

(* The form of these is off.
Lemma X_spec : forall b, super σx (bool_to_matrix b) = bool_to_matrix (negb b).
Proof. ket_denote. destruct b; solve_matrix. Qed.

Lemma CNOT_spec : forall b1 b2, super (control σx) (bool_to_matrix b1 ⊗ bool_to_matrix b2)
                           = (bool_to_matrix b1 ⊗ bool_to_matrix (xorb b1 b2)).
Proof. 
  ket_denote. destruct b1, b2; unfold bool_to_ket; simpl; Msimpl; solve_matrix.
Qed.
*)

Lemma CNOT_spec : forall b1 b2, 
  ⟦boxed_gate CNOT⟧ (bool_to_matrix b1 ⊗ bool_to_matrix b2)
                           = (bool_to_matrix b1 ⊗ bool_to_matrix (b1 ⊕ b2)).
Proof. 
  ket_denote. destruct b1, b2; unfold bool_to_ket; simpl; Msimpl; solve_matrix.
Qed.

Lemma TRUE_spec : forall z, ⟦TRUE⟧ (bool_to_matrix z) = bool_to_matrix (true ⊕ z). 
Proof. ket_denote. destruct z; unfold bool_to_ket; simpl; Msimpl; reflexivity. Qed.

Lemma FALSE_spec : forall z, ⟦FALSE⟧ (bool_to_matrix z) = bool_to_matrix (false ⊕ z). 
Proof. ket_denote. destruct z; unfold bool_to_ket; simpl; Msimpl; reflexivity. Qed.

Lemma NOT_spec : forall (x z : bool), 
  ⟦NOT⟧ (bool_to_matrix x ⊗ bool_to_matrix z) = 
  bool_to_matrix x ⊗ bool_to_matrix ((¬ x) ⊕ z).
Proof.
  ket_denote. 
  destruct x, z; unfold bool_to_ket; simpl; Msimpl; solve_matrix. 
Qed.

Lemma XOR_spec : forall (x y z : bool), 
    ⟦XOR⟧ (bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix z)  = 
    bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix (x ⊕ y ⊕ z).
Proof.  
  ket_denote. Msimpl.
  destruct x, y, z; unfold bool_to_ket; simpl; Msimpl; solve_matrix. 
Qed.

Lemma AND_spec : forall (x y z : bool), 
    ⟦AND⟧ (bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix z)  = 
    bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix ((x && y) ⊕ z).
Proof. 
  ket_denote. Msimpl.
  destruct x, y, z; unfold bool_to_ket; simpl; Msimpl; solve_matrix. 
Qed.
