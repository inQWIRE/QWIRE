Require Import HOASLib.
Require Import Denotation.
Require Import TypeChecking.

Open Scope matrix_scope.

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

Lemma X_spec : forall (b : bool), ⟦boxed_gate X⟧ (bool_to_matrix b) = bool_to_matrix (¬ b).
Proof. ket_denote. destruct b; unfold bool_to_ket; simpl; Msimpl; easy. Qed.

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
