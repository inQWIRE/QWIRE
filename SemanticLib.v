Require Import HOASLib.
Require Import Denotation.
Require Import TypeChecking.
Require Import Ancilla.

Open Scope matrix_scope.

(* ---------------------------------------*)
(*--------- Utility Lemmata --------------*)
(* ---------------------------------------*)

(* It turns out, these generally aren't needed. *)
Lemma valid_denote_true : forall W W' (c : Box W W') 
  (ρ : Square (2^(⟦W⟧))) (ρ' : Square (2^(⟦W⟧))) (safe : bool), 
  (* typically ancilla_free_box c, but we'll make it general *)
  Typed_Box c ->
  valid_ancillae_box c ->
  denote_box true c ρ = ρ' ->
  denote_box safe c ρ = ρ'. 
Proof.
  intros W W' c ρ ρ' safe T H D.
  destruct safe; trivial.
  rewrite <- H; assumption.
Qed.  

Lemma valid_denote_false : forall W W' (c : Box W W') 
  (ρ : Square (2^(⟦W⟧))) (ρ' : Square (2^(⟦W⟧))) (safe : bool), 
  Typed_Box c ->
  valid_ancillae_box c ->
  denote_box false c ρ = ρ' ->
  denote_box safe c ρ = ρ'. 
Proof.
  intros W W' c ρ ρ' safe T H D.
  destruct safe; trivial.
  rewrite H; assumption.
Qed.  

Ltac case_safe := apply valid_denote_true; 
                  try solve [type_check; apply ancilla_free_box_valid; repeat constructor].
Ltac case_unsafe := apply valid_denote_false;
                    try solve [type_check; apply ancilla_free_box_valid; repeat constructor].

(* ---------------------------------------*)
(*--------- Boxed Circuit Specs ----------*)
(* ---------------------------------------*)

Lemma id_circ_spec : forall W ρ safe, WF_Matrix (2^⟦W⟧) (2^⟦W⟧) ρ -> 
  denote_box safe  (@id_circ W) ρ = ρ.
Proof.
  intros W ρ safe H.
  simpl. unfold denote_box. simpl.
  autorewrite with proof_db.
  unfold pad.
  rewrite Nat.sub_diag.
  rewrite kron_1_r.
  rewrite super_I; auto.
Qed.

Lemma X_spec : forall (b safe : bool), denote_box safe (boxed_gate _X) (bool_to_matrix b) = 
                               bool_to_matrix (¬ b).
Proof. intros. ket_denote. destruct b; unfold bool_to_ket; simpl; Msimpl; easy. Qed.

Lemma init0_spec : forall safe, denote_box safe init0 (Id (2^0)) = |0⟩⟨0|.
Proof. intros. matrix_denote. Msimpl. reflexivity. Qed.

Lemma init1_spec : forall safe, denote_box safe init1 (Id (2^0)) = |1⟩⟨1|.
Proof. intros. matrix_denote. Msimpl. reflexivity. Qed.

Lemma assert0_spec : forall safe, denote_box safe assert0 |0⟩⟨0| = Id 1. 
Proof.  
  destruct safe.
  - matrix_denote.
    Msimpl.
    solve_matrix.
  - matrix_denote.
    Msimpl.
    solve_matrix.
Qed.

Lemma assert1_spec : forall safe, denote_box safe assert1 |1⟩⟨1| = Id 1. 
Proof.  
  destruct safe.
  - matrix_denote.
    Msimpl.
    solve_matrix.
  - matrix_denote.
    Msimpl.
    solve_matrix.
Qed.

Lemma init_spec : forall b safe, denote_box safe (init b) (Id (2^0)) = bool_to_matrix b.
Proof. destruct b; [apply init1_spec | apply init0_spec]. Qed.

Lemma assert_spec : forall b safe, denote_box safe (assert b) (bool_to_matrix b) = Id 1.
Proof. destruct b; [apply assert1_spec | apply assert0_spec]. Qed.


(* -----------------------------------------*)
(*--------- Reversible Circuit Specs -------*)
(* -----------------------------------------*)

Lemma CNOT_spec : forall (b1 b2 safe : bool), 
  denote_box safe CNOT (bool_to_matrix b1 ⊗ bool_to_matrix b2)
  = (bool_to_matrix b1 ⊗ bool_to_matrix (b1 ⊕ b2)).
Proof.
  ket_denote. destruct b1, b2; unfold bool_to_ket; simpl; Msimpl; solve_matrix.
Qed.

Lemma TRUE_spec : forall z safe, 
  denote_box safe TRUE (bool_to_matrix z) = bool_to_matrix (true ⊕ z). 
Proof. ket_denote. destruct z; unfold bool_to_ket; simpl; Msimpl; reflexivity. Qed.

Lemma FALSE_spec : forall z safe, 
    denote_box safe FALSE (bool_to_matrix z) = bool_to_matrix (false ⊕ z). 
Proof. ket_denote. destruct z; unfold bool_to_ket; simpl; Msimpl; reflexivity. Qed.

Lemma NOT_spec : forall (x z : bool), 
  forall safe, denote_box safe NOT (bool_to_matrix x ⊗ bool_to_matrix z) = 
  bool_to_matrix x ⊗ bool_to_matrix ((¬ x) ⊕ z).
Proof.
  ket_denote. 
  destruct x, z; unfold bool_to_ket; simpl; Msimpl; solve_matrix. 
Qed.

Lemma XOR_spec : forall (x y z safe : bool), 
    denote_box safe XOR (bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix z)  = 
    bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix (x ⊕ y ⊕ z).
Proof.  
  ket_denote. Msimpl.
  destruct x, y, z; simpl; solve_matrix. 
Qed.

Lemma AND_spec : forall (x y z safe : bool), 
    denote_box safe AND (bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix z)  = 
    bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix ((x && y) ⊕ z).
Proof. 
  ket_denote. Msimpl.
  destruct x, y, z; simpl; Msimpl; solve_matrix. 
Qed.

