Require Import HOASLib.
Require Import Denotation.
Require Import TypeChecking.

Open Scope matrix_scope.

(***************************)
(* Approximate Slide Lemma *)
(***************************)

(* How did this get here?
Lemma slide : forall (p q : Pat Qubit) (Γ0 Γ : Ctx) (U V : Unitary Qubit), 
  denote_circuit true (let_ p' ← U $ p; let_ q' ← V $ q; (p',q')) Γ0 Γ = 
  denote_circuit true (let_ q' ← V $ q; let_ p' ← U $ p; (p',q')) Γ0 Γ.
Proof.
  intros p q Γ0 Γ U V. simpl. 
  unfold denote_circuit.
  simpl.
  dependent destruction p.
  dependent destruction q.
  simpl.
  autounfold with den_db. simpl.

  *)

(* ---------------------------------------*)
(*--------- Boxed Circuit Specs ----------*)
(* ---------------------------------------*)

(* TODO: add lemmas to proof_db *)
Lemma id_circ_spec : forall W ρ safe, WF_Matrix ρ -> 
  denote_box safe  (@id_circ W) ρ = ρ.
Proof.
  intros W ρ safe H.
  simpl. unfold denote_box. simpl.
  autorewrite with proof_db.
  rewrite add_fresh_split.
  simpl.
  unfold pad.
  simpl.
  rewrite Nat.sub_diag.
  rewrite kron_1_r.
  rewrite subst_pat_fresh_empty.
  rewrite denote_pat_fresh_id.
  rewrite super_I; auto.
Qed.

Lemma X_spec : forall (b safe : bool), denote_box safe (boxed_gate _X) (bool_to_matrix b) = 
                               bool_to_matrix (¬ b).
Proof. intros. vector_denote. destruct b; solve_matrix. Qed.

Lemma init0_spec : forall safe, denote_box safe init0 (I (2^0)) = ∣0⟩⟨0∣.
Proof. intros. matrix_denote. Msimpl. reflexivity. Qed.

Lemma init1_spec : forall safe, denote_box safe init1 (I (2^0)) = ∣1⟩⟨1∣.
Proof. intros. matrix_denote. Msimpl. reflexivity. Qed.

Lemma assert0_spec : forall safe, denote_box safe assert0 ∣0⟩⟨0∣ = I 1. 
Proof.  
  destruct safe.
  - matrix_denote.
    Msimpl.
    solve_matrix.
  - matrix_denote.
    Msimpl.
    solve_matrix.
Qed.

Lemma assert1_spec : forall safe, denote_box safe assert1 ∣1⟩⟨1∣ = I 1. 
Proof.  
  destruct safe.
  - matrix_denote.
    Msimpl.
    solve_matrix.
  - matrix_denote.
    Msimpl.
    solve_matrix.
Qed.

Lemma init_spec : forall b safe, denote_box safe (init b) (I (2^0)) = bool_to_matrix b.
Proof. destruct b; [apply init1_spec | apply init0_spec]. Qed.

Lemma assert_spec : forall b safe, denote_box safe (assert b) (bool_to_matrix b) = I 1.
Proof. destruct b; [apply assert1_spec | apply assert0_spec]. Qed.

Lemma SWAP_spec : forall ρ safe, denote_box safe SWAP ρ = swap × ρ × swap.
Proof. intros. matrix_denote. Msimpl. setoid_rewrite swap_sa. reflexivity. Qed.

Lemma SWAP_spec_sep : forall (ρ1 ρ2 : Density 2) safe,
  WF_Matrix ρ1 -> WF_Matrix ρ2 ->
  denote_box safe SWAP (ρ1 ⊗ ρ2) = ρ2 ⊗ ρ1.
Proof. intros. rewrite SWAP_spec. solve_matrix. Qed.

(* MOVE THIS! *)
Lemma fresh_wtype : forall (w : WType) (Γ : Ctx), add_fresh_state w Γ = Γ ++ (add_fresh_state w []).
Proof.
  intros. generalize dependent Γ.
  induction w; unfold add_fresh_state; simpl; try reflexivity; intros.
  - induction Γ; simpl; try reflexivity.
    rewrite <- IHΓ. reflexivity.
  - repeat rewrite add_fresh_split. simpl.
    replace (add_fresh_state w2 (add_fresh_state w1 [])) with ((add_fresh_state w1 []) ++ (add_fresh_state w2 [])) by (rewrite <- IHw2; reflexivity).
    rewrite IHw2. rewrite IHw1. rewrite app_assoc. reflexivity.
Qed.


Lemma SWAP_GEN_spec_same_sep : forall W (ρ1 ρ2 : Density (2^⟦W⟧)) safe,
    denote_box safe (@SWAP_GEN W W) (ρ1 ⊗ ρ2) = ρ2 ⊗ ρ1.
Proof.
  matrix_denote.
  repeat rewrite add_fresh_split.
  unfold hoas_to_db. simpl.
  Search subst_pat.
  rewrite subst_pat_fresh.
  rewrite pad_nothing.
  unfold denote_pat. simpl.
  rewrite subst_pat_no_gaps.

  2:{ rewrite fresh_wtype. rewrite app_length.
      Search Bounded_Pat.
      apply bounded_pat_le with (length (add_fresh_state W [])). 
      lia.
      rewrite length_fresh_state with (w := W) (Γ' := add_fresh_state W []) (Γ := []) by easy.
      apply add_fresh_pat_bounded.
      constructor.
  }

  all: repeat apply add_fresh_state_no_gaps; try constructor.
  Search pat_to_list add_fresh_pat.
  repeat rewrite swap_fresh_seq. simpl.
  Search length add_fresh_state.
  erewrite length_fresh_state by reflexivity. simpl.
Abort.
  
(* -----------------------------------------*)
(*--------- Reversible Circuit Specs -------*)
(* -----------------------------------------*)

Lemma CNOT_spec : forall (b1 b2 safe : bool), 
  denote_box safe CNOT (bool_to_matrix b1 ⊗ bool_to_matrix b2)
  = (bool_to_matrix b1 ⊗ bool_to_matrix (b1 ⊕ b2)).
Proof.
  vector_denote. destruct b1, b2; unfold bool_to_ket; simpl; Msimpl; solve_matrix.
Qed.

Lemma TRUE_spec : forall z safe, 
  denote_box safe TRUE (bool_to_matrix z) = bool_to_matrix (true ⊕ z). 
Proof. vector_denote. destruct z; solve_matrix. Qed.

Lemma FALSE_spec : forall z safe, 
    denote_box safe FALSE (bool_to_matrix z) = bool_to_matrix (false ⊕ z). 
Proof. vector_denote. destruct z; solve_matrix. Qed.

Lemma NOT_spec : forall (x z : bool), 
  forall safe, denote_box safe NOT (bool_to_matrix x ⊗ bool_to_matrix z) = 
  bool_to_matrix x ⊗ bool_to_matrix ((¬ x) ⊕ z).
Proof.
  vector_denote. 
  destruct x, z; unfold bool_to_ket; simpl; Msimpl; solve_matrix. 
Qed.

Lemma XOR_spec : forall (x y z safe : bool), 
    denote_box safe XOR (bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix z)  = 
    bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix (x ⊕ y ⊕ z).
Proof.  
  vector_denote. Msimpl.
  destruct x, y, z; simpl; solve_matrix. 
Qed.

Lemma AND_spec : forall (x y z safe : bool), 
    denote_box safe AND (bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix z)  = 
    bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix ((x && y) ⊕ z).
Proof. 
  vector_denote. Msimpl.
  destruct x, y, z; simpl; Msimpl; solve_matrix. 
Qed.

