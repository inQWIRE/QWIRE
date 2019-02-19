Require Export Quantum.

(************************************)
(* Unitary Properties on Basis Kets *)
(************************************)

(*
Definition plus_state := 1/√2 .* ∣0⟩ .+ 1/√2 .* ∣1⟩.
Definition minus_state := 1/√2 .* ∣0⟩ .+ (-1/√2) .* ∣1⟩.

Transparent plus_state.
Transparent minus_state.
                                                       
Notation "∣+⟩" := plus_state.
Notation "∣-⟩" := minus_state.
*)

Notation "∣+⟩" := (/√2 .* ∣0⟩ .+ /√2 .* ∣1⟩).
Notation "∣-⟩" := (/√2 .* ∣0⟩ .+ (-/√2) .* ∣1⟩).

(* Hadamard properties *)
Lemma H0_spec : hadamard × ∣0⟩ = ∣+⟩.
Proof. solve_matrix. Qed.

Lemma H1_spec : hadamard × ∣1⟩ = ∣-⟩.
Proof. solve_matrix. Qed.

Lemma Hplus_spec : hadamard × ∣+⟩ = ∣0⟩.
Proof. solve_matrix. Qed.

Lemma Hminus_spec : hadamard × ∣-⟩ = ∣1⟩.
Proof. solve_matrix.  Qed.

(* X properties *)
Lemma X0_spec : σx × ∣0⟩ = ∣1⟩.
Proof. solve_matrix. Qed.

Lemma X1_spec : σx × ∣1⟩ = ∣0⟩.
Proof. solve_matrix. Qed.

(* Y properties *)
Lemma Y0_spec : σy × ∣0⟩ = Ci .* ∣1⟩.
Proof. solve_matrix. Qed.

Lemma Y1_spec : σy × ∣1⟩ = -Ci .* ∣0⟩.
Proof. solve_matrix. Qed.

(* Z properties *)
Lemma Z0_spec : σz × ∣0⟩ = ∣0⟩.
Proof. solve_matrix. Qed.

Lemma Z1_spec : σz × ∣1⟩ = -1 .* ∣1⟩.
Proof. solve_matrix. Qed.

(* CNOT properties *)

Lemma CNOT_spec : forall (x y : nat), (x < 2)%nat -> (y < 2)%nat -> cnot × ∣x,y⟩ = ∣x, (x + y) mod 2⟩.
Proof.
  intros; destruct x as [| [|x]], y as [| [|y]]; try omega; solve_matrix.
Qed.

Lemma CNOT00_spec : cnot × ∣0,0⟩ = ∣0,0⟩.
Proof. solve_matrix. Qed.

Lemma CNOT01_spec : cnot × ∣0,1⟩ = ∣0,1⟩.
Proof. crunch_matrix. Qed.

Lemma CNOT10_spec : cnot × ∣1,0⟩ = ∣1,1⟩.
Proof. solve_matrix. Qed.
                                        
Lemma CNOT11_spec : cnot × ∣1,1⟩ = ∣1,0⟩.
Proof. solve_matrix. Qed.

(* SWAP properties *)

Lemma SWAP_spec : forall x y, swap × ∣x,y⟩ = ∣y,x⟩.
Proof. intros. destruct x,y; solve_matrix. Qed.

(* Automation *)

Hint Rewrite Mmult_plus_distr_l Mscale_plus_distr Mscale_mult_dist_r Mscale_mult_dist_l : ket_db.
Hint Rewrite Mscale_assoc Mmult_assoc: ket_db.
Hint Rewrite Mscale_0_l Mscale_1_l : ket_db.
Hint Rewrite H0_spec H1_spec Hplus_spec Hminus_spec X0_spec X1_spec Y0_spec Y1_spec
     Z0_spec Z1_spec : ket_db.

Ltac ket_eq_solver :=
  intros; autorewrite with ket_db C_db;
  try match goal with
  | [|- ?a .* ∣0⟩ .+ ?b .* ∣1⟩ = ?a' .* ∣0⟩ .+ ?b' .* ∣1⟩ ] =>
    replace a with a'; try clra; replace b with b'; try clra; trivial
  end.                                                           

Lemma XYZ0 : -Ci .* σx × σy × σz × ∣0⟩ = ∣0⟩.
Proof. autorewrite with ket_db C_db; easy. Qed.
                                            
Lemma XYZ1 : -Ci .* σx × σy × σz × ∣1⟩ = ∣1⟩.
Proof. autorewrite with ket_db C_db; easy. Qed.

Lemma XYZ : forall α β, -Ci .* σx × σy × σz × (α .* ∣0⟩ .+ β .* ∣1⟩) = α .* ∣0⟩ .+ β .* ∣1⟩.
Proof. ket_eq_solver. Qed.

Proposition HZH : forall α β,
  hadamard × σz × hadamard × (α .* ∣0⟩ .+ β .* ∣1⟩) = σx × (α .* ∣0⟩ .+ β .* ∣1⟩).
Proof.
  ket_eq_solver.
Abort.

(* Next up:
   Multiqubit systems.
   Have ket_eq_solver group ∣0⟩s and ∣1⟩s.
*)
