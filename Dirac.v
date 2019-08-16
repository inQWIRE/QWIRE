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

Notation "∣ + ⟩" := (/√2 .* ∣ 0 ⟩ .+ /√2 .* ∣ 1 ⟩).
Notation "∣ - ⟩" := (/√2 .* ∣ 0 ⟩ .+ (-/√2) .* ∣ 1 ⟩).

(* Bra-Ket properties *)

Lemma bra0_equiv : ⟨0∣ == bra 0.
Proof. reflexivity. Qed.

Lemma bra1_equiv : ⟨1∣ == bra 1.
Proof. reflexivity. Qed.

Lemma ket0_equiv : ∣0⟩ == ket 0.
Proof. reflexivity. Qed.

Lemma ket1_equiv : ∣1⟩ == ket 1.
Proof. reflexivity. Qed.

Lemma bra0ket0 : bra 0 × ket 0 == I 1.
Proof. lma. Qed.

Lemma bra0ket1 : bra 0 × ket 1 == Zero.
Proof. lma. Qed.

Lemma bra1ket0 : bra 1 × ket 0 == Zero.
Proof. lma. Qed.

Lemma bra1ket1 : bra 1 × ket 1 == I 1.
Proof. lma. Qed.

(* Hadamard properties *)
Lemma H0_spec : hadamard × ∣ 0 ⟩ == ∣ + ⟩.
Proof. lma. Qed.

Lemma H1_spec : hadamard × ∣ 1 ⟩ == ∣ - ⟩.
Proof. lma. Qed.

Lemma Hplus_spec : hadamard × ∣ + ⟩ == ∣ 0 ⟩.
Proof. solve_matrix. Qed.

Lemma Hminus_spec : hadamard × ∣ - ⟩ == ∣ 1 ⟩.
Proof. solve_matrix.  Qed.

(* X properties *)
Lemma X0_spec : σx × ∣ 0 ⟩ == ∣ 1 ⟩.
Proof. lma. Qed.

Lemma X1_spec : σx × ∣ 1 ⟩ == ∣ 0 ⟩.
Proof. lma. Qed.

(* Y properties *)
Lemma Y0_spec : σy × ∣ 0 ⟩ == Ci .* ∣ 1 ⟩.
Proof. lma. Qed.

Lemma Y1_spec : σy × ∣ 1 ⟩ == -Ci .* ∣ 0 ⟩.
Proof. lma. Qed.

(* Z properties *)
Lemma Z0_spec : σz × ∣ 0 ⟩ == ∣ 0 ⟩.
Proof. lma. Qed.

Lemma Z1_spec : σz × ∣ 1 ⟩ == -1 .* ∣ 1 ⟩.
Proof. lma. Qed.

(* CNOT properties *)

Lemma CNOT_spec : forall (x y : nat), (x < 2)%nat -> (y < 2)%nat -> 
  cnot × ∣ x,y ⟩ == ∣ x, (x + y) mod 2 ⟩.
Proof.
  intros; destruct x as [| [|x]], y as [| [|y]]; try lia; lma.
Qed.

Lemma CNOT00_spec : cnot × ∣ 0,0 ⟩ == ∣ 0,0 ⟩.
Proof. lma. Qed.

Lemma CNOT01_spec : cnot × ∣ 0,1 ⟩ == ∣ 0,1 ⟩.
Proof. crunch_matrix. Qed.

Lemma CNOT10_spec : cnot × ∣ 1,0 ⟩ == ∣ 1,1 ⟩.
Proof. lma. Qed.
                                        
Lemma CNOT11_spec : cnot × ∣ 1,1 ⟩ == ∣ 1,0 ⟩.
Proof. lma. Qed.

(* SWAP properties *)

Lemma SWAP_spec : forall x y, swap × ∣ x,y ⟩ == ∣ y,x ⟩.
Proof. intros. destruct x,y; lma. Qed.

(* Automation *)

(* General matrix rewrites *)
Hint Rewrite bra0_equiv bra1_equiv ket0_equiv ket1_equiv : ket_db.
Hint Rewrite bra0ket0 bra0ket1 bra1ket0 bra1ket1 : ket_db.
Hint Rewrite @Mmult_plus_dist_l @Mmult_plus_dist_r @kron_plus_dist_l @kron_plus_dist_r @Mscale_plus_dist_r : ket_db.
Hint Rewrite @Mscale_mult_dist_l @Mscale_mult_dist_r @Mscale_kron_dist_l @Mscale_kron_dist_r : ket_db.
Hint Rewrite @Mscale_assoc @Mmult_assoc : ket_db.
(*Hint Rewrite <- Mplus_assoc kron_assoc : ket_db.*)
Hint Rewrite @Mmult_1_l @Mmult_1_r @kron_1_l @kron_1_r @Mscale_0_l @Mscale_1_l @Mplus_0_l @Mplus_0_r : ket_db.
Hint Rewrite @kron_mixed_product.

(* Quantum-specific identities *)
Hint Rewrite H0_spec H1_spec Hplus_spec Hminus_spec X0_spec X1_spec Y0_spec Y1_spec
     Z0_spec Z1_spec : ket_db.
Hint Rewrite CNOT00_spec CNOT01_spec CNOT10_spec CNOT11_spec SWAP_spec : ket_db.

(* Examples using ket_db *)
Lemma XYZ0 : -Ci .* σx × σy × σz × ∣ 0 ⟩ == ∣ 0 ⟩.
Proof. autorewrite with ket_db C_db; easy. Qed.
                                           
Lemma XYZ1 : -Ci .* σx × σy × σz × ∣ 1 ⟩ == ∣ 1 ⟩.
Proof. 
  autorewrite with ket_db C_db. 
  replace (Ci * -1 * Ci) with (RtoC 1) by lca. 
  rewrite Mscale_1_l; reflexivity.
  Qed.

(* Simplify left-associated sums of terms of the form (a .* ∣ x ⟩).   
   The end result should have the form (a .* ∣ 0 ⟩ .+ b .* ∣ 1 ⟩) *)
Ltac simpl_ket_1_qubit :=
  repeat
  (match goal with
    (* combine like terms *)
    | [ |- context[ ?a .* ∣ ?x ⟩ .+ ?b .* ∣ ?x ⟩ ] ] => 
          rewrite <- (Mscale_plus_dist_l _ _ a b ∣ x ⟩)
    | [ |- context[ (?a .+ ?b .* ∣ ?x ⟩) .+ ?c .* ∣ ?x ⟩ ] ] => 
          rewrite (Mplus_assoc _ _ a (b .* ∣ x ⟩) (c .* ∣ x ⟩));
          rewrite <- (Mscale_plus_dist_l _ _ b c ∣ x ⟩)
    (* reorder terms *)
    | [ |- context[ ?a .* ∣ 1 ⟩ .+ ?b .* ∣ 0 ⟩ ] ] => 
          rewrite (Mplus_comm _ _ (a .* ∣ 1 ⟩) (b .* ∣ 0 ⟩))
    | [ |- context[ (?a .+ ?b .* ∣ 1 ⟩) .+ ?c .* ∣ 0 ⟩ ] ] => 
          rewrite (Mplus_assoc _ _ a (b .* ∣ 1 ⟩) (c .* ∣ 0 ⟩));
          rewrite (Mplus_comm _ _ (b .* ∣ 1 ⟩) (c .* ∣ 0 ⟩)); 
          rewrite <- (Mplus_assoc _ _ a (c .* ∣ 0 ⟩) (b .* ∣ 1 ⟩))
   
  end).
    
(* Simplify left-associated sums of terms of the form (a .* ∣ x,y ⟩).
   The end result should have the form
       a .* ∣ 0,0 ⟩ .+ b .* ∣ 0,1 ⟩ .+ c .* ∣ 1,0 ⟩ .+ d .* ∣ 1,1 ⟩ *)
Local Open Scope nat_scope.
Ltac simpl_ket_2_qubit :=
  repeat
  (match goal with
    (* combine like terms *)
    | [ |- context[ ?a .* ∣ ?x,?y ⟩ .+ ?b .* ∣ ?x,?y ⟩ ] ] => 
          rewrite <- (Mscale_plus_dist_l _ _ a b ∣ x,y ⟩)
    | [ |- context[ (?a .+ ?b .* ∣ ?x,?y ⟩) .+ ?c .* ∣ ?x,?y ⟩ ] ] => 
          rewrite (Mplus_assoc _ _ a (b .* ∣ x,y ⟩) (c .* ∣ x,y ⟩));
          rewrite <- (Mscale_plus_dist_l _ _ b c ∣ x,y ⟩)
    (* reorder terms *)
    (* NOTE: we could also write explicit rules for 00, 01, 10, 11,
       but this seemed cleaner. I don't know how this style impacts
       automation efficiency. *) 
    | [ |- context[ ?a .* ∣ ?x,?y ⟩ .+ ?b .* ∣ ?x',?y' ⟩ ] ] => 
          assert ((x' < x) \/ (x' = x /\ y' < y)) by lia;
          rewrite (Mplus_comm _ _ (a .* ∣ x,y ⟩) (b .* ∣ x',y' ⟩))
    | [ |- context[ ?a .+ ?b .* ∣ ?x,?y ⟩ .+ ?c .* ∣ ?x',?y' ⟩ ] ] => 
          assert ((x' < x) \/ (x' = x /\ y' < y)) by lia;
          rewrite (Mplus_assoc _ _ a (b .* ∣ x,y ⟩) (c .* ∣ x',y' ⟩));
          rewrite (Mplus_comm _ _ (b .* ∣ x,y ⟩) (c .* ∣ x',y' ⟩)); 
          rewrite <- (Mplus_assoc _ _ a (c .* ∣ x',y' ⟩) (b .* ∣ x,y ⟩))   
  end). 
Local Close Scope nat_scope. 

(* The main issue with simpl_ket_1_qubit and simpl_ket_2_qubit is that
   they expect the goal to be in a particular form, so I need to write
   additional tactics to put the goal in the desired form.

   I'd also like to write a version of ket_eq_solver that works for
   multi-qubit systems. *)

Ltac ket_eq_solver :=
  intros; autorewrite with ket_db C_db;
  try match goal with
  | [ |- ?a .* ∣ 0 ⟩ .+ ?b .* ∣ 1 ⟩ == ?a' .* ∣ 0 ⟩ .+ ?b' .* ∣ 1 ⟩ ] =>
    replace a with a' by lca; replace b with b' by lca; reflexivity
  end.      

Lemma XYZ : forall α β,
  -Ci .* σx × σy × σz × (α .* ∣ 0 ⟩ .+ β .* ∣ 1 ⟩) == α .* ∣ 0 ⟩ .+ β .* ∣ 1 ⟩.
Proof. ket_eq_solver. Qed.

(* This proof would be nicest with +/- basis specific rewriting.

Proposition HZH : forall α β,
  hadamard × σz × hadamard × (α .* ∣ 0 ⟩ .+ β .* ∣ 1 ⟩) = σx × (α .* ∣ 0 ⟩ .+ β .* ∣ 1 ⟩).
Proof.
  ket_eq_solver.
Abort.

Proposition HXH : forall α β,
  hadamard × σx × hadamard × (α .* ∣ 0 ⟩ .+ β .* ∣ 1 ⟩) = σz × (α .* ∣ 0 ⟩ .+ β .* ∣ 1 ⟩).
Proof.
  ket_eq_solver.
Abort.

Proposition H_CNOT_H : (I 2 ⊗ hadamard) × cnot × (I 2 ⊗ hadamard) = control σz .
Proof.
Abort.

 *)
                                                                             


