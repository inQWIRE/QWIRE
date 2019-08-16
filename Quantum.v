Require Import Psatz.
Require Import Reals.
Require Import Setoid.
Require Export Matrix.

(* Using our (complex, unbounded) matrices, their complex numbers *)

(*******************************************)
(* Quantum basis states *)
(*******************************************)

(* Notation qubit := (Vector 2). *)

(* Maybe change to IF statements? *)
Definition qubit0 : Vector 2 := fun i j => if i =? 0 then 1 else 0.
Definition qubit1 : Vector 2 := fun i j => if i =? 1 then 1 else 0.

(* Ket notation: \mid 0 \rangle *)
Notation "∣0⟩" := qubit0.
Notation "∣1⟩" := qubit1.
Notation "⟨0∣" := qubit0†.
Notation "⟨1∣" := qubit1†.
Notation "∣0⟩⟨0∣" := (∣0⟩×⟨0∣).
Notation "∣1⟩⟨1∣" := (∣1⟩×⟨1∣).
Notation "∣1⟩⟨0∣" := (∣1⟩×⟨0∣).
Notation "∣0⟩⟨1∣" := (∣0⟩×⟨1∣).

Definition bra (x : nat) : Matrix 1 2 := if x =? 0 then ⟨0∣ else ⟨1∣.
Definition ket (x : nat) : Matrix 2 1 := if x =? 0 then ∣0⟩ else ∣1⟩.

(* Note the 'mid' symbol for these *)
Notation "'∣' x '⟩'" := (ket x).
Notation "'⟨' x '∣'" := (bra x). (* This gives the Coq parser headaches *)

Notation "∣ x , y , .. , z ⟩" := (kron .. (kron ∣x⟩ ∣y⟩) .. ∣z⟩) (at level 0).
(* Alternative: |0⟩|1⟩. *)

(*                                                                       
Transparent bra.
Transparent ket.
Transparent qubit0.
Transparent qubit1.
*)

Definition bool_to_ket (b : bool) : Matrix 2 1 := if b then ∣1⟩ else ∣0⟩.
                                                                     
Definition bool_to_matrix (b : bool) : Matrix 2 2 := if b then ∣1⟩⟨1∣ else ∣0⟩⟨0∣.

Definition bool_to_matrix' (b : bool) : Matrix 2 2 :=
  fun i j => if negb b && (i =? 0) && (j =? 0) then 1 
          else if b && (i =? 1) && (j =? 1) then 1
          else 0.

Lemma bool_to_matrix_eq : forall b, bool_to_matrix b == bool_to_matrix' b.
Proof. destruct b; lma. Qed.

Lemma bool_to_ket_matrix_eq : forall b,
    outer_product (bool_to_ket b) (bool_to_ket b) == bool_to_matrix b.
Proof. destruct b; lma. Qed.

Definition bools_to_matrix (l : list bool) : Square (2^(length l)) := 
  big_kron (map bool_to_matrix l).


(*************)
(* Unitaries *)
(*************)

Definition hadamard : Square 2 := 
  fun i j => if (i =? 1) && (j =? 1) then -/√2 else /√2. 

Fixpoint hadamard_k (k : nat) : Matrix (2^k) (2^k):= 
  match k with
  | 0 => I 1
  | S k' => hadamard ⊗ hadamard_k k'
  end. 

Lemma hadamard_1 : hadamard_k 1 == hadamard.
Proof. apply kron_1_r. Qed.

(* Alternative definitions:
Definition pauli_x : Matrix 2 2 := fun x y => if x + y =? 1 then 1 else 0.
Definition pauli_y : Matrix 2 2 := fun x y => if x + y =? 1 then (-1) ^ x * Ci else 0.
Definition pauli_z : Matrix 2 2 := fun x y => if (x =? y) && (x <? 2) 
                                           then (-1) ^ x else 0.
*)

Definition σx : Square 2 := fun i j => if i + j =? 1 then 1 else 0.
Definition σy : Square 2 := fun i j => if i + j =? 1 then (-1) ^ j * Ci else 0.
Definition σz : Square 2 := fun i j => if i =? j then (-1) ^ i else 0.

(* Could do [i =? j then Cexp i] but not worth having to simplify *)
Definition phase_shift (ϕ : R) : Square 2 := 
  fun i j => if (i =? 0) && (j =? 0) then 1 
          else if (i =? 1) && (j =? 1) then Cexp ϕ
          else 0.
  
(** X Lemmas - need in this file? *)
Lemma MmultX1 : σx × ∣1⟩ == ∣0⟩. Proof. lma. Qed.  
Lemma Mmult1X : ⟨1∣ × σx == ⟨0∣. Proof. lma. Qed.
Lemma MmultX0 : σx × ∣0⟩ == ∣1⟩. Proof. lma. Qed.
Lemma Mmult0X : ⟨0∣ × σx == ⟨1∣. Proof. lma. Qed.

Hint Rewrite Mmult0X Mmult1X MmultX0 MmultX1 : M_db.

(** Controlled unitaries *)

Definition control {n : nat} (A : Matrix n n) : Matrix (2*n) (2*n) :=
  fun x y => if (x <? n) && (y =? x) then 1 else 
          if (n <=? x) && (n <=? y) then A (x-n)%nat (y-n)%nat else 0.

(* Definition cnot := control pauli_x. *)
(* Direct definition makes our lives easier *)
(* Dimensions are given their current form for convenient
   kron_mixed_product applications *)
Definition cnot : Matrix (2*2) (2*2) :=
  fun i j => if ((i =? j) && (i <? 2)) || (i + j =? 5) then 1 else 0.
                                                          
Lemma cnot_eq : cnot == control σx.
Proof. lma. Qed.

Definition notc : Matrix (2*2) (2*2) :=
  fun i j => if (i + j =? 0) || (i + j =? 4) then 1 else 0.

Lemma control_compat : forall n (A B : Matrix n n), A == B -> control A == control B.
Proof.
  intros n A B H i j Hi Hj.
  unfold control.
  destruct ((i <? n) && (j =? i)), ((n <=? i) && (n <=? j)); trivial.
  rewrite H; trivial; lia.
Qed.

Add Parametric Morphism n : (@control n)
  with signature mat_equiv ==> mat_equiv as control_mor.
Proof. intros. apply control_compat; easy. Qed.
  
(** SWAP *)

Definition swap : Matrix (2*2) (2*2) :=
  fun i j => if (i + j =? 0) || (i * j =? 2) || (i + j =? 6) then 1 else 0.


(* Does this overwrite the other Hint DB M? *)
Hint Unfold qubit0 qubit1 hadamard σx σy σz phase_shift 
            control cnot notc swap bra ket : U_db.

Lemma swap_swap : swap × swap == I (2*2). Proof. lma. Qed.

Lemma swap_swap_r : forall (A : Matrix (2*2) (2*2)), 
  A × swap × swap == A.
Proof. lma. Qed.

(* The input k is really k+1, to appease to Coq termination gods *)
(* NOTE: Check that the offsets are right *)
(* Requires: i + 1 < n *)
Fixpoint swap_to_0_aux (n i : nat) {struct i} : Matrix (2^n) (2^n) := 
  match i with
  | O => swap ⊗ I (2^(n-2))
  | S i' =>  (I (2^i) ⊗ swap ⊗ I (2^(n-i-2))) × (* swap i-1 with i *)
            swap_to_0_aux n i' × 
            (I (2^i) ⊗ swap ⊗ I (2^(n-i-2))) (* swap i-1 with 0 *)
  end.

(* Requires: i < n *)
Definition swap_to_0 (n i : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => I (2^n) 
  | S i' => swap_to_0_aux n i'
  end.
  
(* Swapping qubits i and j in an n-qubit system, where i < j *) 
(* Requires i < j, j < n *)
Fixpoint swap_two_aux (n i j : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => swap_to_0 n j 
  | S i' => I 2 ⊗ swap_two_aux (n-1) (i') (j-1)
  end.

(* Swapping qubits i and j in an n-qubit system *)
(* Requires i < n, j < n *)
Definition swap_two (n i j : nat) : Matrix (2^n) (2^n) :=
  if i =? j then I (2^n) 
  else if i <? j then swap_two_aux n i j
  else swap_two_aux n j i.

(* Simpler version of swap_to_0 that shifts other elements *)
(* Requires: i+1 < n *)
Fixpoint move_to_0_aux (n i : nat) {struct i}: Matrix (2^n) (2^n) := 
  match i with
  | O => swap ⊗ I (2^(n-2))
  | S i' => (move_to_0_aux n i') × (I (2^i) ⊗ swap ⊗ I (2^(n-i-2))) 
                  
  end.
             
(* Requires: i < n *)
Definition move_to_0 (n i : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => I (2^n) 
  | S i' => move_to_0_aux n i'
  end.
 
(* Always moves up in the matrix from i to k *)
(* Requires: k < i < n *)
Fixpoint move_to (n i k : nat) : Matrix (2^n) (2^n) := 
  match k with 
  | O => move_to_0 n i 
  | S k' => I 2 ⊗ move_to (n-1) (i-1) (k')
  end.

(***************************)
(** Unitaries are unitary **)
(***************************)

Definition WF_Unitary {n: nat} (U : Matrix n n): Prop :=
  U † × U == I n.

Hint Unfold WF_Unitary : U_db.

(* More precise *)
(* Definition unitary_matrix' {n: nat} (A : Matrix n n): Prop := Minv A A†. *)

Lemma H_unitary : WF_Unitary hadamard.
Proof.
  (* I'd like to switch this to use C_field as some point *)
  by_cell; autounfold with U_db; simpl; group_radicals; lca.
Qed.

Lemma σx_unitary : WF_Unitary σx. Proof. lma. Qed.
Lemma σy_unitary : WF_Unitary σy. Proof. lma. Qed.
Lemma σz_unitary : WF_Unitary σz. Proof. lma. Qed.

Lemma phase_unitary : forall ϕ, @WF_Unitary 2 (phase_shift ϕ).
Proof. 
  by_cell; autounfold with U_db; simpl; try lca. 
  apply c_proj_eq; simpl; try lra.
  autorewrite with R_db.
  replace (cos ϕ * cos ϕ)%R with ((cos ϕ)²) by easy.
  replace (sin ϕ * sin ϕ)%R with ((sin ϕ)²) by easy. 
  rewrite Rplus_comm.
  rewrite sin2_cos2.
  reflexivity.
Qed.

Lemma control_unitary : forall n (A : Matrix n n), 
  WF_Unitary A -> WF_Unitary (control A). 
Proof.
  intros n A U.
  unfold WF_Unitary in *.
  unfold control, adjoint, Mmult, I.
  intros x y Hx Hy.
  simpl.
  bdestructΩ (x =? y).
  - subst; simpl.
    rewrite Csum_sum.
    bdestructΩ (y <? n + (n + 0)).
    + bdestructΩ (n <=? y).
      * rewrite Csum_0_bounded. Csimpl.
        rewrite (Csum_eq_bounded _ (fun x => A x (y - n)%nat ^* * A x (y - n)%nat)).
        ++ unfold control, adjoint, Mmult, I in U.
           rewrite Nat.add_0_r.
           rewrite U by lia.
           rewrite Nat.eqb_refl. 
           easy.
        ++ intros x L.
           bdestructΩ (n + x <? n).
           bdestructΩ (n <=? n + x).
           rewrite minus_plus.
           easy.
        ++ intros x L.
           bdestructΩ (y =? x).
           rewrite andb_false_r.
           bdestructΩ (n <=? x).
           lca.
      * rewrite (Csum_unique _ 1 _ y); try lia.
        rewrite Csum_0_bounded; try lca.
        ++ intros.
           rewrite andb_false_r.
           bdestructΩ (n + x <? n).
           simpl.
           lca.
        ++ rewrite Nat.eqb_refl.
           bdestructΩ (y <? n).
           lca.
        ++ intros.
           bdestructΩ (y =? x').
           repeat rewrite andb_false_r.
           lca.
  - simpl.
    rewrite Csum_sum.
    bdestructΩ (y <? n + (n + 0)).
    + bdestructΩ (n <=? y).
      * rewrite Csum_0_bounded. Csimpl.
        bdestructΩ (n <=? x).
        rewrite (Csum_eq_bounded _ (fun z => A z (x - n)%nat ^* * A z (y - n)%nat)).
        ++ unfold control, adjoint, Mmult, I in U.
           rewrite Nat.add_0_r.
           rewrite U by lia.
           bdestructΩ (x - n =? y - n).
           simpl.
           easy.
        ++ intros z L.
           bdestructΩ (n + z <? n).
           bdestructΩ (n <=? n + z).
           rewrite minus_plus.
           easy.
        ++ rewrite Nat.add_0_r. 
           rewrite Csum_0_bounded; trivial. 
           intros z L.
           bdestructΩ (n + z <? n).
           rewrite andb_false_r.
           Csimpl. 
           easy. 
        ++ intros z L.
           bdestructΩ (z <? n).
           bdestructΩ (n <=? z).
           bdestructΩ (x =? z); bdestructΩ (y =? z); try lca. 
      * bdestructΩ (n <=? x).        
        ++ rewrite Csum_0_bounded.
           rewrite Csum_0_bounded. lca.
           ** intros z L.
              bdestructΩ (n + z <? n).
              rewrite andb_false_r.
              lca.
           ** intros z L.
              bdestructΩ (z <? n).
              rewrite andb_false_r.
              bdestructΩ (x =? z); bdestructΩ (y =? z); try lca.
              bdestructΩ (n <=? z).
              lca.
        ++ rewrite 2 Csum_0_bounded; [lca| |].
           ** intros z L.
              rewrite andb_false_r.
              bdestructΩ (x =? n + z); bdestructΩ (y =? n + z); 
                rewrite andb_false_r; lca.
           ** intros z L.
              rewrite andb_false_r.
              bdestructΩ (x =? z); bdestructΩ (y =? z); rewrite andb_false_r; lca.
Qed.

Lemma transpose_unitary : forall n (A : Matrix n n), WF_Unitary A -> WF_Unitary (A†).
Proof. 
  intros. 
  unfold WF_Unitary in *.
  rewrite adjoint_involutive.
  apply Minv_left in H as [_ S]. (* NB: admitted lemma *)
  assumption.
Qed.

Lemma cnot_unitary : WF_Unitary cnot.
Proof. lma. Qed.

Lemma id_unitary : forall n, WF_Unitary (I n). 
Proof. 
  intros n.
  unfold WF_Unitary.
  rewrite id_adjoint_eq.
  apply Mmult_1_l.
Qed.

Lemma swap_unitary : WF_Unitary swap.
Proof. lma. Qed.

Lemma zero_not_unitary : forall n, ~ (WF_Unitary (@Zero (2^n) (2^n))).
Proof.
  intros n.
  assert (2 <> 0)%nat by lia.
  specialize (pow_positive 2 n H) as P. clear H.
  intros U.
  specialize (U _ _ P P).
  revert U.
  rewrite Mmult_0_r; trivial.
  unfold I, Zero.
  simpl.
  intros U.
  inversion U.
  lra.
Qed.

Lemma kron_unitary : forall {m n} (A : Matrix m m) (B : Matrix n n),
  WF_Unitary A -> WF_Unitary B -> WF_Unitary (A ⊗ B).
Proof.
  intros m n A B UA UB.
  unfold WF_Unitary in *.
  rewrite kron_adjoint.
  rewrite kron_mixed_product.
  rewrite UA, UB.
  rewrite id_kron. 
  easy.
Qed.

Lemma Mmult_unitary : forall (n : nat) (A : Square n) (B : Square n),
  WF_Unitary A ->
  WF_Unitary B ->
  WF_Unitary (A × B).  
Proof.
  intros n A B UA UB.
  unfold WF_Unitary in *.
  restore_dims.
  Msimpl.
  rewrite Mmult_assoc.
  rewrite <- (Mmult_assoc A†).
  rewrite UA.
  Msimpl.
  apply UB.
Qed.

(********************)
(* Self-adjointness *)
(********************)

(* Maybe change to "Hermitian?" *)

Definition id_adj := @id_adjoint_eq.

Lemma hadamard_adj : hadamard† == hadamard.
Proof. lma. Qed.

Lemma σx_adj : σx† == σx.
Proof. lma. Qed.

Lemma σy_adj : σy† == σy.
Proof. lma. Qed.

Lemma σz_adj : σz† == σz.
Proof. lma. Qed.

Lemma cnot_adj : cnot† == cnot.
Proof. lma. Qed.

Lemma swap_adj : swap† == swap.
Proof. lma. Qed.

Lemma control_adj : forall n (U : Square n), (control U)† == control (U†).
Proof.
  intros n U i j Hi Hj.
  unfold control, adjoint.
  rewrite Nat.eqb_sym.
  bdestruct (j =? i). 
  - subst.
    bdestruct (i <? n); bdestruct (n <=? i); try lia; simpl; lca.
  - rewrite 2 andb_false_r.
    rewrite andb_comm.
    rewrite (if_dist _ _ _ Cconj).
    rewrite Cconj_0.
    reflexivity.
Qed.

(* 
Lemma control_sa : forall (n : nat) (A : Square n), 
    A† == A -> (control A)† == (control A).
Proof.
  intros n A H.
  rewrite control_adjoint.
  intros i j Hi Hj.
  unfold control.
  simpl.
  rewrite <- H by lia.
  easy.
Qed. Add that control is a morphism? *)

Lemma phase_adj : forall ϕ, (phase_shift ϕ)† == phase_shift (-ϕ). 
Proof. 
  intros ϕ.
  unfold phase_shift, adjoint.
  by_cell; try lca.
  unfold Cexp, Cconj. 
  rewrite cos_neg, sin_neg.
  easy.
Qed.

Lemma braqubit0_adj : ∣0⟩⟨0∣† == ∣0⟩⟨0∣. Proof. lma. Qed.
Lemma braqubit1_adj : ∣1⟩⟨1∣† == ∣1⟩⟨1∣. Proof. lma. Qed.

Hint Rewrite hadamard_adj σx_adj σy_adj σz_adj cnot_adj swap_adj 
             braqubit1_adj braqubit0_adj control_adj phase_adj : M_db.

(* Rather use control_adjoint :
Hint Rewrite control_adj using (Msimpl; reflexivity) : M_db. *)


Lemma cnot_decomposition : ∣1⟩⟨1∣ ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 2 == cnot.
Proof. lma. Qed.                                               

Lemma notc_decomposition : σx ⊗ ∣1⟩⟨1∣ .+ I 2 ⊗ ∣0⟩⟨0∣ == notc.
Proof. lma. Qed.                                               


(*****************************)
(* Positive Semidefiniteness *)
(*****************************)

Definition positive_semidefinite {n} (A : Square n) : Prop :=
  forall (z : Vector n), fst ((z† × A × z) O O) >= 0.  

Lemma mat_equiv_element_property : forall {m n} (P : C -> Prop) (A B : Matrix m n) (i j : nat), 
  A == B -> lt i m -> lt j n -> P (A i j) -> P (B i j).
Proof. intros. rewrite <- H; easy. Qed.

Lemma positive_semidefinite_compat : forall {n} (A B : Square n), 
  A == B -> 
  positive_semidefinite A -> 
  positive_semidefinite B.
Proof.
  intros.
  unfold positive_semidefinite in *.
  intros z.
  eapply mat_equiv_element_property; try lia.
  rewrite <- H.
  reflexivity.
  apply H0.
Qed.

Lemma pure_psd : forall (n : nat) (ϕ : Vector n), positive_semidefinite (ϕ × ϕ†). 
Proof. 
  intros.
  unfold positive_semidefinite in *.
  intros z.
  eapply mat_equiv_element_property; try lia.
  - repeat rewrite Mmult_assoc by lia.
    remember (ϕ† × z) as ψ.
    repeat rewrite <- Mmult_assoc by lia.
    rewrite <- (adjoint_involutive ϕ).
    rewrite <- Mmult_adjoint.
    rewrite <- Heqψ.
    unfold Mmult. simpl.
    intros i j Hi Hj.
    rewrite Cplus_0_l.
    destruct i, j; try lia.
    unfold adjoint.
    subst.     
    reflexivity.
  - remember (ϕ† × z) as ψ.
    simpl.
    autorewrite with R_db.
    replace (fst (z 1%nat 0%nat) * fst (z 1%nat 0%nat))%R with ((fst (z 1%nat 0%nat))²) by easy. 
    replace (snd (z 1%nat 0%nat) * snd (z 1%nat 0%nat))%R with ((snd (z 1%nat 0%nat))²) by easy. 
    apply Rle_ge.
    apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Lemma braket0_psd : positive_semidefinite ∣0⟩⟨0∣.
Proof. apply pure_psd. Qed.

Lemma braket1_psd : positive_semidefinite ∣1⟩⟨1∣.
Proof. apply pure_psd. Qed.

Lemma H0_psd : positive_semidefinite (hadamard × ∣0⟩⟨0∣ × hadamard).
Proof.
  eapply positive_semidefinite_compat.
  - repeat rewrite Mmult_assoc.
    rewrite <- hadamard_adj at 2.
    rewrite <- Mmult_adjoint.
    repeat rewrite <- Mmult_assoc.
    reflexivity.
  - apply pure_psd.
Qed.


(*************************)
(* Pure and Mixed States *)
(*************************)

Notation Density n := (Matrix n n) (only parsing). 

Definition Classical {n} (ρ : Density n) := forall i j, i <> j -> ρ i j = 0.

Definition Pure_State_Vector {n} (φ : Vector n): Prop := 
  φ† × φ == I 1.

Definition Pure_State {n} (ρ : Density n) : Prop := 
  exists φ, Pure_State_Vector φ /\ ρ == φ × φ†.

(* Rewritten so Mix_S takes a C (to avoid mixing R and C). 
   Somewhat uglier, though *)
Inductive Mixed_State {n} : Matrix n n -> Prop :=
| Pure_S : forall ρ, Pure_State ρ -> Mixed_State ρ
| Mix_S : forall (p : C) ρ ρ1 ρ2, snd p = 0 ->
                             0 < fst p < 1 -> 
                             ρ == p .* ρ1 .+ (1 - p) .* ρ2 ->
                             Mixed_State ρ1 -> 
                             Mixed_State ρ2 ->
                             Mixed_State ρ.  

Lemma pure_state_compat : forall {n} (A B : Density n), 
  A == B ->  Pure_State A ->  Pure_State B.
Proof.
  intros.
  unfold  Pure_State in *.
  destruct H0 as [v HA].
  exists v. rewrite <- H. assumption.
Qed.

Add Parametric Morphism n : (@Pure_State n)
  with signature mat_equiv ==> iff as pure_state_mor.
Proof. intros; split; apply pure_state_compat; easy. Qed.


Lemma mixed_state_compat : forall {n} (A B : Density n), 
  A == B -> Mixed_State A ->  Mixed_State B.
Proof.
  intros n A B E MA. gen B.
  induction MA as [A | r A A1 A2].
  - intros. apply Pure_S. apply (pure_state_compat A); assumption.
  - intros.
    apply (Mix_S r _ A1 A2); trivial.
    rewrite <- E; assumption.
Qed.

Add Parametric Morphism n : (@Mixed_State n)
  with signature mat_equiv ==> iff as mixed_state_mor.
Proof. intros; split; apply mixed_state_compat; easy. Qed.

(* A convenient characterization: *)
Lemma mixed_state_cond : forall {n} (a b : R) (A B : Square n),
   0 <= a -> 
   0 <= b ->
   a + b = 1 -> 
   Mixed_State A ->
   Mixed_State B ->
   Mixed_State (a .* A .+ b .* B).
Proof.
  intros n a b A B Pa Pb Sab MA MB.
  destruct Pa; [destruct Pb|].
  - eapply (Mix_S (RtoC a) _ A B); trivial.
    + simpl. inversion Sab. lra.
    + replace (1-a) with (RtoC b) by (rewrite <- Sab; lca).
      reflexivity.
  - rewrite <- H0 in *.
    rewrite Cplus_0_r in Sab. rewrite Sab. 
    rewrite Mscale_0_l, Mplus_0_r, Mscale_1_l.
    easy.
  - rewrite <- H in *.
    rewrite Cplus_0_l in Sab. rewrite Sab. 
    rewrite Mscale_0_l, Mplus_0_l, Mscale_1_l.
    easy.
Qed.

Lemma pure0 : Pure_State ∣0⟩⟨0∣. 
Proof. exists ∣0⟩. split; lma. Qed.

Lemma pure1 : Pure_State ∣1⟩⟨1∣. 
Proof. exists ∣1⟩. split; lma. Qed.

Lemma pure_id1 : Pure_State (I 1).
Proof. exists (I 1). split; lma. Qed.

Lemma pure_dim1 : forall (ρ : Square 1), Pure_State ρ -> ρ == I  1.
Proof.
  intros ρ [φ [IP1 E]]. 
  apply Minv_flip in IP1.
  rewrite E; easy.
Qed.    
  
Lemma pure_state_kron : forall m n (ρ : Square m) (φ : Square n),
  Pure_State ρ -> Pure_State φ -> Pure_State (ρ ⊗ φ).
Proof.
  intros m n ρ φ [u [Pu Eρ]] [v [Pv Eφ]].
  exists (u ⊗ v).
  split.
  - unfold Pure_State_Vector in *. 
    restore_dims.
    Msimpl.
    rewrite Pu, Pv.
    lma.
  - rewrite Eρ, Eφ.
    restore_dims.
    Msimpl.
    reflexivity.
Qed.

Lemma mixed_state_kron : forall m n (ρ : Square m) (φ : Square n),
  Mixed_State ρ -> Mixed_State φ -> Mixed_State (ρ ⊗ φ).
Proof.
  intros m n ρ φ Mρ Mφ.
  induction Mρ.
  induction Mφ.
  - apply Pure_S. apply pure_state_kron; easy.
  - rewrite H2.
    rewrite kron_plus_dist_l.
    rewrite 2 Mscale_kron_dist_r. 
    eapply (Mix_S p); easy.
  - rewrite H1.
    rewrite kron_plus_dist_r.
    rewrite 2 Mscale_kron_dist_l. 
    eapply (Mix_S p); easy.
Qed.

Lemma pure_big_kron : forall (n : nat) (l : list (Square n)) (A : Square n),
  (forall i : nat, Pure_State (nth i l A)) -> 
  Pure_State (⨂ l).
Proof.
  induction l;  intros A H.
  - simpl. apply pure_id1.
  - simpl. apply pure_state_kron. apply (H O).
    apply (IHl A).    
    intros i.
    apply (H (S i)).
Qed.

Lemma mixed_big_kron : forall (n : nat) (l : list (Square n)) (A : Square n),
(forall i : nat, Mixed_State (nth i l A)) -> Mixed_State (⨂ l).
Proof.
  induction l;  intros A H.
  - simpl. constructor. apply pure_id1.
  - simpl. apply mixed_state_kron. apply (H O).
    eapply IHl.
    intros i.
    apply (H (S i)).
Qed.

Lemma pure_state_trace_1 : forall {n} (ρ : Density n), Pure_State ρ -> trace ρ = 1.
Proof.
  intros n ρ [u [Uu E]]. 
  unfold Pure_State_Vector in Uu.
  subst.
  rewrite E.
  clear -Uu.
  unfold trace.
  unfold Mmult, adjoint in *.
  simpl in *.
  erewrite Csum_eq_bounded; intros.
  rewrite (Uu O O) by lia. easy.
  simpl; lca.
Qed.

Lemma mixed_state_trace_1 : forall {n} (ρ : Density n), Mixed_State ρ -> trace ρ = 1.
Proof.
  intros n ρ M. 
  induction M. 
  - apply pure_state_trace_1. easy.
  - rewrite H1.
    rewrite trace_plus_dist.
    rewrite 2 trace_mult_dist.
    rewrite IHM1, IHM2.
    lca.
Qed.

(* The following two lemmas say that for any mixed states, the elements along the 
   diagonal are real numbers in the [0,1] interval. *)

Lemma mixed_state_diag_in01 : forall {n} (ρ : Density n) i , Mixed_State ρ -> 
                                                        lt i n ->
                                                        0 <= fst (ρ i i) <= 1.
Proof.
  intros n ρ i M L.
  induction M.
  - destruct H as [φ [IP1 Eρ]].
    rewrite Eρ; trivial.
    unfold Mmult, adjoint in *.
    simpl in *.
    rewrite Rplus_0_l.
    unfold Pure_State_Vector in IP1.
    specialize (IP1 O O Nat.lt_0_1 Nat.lt_0_1).
    unfold I in IP1. simpl in IP1. 
    apply f_equal with (f:=fst) in IP1.
    simpl in IP1. rewrite <- IP1.
    split.
    + unfold Rminus. rewrite <- Ropp_mult_distr_r. rewrite Ropp_involutive.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat; apply Rle_0_sqr.    
    + unfold Mmult.
      match goal with 
      [ |- ?x <= fst (Csum ?f ?m)] => specialize (Csum_member_le f n) as res
      end.
      simpl in *.
      unfold Rminus in *.
      rewrite <- Ropp_mult_distr_r.
      rewrite Ropp_mult_distr_l.
      apply res with (x := i); trivial. 
      intros x.
      unfold Rminus. rewrite <- Ropp_mult_distr_l. rewrite Ropp_involutive.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat; apply Rle_0_sqr.    
  - split.
    + assert (0 <= fst p * fst (ρ1 i i)).
        apply Rmult_le_pos; lra.
      assert (0 <= (1 - fst p) * fst (ρ2 i i)).
        apply Rmult_le_pos; lra.
      specialize (H1 i i L L). rewrite H1.
      unfold Mplus, scale. simpl.
      rewrite H; lra.
    + assert (fst p * fst (ρ1 i i) <= fst p). 
        rewrite <- Rmult_1_r.
        apply Rmult_le_compat_l; lra.
      assert ((1 - fst p) * fst (ρ2 i i) <= (1-fst p)). 
        rewrite <- Rmult_1_r.
        apply Rmult_le_compat_l; lra.
      specialize (H1 i i L L). rewrite H1.
      unfold Mplus, scale. simpl.
      rewrite H; lra.
Qed.

Lemma mixed_state_diag_real : forall {n} (ρ : Density n) i , 
  lt i n ->
  Mixed_State ρ -> 
  snd (ρ i i) = 0.
Proof.
  intros n ρ i L M.
  induction M.
  - unfold Pure_State in H. 
    destruct H as [φ [IP1 Eρ]].
    rewrite Eρ by lia.
    simpl; lra.
  - simpl.
    rewrite H1 by lia.
    unfold Mplus; simpl. 
    rewrite IHM1, IHM2.
    rewrite H; lra.
Qed.

Lemma mixed_dim1 : forall (ρ : Square 1), Mixed_State ρ -> ρ == I  1.
Proof.
  intros ρ M.
  induction M.
  - apply pure_dim1; trivial.
  - rewrite H1. rewrite IHM1, IHM2. lma.
Qed.  

(** Density matrices and superoperators **)

Definition Superoperator m n := Density m -> Density n.

Definition WF_Superoperator {m n} (f : Superoperator m n) := 
  (forall ρ, Mixed_State ρ -> Mixed_State (f ρ)).   

Definition super {m n} (M : Matrix m n) : Superoperator n m := fun ρ => 
  M × ρ × M†.

Lemma super_I : forall n ρ, super (I n) ρ == ρ.
Proof. intros. unfold super. Msimpl. reflexivity. Qed.

Add Parametric Morphism m n : (@super m n)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as super_mor.
Proof. intros. unfold super. rewrite H, H0. reflexivity. Qed.

Lemma super_outer_product : forall m (φ : Matrix m 1) (U : Matrix m m), 
    super U (outer_product φ φ) == outer_product (U × φ) (U × φ).
Proof.
  intros. unfold super, outer_product.
  Msimpl.
  repeat rewrite Mmult_assoc. reflexivity.
Qed.

Definition compose_super {m n p} (g : Superoperator n p) (f : Superoperator m n)
                      : Superoperator m p := fun ρ => g (f ρ).

Lemma compose_super_correct : forall {m n p} 
                              (g : Superoperator n p) (f : Superoperator m n),
      WF_Superoperator g -> 
      WF_Superoperator f ->
      WF_Superoperator (compose_super g f).
Proof.
  intros m n p g f pf_g pf_f.
  unfold WF_Superoperator.
  intros ρ mixed.
  unfold compose_super.
  apply pf_g. apply pf_f. auto.
Qed.

Definition sum_super {m n} (f g : Superoperator m n) : Superoperator m n :=
  fun ρ => 1/2 .* f ρ .+ (1 - 1/2) .* g ρ.

Lemma sum_super_correct : forall m n (f g : Superoperator m n),
      WF_Superoperator f -> WF_Superoperator g -> WF_Superoperator (sum_super f g).
Proof.
  intros m n f g wf_f wf_g ρ pf_ρ.
  unfold sum_super. 
  set (wf_f' := wf_f _ pf_ρ).
  set (wf_g' := wf_g _ pf_ρ).
  eapply (Mix_S (1/2) _ (f ρ) (g ρ)); auto. 
  simpl; lra.
  simpl; lra.
  reflexivity.
Qed.

(* Maybe we shouldn't call these superoperators? Neither is trace-preserving *)
Definition SZero {m n} : Superoperator m n := fun ρ => Zero.
Definition Splus {m n} (S T : Superoperator m n) : Superoperator m n :=
  fun ρ => S ρ .+ T ρ.

(* These are *)
Definition new0_op : Superoperator 1 2 := super ∣0⟩.
Definition new1_op : Superoperator 1 2 := super ∣1⟩.
Definition meas_op : Superoperator 2 2 := Splus (super ∣0⟩⟨0∣) (super ∣1⟩⟨1∣).
Definition discard_op : Superoperator 2 1 := Splus (super ⟨0∣) (super ⟨1∣).

Lemma pure_unitary : forall {n} (U ρ : Matrix n n), 
  WF_Unitary U -> Pure_State ρ -> Pure_State (super U ρ).
Proof.
  intros n U ρ H [φ [IP1 Eρ]].
  eapply pure_state_compat.
  unfold super. rewrite Eρ. easy.  
  exists (U × φ).
  split.
  - unfold Pure_State_Vector in *. 
    rewrite (Mmult_adjoint U φ).
    rewrite Mmult_assoc.
    rewrite <- (Mmult_assoc (U†)).
    unfold WF_Unitary in H.
    rewrite H, Mmult_1_l, IP1; easy.
  - unfold super.
    rewrite (Mmult_adjoint U φ).
    repeat rewrite Mmult_assoc.
    reflexivity.
Qed.    

Lemma mixed_unitary : forall {n} (U ρ : Matrix n n), 
  WF_Unitary U -> Mixed_State ρ -> Mixed_State (super U ρ).
Proof.
  intros n U ρ H M.
  induction M.
  + apply Pure_S.
    apply pure_unitary; trivial.
  + unfold WF_Unitary, super in *.
    rewrite H2.
    rewrite Mmult_plus_dist_l.
    rewrite Mmult_plus_dist_r.
    rewrite 2 Mscale_mult_dist_r.
    rewrite 2 Mscale_mult_dist_l.
    eapply (Mix_S p); easy. 
Qed.

Lemma super_unitary_correct : forall {n} (U : Matrix n n), 
  WF_Unitary U -> WF_Superoperator (super U).
Proof.
  intros n U H ρ Mρ.
  apply mixed_unitary; easy.
Qed.

Lemma compose_super_assoc : forall {m n p q}
      (f : Superoperator m n) (g : Superoperator n p) (h : Superoperator p q), 
      compose_super (compose_super f g) h
    = compose_super f (compose_super g h).
Proof. easy. Qed.


(* This is compose_super_correct 
Lemma WF_Superoperator_compose : forall m n p (s : Superoperator n p) (s' : Superoperator m n),
    WF_Superoperator s ->
    WF_Superoperator s' ->
    WF_Superoperator (compose_super s s').
Proof.
  unfold WF_Superoperator.
  intros m n p s s' H H0 ρ H1.
  unfold compose_super.
  apply H.
  apply H0.
  easy.
Qed.
*)

(****************************************)
(* Tests and Lemmas about swap matrices *)
(****************************************)

Lemma swap_spec : forall (q q' : Vector 2), swap × (q ⊗ q') == q' ⊗ q.
Proof. lma. Qed.

Hint Rewrite swap_spec : M_db.

Example swap_to_0_test_24 : forall (q0 q1 q2 q3 : Vector 2), 
  swap_to_0 4 2 × (q0 ⊗ q1 ⊗ q2 ⊗ q3) == (q2 ⊗ q1 ⊗ q0 ⊗ q3). 
Proof. 
  intros q0 q1 q2 q3.
  unfold swap_to_0, swap_to_0_aux.
  simpl.
  rewrite Mmult_assoc.
  repeat rewrite Mmult_assoc.
  rewrite (kron_assoc q0 q1).
  Msimpl.
  repeat rewrite kron_assoc.
  restore_dims.
  rewrite <- (kron_assoc q0 q2).
  Msimpl.
  rewrite (kron_assoc q2 q0).
  Msimpl.
  rewrite <- (kron_assoc q0).
  Msimpl.
  rewrite (kron_assoc q1 q0).
  reflexivity.
Qed.

Lemma swap_two_base : swap_two 2 1 0 == swap.
Proof. lma. Qed.

Lemma swap_second_two : swap_two 3 1 2 == I 2 ⊗ swap.
Proof. 
  unfold swap_two.
  simpl.
  rewrite (kron_1_r swap).
  reflexivity.
Qed.

Lemma swap_0_2 : swap_two 3 0 2 == (I 2 ⊗ swap) × (swap ⊗ I 2) × (I 2 ⊗ swap).
Proof.
  unfold swap_two.
  simpl.
  rewrite (kron_1_r (I 2 ⊗ swap)).
  reflexivity.
Qed.

(*
Proposition swap_to_0_spec : forall (q q0 : Matrix 2 1) (n k : nat) (l1 l2 : list (Matrix 2 1)), 
   length l1 = (k - 1)%nat ->
   length l2 = (n - k - 2)%nat ->   
   @Mmult (2^n) (2^n) 1 (swap_to_0 n k) (⨂ ([q0] ++ l1 ++ [q] ++ l2)) = 
     ⨂ ([q] ++ l1 ++ [q0] ++ l2).

Proposition swap_two_spec : forall (q q0 : Matrix 2 1) (n0 n1 n2 n k : nat) (l0 l1 l2 : list (Matrix 2 1)), 
   length l0 = n0 ->
   length l1 = n1 ->
   length l2 = n2 ->   
   n = (n0 + n1 + n2 + 2)%nat ->
   @Mmult (2^n) (2^n) 1 
     (swap_two n n0 (n0+n1+1)) (⨂ (l0 ++ [q0] ++ l1 ++ [q] ++ l2)) = 
     ⨂ (l0 ++ [q] ++ l1 ++ [q0] ++ l2).
*)


Example move_to_0_test_24 : forall (q0 q1 q2 q3 : Vector 2), 
  move_to_0 4 2 × (q0 ⊗ q1 ⊗ q2 ⊗ q3) == (q2 ⊗ q0 ⊗ q1 ⊗ q3). 
Proof.
  intros q0 q1 q2 q3.
  unfold move_to_0, move_to_0_aux.
  repeat rewrite Mmult_assoc.
  rewrite (kron_assoc q0 q1).
  simpl. Msimpl.
  rewrite <- kron_assoc.
  restore_dims.
  repeat rewrite (kron_assoc _ q1). 
  Msimpl.
  reflexivity.
Qed.

(* *)
