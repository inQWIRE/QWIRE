Require Import Psatz.
Require Import Reals.

Require Export Matrix.

(* Using our (complex, unbounded) matrices, their complex numbers *)

(*******************************************)
(** * Quantum basis states *)
(*******************************************)

(* Maybe change to IF statements? *)
Definition qubit0 : Vector 2 := 
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 0 => C0
          | _, _ => C0
          end.
Definition qubit1 : Vector 2 := 
  fun x y => match x, y with 
          | 0, 0 => C0
          | 1, 0 => C1
          | _, _ => C0
          end.

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
                                                                       
Transparent bra.
Transparent ket.
Transparent qubit0.
Transparent qubit1.

Definition bool_to_ket (b : bool) : Matrix 2 1 := if b then ∣1⟩ else ∣0⟩.
                                                                     
Definition bool_to_matrix (b : bool) : Matrix 2 2 := if b then ∣1⟩⟨1∣ else ∣0⟩⟨0∣.

Definition bool_to_matrix' (b : bool) : Matrix 2 2 := fun x y =>
  match x, y with
  | 0, 0 => if b then 0 else 1
  | 1, 1 => if b then 1 else 0
  | _, _ => 0
  end.  
  
Lemma bool_to_matrix_eq : forall b, bool_to_matrix b = bool_to_matrix' b.
Proof. intros. destruct b; simpl; solve_matrix. Qed.

Lemma bool_to_ket_matrix_eq : forall b,
    outer_product (bool_to_ket b) (bool_to_ket b) = bool_to_matrix b.
Proof. unfold outer_product. destruct b; simpl; reflexivity. Qed.

Definition bools_to_matrix (l : list bool) : Square (2^(length l)) := 
  big_kron (map bool_to_matrix l).

Lemma ket_decomposition : forall (ψ : Vector 2), 
  WF_Matrix ψ ->
  ψ = (ψ 0%nat 0%nat) .* ∣ 0 ⟩ .+ (ψ 1%nat 0%nat) .* ∣ 1 ⟩.
Proof.
  intros.
  prep_matrix_equality.
  unfold scale, Mplus.
  destruct y as [|y']. 
  2:{ rewrite H; try lia. 
      unfold ket, qubit0, qubit1. simpl. 
      repeat (destruct x; try lca). }
  destruct x as [| [| n]]; unfold ket, qubit0, qubit1; simpl; try lca.  
  rewrite H; try lia.
  lca.
Qed. 

(****************)
(** * Unitaries *)
(****************)

Definition hadamard : Matrix 2 2 := 
  (fun x y => match x, y with
          | 0, 0 => (1 / √2)
          | 0, 1 => (1 / √2)
          | 1, 0 => (1 / √2)
          | 1, 1 => -(1 / √2)
          | _, _ => 0
          end).

Fixpoint hadamard_k (k : nat) : Matrix (2^k) (2^k):= 
  match k with
  | 0 => I 1
  | S k' => hadamard ⊗ hadamard_k k'
  end. 

Lemma hadamard_1 : hadamard_k 1 = hadamard.
Proof. apply kron_1_r. Qed.

(* Alternative definitions:
Definition pauli_x : Matrix 2 2 := fun x y => if x + y =? 1 then 1 else 0.
Definition pauli_y : Matrix 2 2 := fun x y => if x + y =? 1 then (-1) ^ x * Ci else 0.
Definition pauli_z : Matrix 2 2 := fun x y => if (x =? y) && (x <? 2) 
                                           then (-1) ^ x * Ci else 0.
*)

Definition σx : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 1 => C1
          | 1, 0 => C1
          | _, _ => C0
          end.

Definition σy : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 1 => -Ci
          | 1, 0 => Ci
          | _, _ => C0
          end.

Definition σz : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 1 => -C1
          | _, _ => C0
          end.
  
Definition control {n : nat} (A : Matrix n n) : Matrix (2*n) (2*n) :=
  fun x y => if (x <? n) && (y =? x) then 1 else 
          if (n <=? x) && (n <=? y) then A (x-n)%nat (y-n)%nat else 0.

(* Definition cnot := control pauli_x. *)
(* Direct definition makes our lives easier *)
(* Dimensions are given their current form for convenient
   kron_mixed_product applications *)
Definition cnot : Matrix (2*2) (2*2) :=
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 1 => C1
          | 2, 3 => C1
          | 3, 2 => C1
          | _, _ => C0
          end.          

Lemma cnot_eq : cnot = control σx.
Proof.
  unfold cnot, control, σx.
  solve_matrix.
Qed.

Definition notc : Matrix (2*2) (2*2) :=
  fun x y => match x, y with 
          | 1, 3 => 1%C
          | 3, 1 => 1%C
          | 0, 0 => 1%C
          | 2, 2 => 1%C
          | _, _ => 0%C
          end.          

(* Swap Matrices *)

Definition swap : Matrix (2*2) (2*2) :=
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 2 => C1
          | 2, 1 => C1
          | 3, 3 => C1
          | _, _ => C0
          end.

Hint Unfold qubit0 qubit1 hadamard σx σy σz control cnot swap bra ket : U_db.

(** ** Rotation Matrices *)
                              
(* Standard(?) definition, but it makes equivalence-checking a little annoying 
   because of a global phase.

Definition rotation (θ ϕ λ : R) : Matrix 2 2 :=
  fun x y => match x, y with
             | 0, 0 => (Cexp (-(ϕ + λ)/2)) * (cos (θ/2))
             | 0, 1 => - (Cexp (-(ϕ - λ)/2)) * (sin (θ/2))
             | 1, 0 => (Cexp ((ϕ - λ)/2)) * (sin (θ/2))
             | 1, 1 => (Cexp ((ϕ + λ)/2)) * (cos (θ/2))
             | _, _ => C0
             end.
*)
Definition rotation (θ ϕ λ : R) : Matrix 2 2 :=
  fun x y => match x, y with
             | 0, 0 => (cos (θ/2))
             | 0, 1 => - (Cexp λ) * (sin (θ/2))
             | 1, 0 => (Cexp ϕ) * (sin (θ/2))
             | 1, 1 => (Cexp (ϕ + λ)) * (cos (θ/2))
             | _, _ => C0
             end.

(* z_rotation lemmas are further down *)
Definition phase_shift (ϕ : R) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 1 => Cexp ϕ
          | _, _ => C0
          end.

(* Notation z_rotation := phase_shift. *)

Definition x_rotation  (θ : R) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => cos (θ / 2)
          | 0, 1 => -Ci * sin (θ / 2)
          | 1, 0 => -Ci * sin (θ / 2)
          | 1, 1 => cos (θ / 2)
          | _, _ => 0
          end.

Definition y_rotation  (θ : R) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => cos (θ / 2)
          | 0, 1 => - sin (θ / 2)
          | 1, 0 => sin (θ / 2)
          | 1, 1 => cos (θ / 2)
          | _, _ => 0
          end.

(* Shifted by i so x/y_rotation PI = σx/y :
Definition x_rotation  (θ : R) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => Ci * cos (θ / 2)
          | 0, 1 => sin (θ / 2)
          | 1, 0 => sin (θ / 2)
          | 1, 1 => Ci * cos (θ / 2)
          | _, _ => 0
          end.

Definition y_rotation  (θ : R) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => Ci * cos (θ / 2)
          | 0, 1 => -Ci * sin (θ / 2)
          | 1, 0 => Ci * sin (θ / 2)
          | 1, 1 => Ci * cos (θ / 2)
          | _, _ => 0
          end.
 *)

Lemma x_rotation_pi : x_rotation PI = -Ci .* σx.
Proof.
  unfold σx, x_rotation, scale.
  prep_matrix_equality.
  destruct_m_eq; 
  autorewrite with trig_db C_db;
  reflexivity. 
Qed.

Lemma y_rotation_pi : y_rotation PI = -Ci .* σy.
Proof.
  unfold σy, y_rotation, scale. 
  prep_matrix_equality.
  destruct_m_eq; 
  autorewrite with trig_db C_db;
  try reflexivity. 
Qed.

Lemma hadamard_rotation : rotation (PI/2) 0 PI = hadamard.
Proof.
  unfold hadamard, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity; 
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with R_db;
  autorewrite with trig_db;
  autorewrite with R_db;
  try reflexivity.
  all: rewrite Rmult_assoc;
       replace (/2 * /2)%R with (/4)%R by lra;
       repeat rewrite <- Rdiv_unfold;
       autorewrite with trig_db;
       rewrite sqrt2_div2;
       lra.
Qed.

Lemma pauli_x_rotation : rotation PI 0 PI = σx.
Proof.
  unfold σx, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity;
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with trig_db;
  lra.
Qed.

Lemma pauli_y_rotation : rotation PI (PI/2) (PI/2) = σy.
Proof. 
  unfold σy, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity;
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with trig_db;
  lra.
Qed.

Lemma pauli_z_rotation : rotation 0 0 PI = σz.
Proof. 
  unfold σz, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity;
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with R_db;
  autorewrite with trig_db;
  lra.
Qed.

Lemma Rx_rotation : forall θ, rotation θ (3*PI/2) (PI/2) = x_rotation θ.
Proof.
  intros.
  unfold rotation, x_rotation. 
  prep_matrix_equality.
  destruct_m_eq;
  autorewrite with C_db Cexp_db; reflexivity.
Qed.

Lemma Ry_rotation : forall θ, rotation θ 0 0 = y_rotation θ.
Proof. 
  intros.
  unfold rotation, y_rotation. 
  prep_matrix_equality.
  destruct_m_eq;
  autorewrite with C_db Cexp_db; try reflexivity.
Qed.


Lemma phase_shift_rotation : forall θ, rotation 0 0 θ = phase_shift θ.
Proof. 
  intros.
  unfold phase_shift, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity;
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with R_db;
  autorewrite with trig_db;
  lra.
Qed.

Lemma I_rotation : rotation 0 0 0 = I 2.
Proof.
  unfold I, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity;
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with R_db;
  autorewrite with trig_db;
  autorewrite with R_db;
  try reflexivity.
  bdestruct (x =? y); bdestruct (S (S x) <? 2); simpl; try reflexivity; lia.
  destruct (x =? y); destruct (S (S x) <? 2); reflexivity.
Qed.


(* Lemmas *)

(* Additional tactics for ∣0⟩, ∣1⟩, cnot and σx. *)

Lemma Mmult00 : ⟨0∣ × ∣0⟩ = I 1. Proof. solve_matrix. Qed.
Lemma Mmult01 : ⟨0∣ × ∣1⟩ = Zero. Proof. solve_matrix. Qed.
Lemma Mmult10 : ⟨1∣ × ∣0⟩ = Zero. Proof. solve_matrix. Qed.
Lemma Mmult11 : ⟨1∣ × ∣1⟩ = I 1. Proof. solve_matrix. Qed.

Lemma MmultX1 : σx × ∣1⟩ = ∣0⟩. Proof. solve_matrix. Qed.
Lemma Mmult1X : ⟨1∣ × σx = ⟨0∣. Proof. solve_matrix. Qed.
Lemma MmultX0 : σx × ∣0⟩ = ∣1⟩. Proof. solve_matrix. Qed.
Lemma Mmult0X : ⟨0∣ × σx = ⟨1∣. Proof. solve_matrix. Qed.

Lemma MmultXX : σx × σx = I 2. Proof. solve_matrix. Qed.
Lemma MmultYY : σy × σy = I 2. Proof. solve_matrix. Qed.
Lemma MmultZZ : σz × σz = I 2. Proof. solve_matrix. Qed.
Lemma MmultHH : hadamard × hadamard = I 2. Proof. solve_matrix. Qed.
Lemma Mplus01 : ∣0⟩⟨0∣ .+ ∣1⟩⟨1∣ = I 2. Proof. solve_matrix. Qed.
Lemma Mplus10 : ∣1⟩⟨1∣ .+ ∣0⟩⟨0∣ = I 2. Proof. solve_matrix. Qed.
                            
Lemma σx_on_right0 : forall (q : Vector 2), (q × ⟨0∣) × σx = q × ⟨1∣.
Proof. intros. rewrite Mmult_assoc, Mmult0X. reflexivity. Qed.

Lemma σx_on_right1 : forall (q : Vector 2), (q × ⟨1∣) × σx = q × ⟨0∣.
Proof. intros. rewrite Mmult_assoc, Mmult1X. reflexivity. Qed.

Lemma σx_on_left0 : forall (q : Matrix 1 2), σx × (∣0⟩ × q) = ∣1⟩ × q.
Proof. intros. rewrite <- Mmult_assoc, MmultX0. reflexivity. Qed.

Lemma σx_on_left1 : forall (q : Matrix 1 2), σx × (∣1⟩ × q) = ∣0⟩ × q.
Proof. intros. rewrite <- Mmult_assoc, MmultX1. reflexivity. Qed.

Lemma cancel00 : forall (q1 : Matrix 2 1) (q2 : Matrix 1 2), 
  WF_Matrix q2 ->
  (q1 × ⟨0∣) × (∣0⟩ × q2) = q1 × q2.
Proof. 
  intros. 
  rewrite Mmult_assoc. 
  rewrite <- (Mmult_assoc ⟨0∣).
  rewrite Mmult00.             
  Msimpl; reflexivity.
Qed.

Lemma cancel01 : forall (q1 : Matrix 2 1) (q2 : Matrix 1 2), 
  (q1 × ⟨0∣) × (∣1⟩ × q2) = Zero.
Proof. 
  intros. 
  rewrite Mmult_assoc. 
  rewrite <- (Mmult_assoc ⟨0∣).
  rewrite Mmult01.             
  Msimpl_light; reflexivity.
Qed.

Lemma cancel10 : forall (q1 : Matrix 2 1) (q2 : Matrix 1 2), 
  (q1 × ⟨1∣) × (∣0⟩ × q2) = Zero.
Proof. 
  intros. 
  rewrite Mmult_assoc. 
  rewrite <- (Mmult_assoc ⟨1∣).
  rewrite Mmult10.             
  Msimpl_light; reflexivity.
Qed.

Lemma cancel11 : forall (q1 : Matrix 2 1) (q2 : Matrix 1 2), 
  WF_Matrix q2 ->
  (q1 × ⟨1∣) × (∣1⟩ × q2) = q1 × q2.
Proof. 
  intros. 
  rewrite Mmult_assoc. 
  rewrite <- (Mmult_assoc ⟨1∣).
  rewrite Mmult11.             
  Msimpl; reflexivity.
Qed.

Hint Rewrite Mmult00 Mmult01 Mmult10 Mmult11 Mmult0X MmultX0 Mmult1X MmultX1 : Q_db.
Hint Rewrite MmultXX MmultYY MmultZZ MmultHH Mplus01 Mplus10 : Q_db.
Hint Rewrite σx_on_right0 σx_on_right1 σx_on_left0 σx_on_left1 : Q_db.
Hint Rewrite cancel00 cancel01 cancel10 cancel11 using (auto with wf_db) : Q_db.

Lemma swap_swap : swap × swap = I (2*2). Proof. solve_matrix. Qed.

Lemma swap_swap_r : forall (A : Matrix (2*2) (2*2)), 
  WF_Matrix A ->
  A × swap × swap = A.
Proof.
  intros.
  rewrite Mmult_assoc.
  rewrite swap_swap.
  Msimpl.
  reflexivity.
Qed.

Hint Rewrite swap_swap swap_swap_r using (auto 100 with wf_db): Q_db.



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

(*
Eval compute in ((swap_two 1 0 1) 0 0)%nat.
Eval compute in (print_matrix (swap_two 1 0 2)).
*)

(** Well Formedness of Quantum States and Unitaries **)

Lemma WF_bra0 : WF_Matrix ⟨0∣. Proof. show_wf. Qed. 
Lemma WF_bra1 : WF_Matrix ⟨1∣. Proof. show_wf. Qed.
Lemma WF_qubit0 : WF_Matrix ∣0⟩. Proof. show_wf. Qed.
Lemma WF_qubit1 : WF_Matrix ∣1⟩. Proof. show_wf. Qed.
Lemma WF_braqubit0 : WF_Matrix ∣0⟩⟨0∣. Proof. show_wf. Qed.
Lemma WF_braqubit1 : WF_Matrix ∣1⟩⟨1∣. Proof. show_wf. Qed.
Lemma WF_bool_to_ket : forall b, WF_Matrix (bool_to_ket b). 
Proof. destruct b; show_wf. Qed.
Lemma WF_bool_to_matrix : forall b, WF_Matrix (bool_to_matrix b).
Proof. destruct b; show_wf. Qed.
Lemma WF_bool_to_matrix' : forall b, WF_Matrix (bool_to_matrix' b).
Proof. destruct b; show_wf. Qed.

Lemma WF_bools_to_matrix : forall l, 
  @WF_Matrix (2^(length l)) (2^(length l))  (bools_to_matrix l).
Proof. 
  induction l; auto with wf_db.
  unfold bools_to_matrix in *; simpl.
  apply WF_kron; try rewrite map_length; try lia.
  apply WF_bool_to_matrix.
  apply IHl.
Qed.

Hint Resolve WF_bra0 WF_bra1 WF_qubit0 WF_qubit1 WF_braqubit0 WF_braqubit1 : wf_db.
Hint Resolve WF_bool_to_ket WF_bool_to_matrix WF_bool_to_matrix' : wf_db.
Hint Resolve WF_bools_to_matrix : wf_db.

Lemma WF_hadamard : WF_Matrix hadamard. Proof. show_wf. Qed.
Lemma WF_σx : WF_Matrix σx. Proof. show_wf. Qed.
Lemma WF_σy : WF_Matrix σy. Proof. show_wf. Qed.
Lemma WF_σz : WF_Matrix σz. Proof. show_wf. Qed.
Lemma WF_cnot : WF_Matrix cnot. Proof. show_wf. Qed.
Lemma WF_swap : WF_Matrix swap. Proof. show_wf. Qed.

Lemma WF_rotation : forall θ ϕ λ, WF_Matrix (rotation θ ϕ λ). Proof. intros. show_wf. Qed.
Lemma WF_phase : forall ϕ, WF_Matrix (phase_shift ϕ). Proof. intros. show_wf. Qed.


Lemma WF_control : forall (n : nat) (U : Matrix n n), 
      WF_Matrix U -> WF_Matrix (control U).
Proof.
  intros n U WFU.
  unfold control, WF_Matrix in *.
  intros x y [Hx | Hy];
  bdestruct (x <? n); bdestruct (y =? x); bdestruct (n <=? x); bdestruct (n <=? y);
    simpl; try reflexivity; try lia. 
  all: rewrite WFU; [reflexivity|lia].
Qed.

Hint Resolve WF_hadamard WF_σx WF_σy WF_σz WF_cnot WF_swap WF_phase : wf_db.
Hint Resolve WF_rotation : wf_db.

Hint Extern 2 (WF_Matrix (phase_shift _)) => apply WF_phase : wf_db.
Hint Extern 2 (WF_Matrix (control _)) => apply WF_control : wf_db.

(***************************)
(** Unitaries are unitary **)
(***************************)

(* For this section, we could just convert all single-qubit unitaries into their 
   rotation form and use rotation_unitary. *)

Definition WF_Unitary {n: nat} (U : Matrix n n): Prop :=
  WF_Matrix U /\ U † × U = I n.

Hint Unfold WF_Unitary : U_db.

(* More precise *)
(* Definition unitary_matrix' {n: nat} (A : Matrix n n): Prop := Minv A A†. *)

Lemma H_unitary : WF_Unitary hadamard.
Proof.
  split.
  show_wf.
  unfold Mmult, I.
  prep_matrix_equality.
  autounfold with U_db.
  destruct x as [| [|x]]; destruct y as [|[|y]]; simpl; autorewrite with C_db; 
    try reflexivity.
  replace ((S (S x) <? 2)) with false by reflexivity.
  rewrite andb_false_r.
  reflexivity.
Qed.

Lemma σx_unitary : WF_Unitary σx.
Proof. 
  split.
  show_wf.
  unfold Mmult, I.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try lca.
  simpl.
  replace ((S (S x) <? 2)) with false by reflexivity.
  rewrite andb_false_r.
  lca.
Qed.

Lemma σy_unitary : WF_Unitary σy.
Proof.
  split.
  show_wf.
  unfold Mmult, I.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try lca.
  simpl.
  replace ((S (S x) <? 2)) with false by reflexivity.
  rewrite andb_false_r.
  lca.
Qed.

Lemma σz_unitary : WF_Unitary σz.
Proof.
  split.
  show_wf.
  unfold Mmult, I.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try lca.
  simpl.
  replace ((S (S x) <? 2)) with false by reflexivity.
  rewrite andb_false_r.
  lca.
Qed.

Lemma phase_unitary : forall ϕ, @WF_Unitary 2 (phase_shift ϕ).
Proof.
  intros ϕ.
  split; [show_wf|].
  unfold Mmult, I, phase_shift, adjoint, Cexp.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try lca.
  - simpl.
    Csimpl.
    unfold Cconj, Cmult.
    simpl.
    unfold Rminus.
    rewrite Ropp_mult_distr_l.
    rewrite Ropp_involutive.
    replace (cos ϕ * cos ϕ)%R with ((cos ϕ)²) by easy.
    replace (sin ϕ * sin ϕ)%R with ((sin ϕ)²) by easy. 
    rewrite Rplus_comm.
    rewrite sin2_cos2.
    lca.
  - simpl. Csimpl.
    replace ((S (S x) <? 2)) with false by reflexivity.
    rewrite andb_false_r.
    lca.
Qed.

Lemma rotation_unitary : forall θ ϕ λ, @WF_Unitary 2 (rotation θ ϕ λ).
Proof.
  intros.
  split; [show_wf|].
  unfold Mmult, I, rotation, adjoint, Cexp.
  prep_matrix_equality.
  destruct_m_eq; try lca;
  unfold Cexp, Cconj;
  apply injective_projections; simpl;
  autorewrite with R_db;
  try lra.
  (* some general rewriting *)
  all: (repeat rewrite <- Rmult_assoc;
        repeat rewrite Ropp_mult_distr_l;
        repeat rewrite <- Rmult_plus_distr_r;
        repeat rewrite Rmult_assoc;
        repeat rewrite (Rmult_comm (cos (θ * / 2)));
        repeat rewrite (Rmult_comm (sin (θ * / 2)));
        repeat rewrite <- Rmult_assoc;
        repeat rewrite <- Rmult_plus_distr_r).
  (* all the cases are about the same; just setting up applications of
     cos_minus/sin_minus and simplifying *)
  all: repeat rewrite <- cos_minus.
  3: (rewrite (Rmult_comm (cos ϕ));
      rewrite <- (Ropp_mult_distr_l (sin ϕ));
      rewrite (Rmult_comm (sin ϕ));
      rewrite <- Rminus_unfold).
  5: (rewrite (Rmult_comm _ (cos ϕ));
      rewrite (Rmult_comm _ (sin ϕ));
      rewrite <- Ropp_mult_distr_r;
      rewrite <- Rminus_unfold).
  all: try rewrite <- sin_minus.
  all: autorewrite with R_db.
  all: repeat rewrite Rplus_opp_r.
  all: try (rewrite Ropp_plus_distr;
            repeat rewrite <- Rplus_assoc;
            rewrite Rplus_opp_r).
  all: try (rewrite (Rplus_comm ϕ λ);
            rewrite Rplus_assoc;
            rewrite Rplus_opp_r).
  all: (autorewrite with R_db;
        autorewrite with trig_db;
        autorewrite with R_db).
  all: try lra.
  all: try (replace (cos (θ * / 2) * cos (θ * / 2))%R with ((cos (θ * / 2))²) by easy;
            replace (sin (θ * / 2) * sin (θ * / 2))%R with ((sin (θ * / 2))²) by easy).
  1: rewrite Rplus_comm.
  all: try (rewrite sin2_cos2; reflexivity).
  (* two weird left-over cases *)
  all: (destruct ((x =? y) && (S (S x) <? 2)) eqn:E;
        try reflexivity).
  apply andb_prop in E as [_ E].
  apply Nat.ltb_lt in E; lia.
Qed.

Lemma x_rotation_unitary : forall θ, @WF_Unitary 2 (x_rotation θ).
Proof. intros. rewrite <- Rx_rotation. apply rotation_unitary. Qed.

Lemma y_rotation_unitary : forall θ, @WF_Unitary 2 (y_rotation θ).
Proof. intros. rewrite <- Ry_rotation. apply rotation_unitary. Qed.

Lemma control_unitary : forall n (A : Matrix n n), 
                          WF_Unitary A -> WF_Unitary (control A). 
Proof.
  intros n A H.
  destruct H as [WF U].
  split; auto with wf_db.
  unfold control, adjoint, Mmult, I.
  prep_matrix_equality.
  simpl.
  bdestructΩ (x =? y).
  - subst; simpl.
    rewrite Csum_sum.
    bdestructΩ (y <? n + (n + 0)).
    + bdestructΩ (n <=? y).
      * rewrite Csum_0_bounded. Csimpl.
        rewrite (Csum_eq _ (fun x => A x (y - n)%nat ^* * A x (y - n)%nat)).
        ++ unfold control, adjoint, Mmult, I in U.
           rewrite Nat.add_0_r.
           eapply (equal_f) in U. 
           eapply (equal_f) in U. 
           rewrite U.
           rewrite Nat.eqb_refl. simpl.
           bdestructΩ (y - n <? n).
           easy.
        ++ apply functional_extensionality. intros x.
           bdestructΩ (n + x <? n).
           bdestructΩ (n <=? n + x).
           rewrite minus_plus.
           easy.
        ++ intros x L.
           bdestructΩ (y =? x).
           rewrite andb_false_r.
           bdestructΩ (n <=? x).
           simpl. lca.
      * rewrite (Csum_unique 1). 
        rewrite Csum_0_bounded.
        ++ lca.
        ++ intros.
           rewrite andb_false_r.
           bdestructΩ (n + x <? n).
           simpl.
           lca.
        ++ exists y.
           repeat rewrite andb_false_r.
           split. easy.
           split. 
           rewrite Nat.eqb_refl.
           bdestructΩ (y <? n).
           simpl. lca.
           intros x Ne.
           bdestructΩ (y =? x ).
           repeat rewrite andb_false_r.
           lca.
    + rewrite 2 Csum_0_bounded; [lca| |].
      * intros x L.
        rewrite WF by (right; lia).
        bdestructΩ (n + x <? n).
        bdestructΩ (n <=? n + x).
        bdestructΩ (n <=? y).
        lca.
      * intros x L.
        bdestructΩ (y =? x).
        rewrite andb_false_r.
        bdestructΩ (n <=? x).
        simpl. lca.
  - simpl.
    rewrite Csum_sum.
    bdestructΩ (y <? n + (n + 0)).
    + bdestructΩ (n <=? y).
      * rewrite Csum_0_bounded. Csimpl.
        bdestructΩ (n <=? x).
        rewrite (Csum_eq _ (fun z => A z (x - n)%nat ^* * A z (y - n)%nat)).
        ++ unfold control, adjoint, Mmult, I in U.
           rewrite Nat.add_0_r.
           eapply (equal_f) in U. 
           eapply (equal_f) in U. 
           rewrite U.
           bdestructΩ (x - n =? y - n).
           simpl.
           easy.
        ++ apply functional_extensionality. intros z.
           bdestructΩ (n + z <? n).
           bdestructΩ (n <=? n + z).
           rewrite minus_plus.
           easy.
        ++ rewrite Csum_0. easy.
           intros z.
           bdestructΩ (n + z <? n).
           rewrite andb_false_r.
           Csimpl. easy. 
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
              bdestructΩ (x =? n + z); bdestructΩ (y =? n + z); rewrite andb_false_r; lca.
           ** intros z L.
              rewrite andb_false_r.
              bdestructΩ (x =? z); bdestructΩ (y =? z); rewrite andb_false_r; lca.
    + rewrite 2 Csum_0_bounded; [lca| |].
      * intros z L.
        bdestructΩ (n + z <? n). 
        bdestructΩ (n <=? n + z). 
        bdestructΩ (n <=? y).
        rewrite (WF _ (y-n)%nat) by (right; lia).
        lca.
      * intros z L.
        bdestructΩ (y =? z).
        rewrite andb_false_r.
        rewrite (WF _ (y-n)%nat) by (right; lia).
        destruct ((n <=? z) && (n <=? y)); lca.
Qed.

Lemma transpose_unitary : forall n (A : Matrix n n), WF_Unitary A -> WF_Unitary (A†).
Proof.
  intros. 
  simpl.
  split.
  + destruct H; auto with wf_db.
  + unfold WF_Unitary in *.
    rewrite adjoint_involutive.
    destruct H as [_ H].
    apply Minv_left in H as [_ S]. (* NB: admitted lemma *)
    assumption.
Qed.

Lemma cnot_unitary : WF_Unitary cnot.
Proof.
  split. 
  apply WF_cnot.
  unfold Mmult, I.
  prep_matrix_equality.
  do 4 (try destruct x; try destruct y; try lca).
  replace ((S (S (S (S x))) <? 4)) with (false) by reflexivity.
  rewrite andb_false_r.
  lca.
Qed.

Lemma id_unitary : forall n, WF_Unitary (I n). 
Proof.
  split.
  apply WF_I.
  unfold WF_Unitary.
  rewrite id_adjoint_eq.
  apply Mmult_1_l.
  apply WF_I.
Qed.

Lemma swap_unitary : WF_Unitary swap.
Proof. 
  split.
  apply WF_swap.
  unfold WF_Unitary, Mmult, I.
  prep_matrix_equality.
  do 4 (try destruct x; try destruct y; try lca).
  replace ((S (S (S (S x))) <? 4)) with (false) by reflexivity.
  rewrite andb_false_r.
  lca.
Qed.

Lemma zero_not_unitary : forall n, ~ (WF_Unitary (@Zero (2^n) (2^n))).
Proof.
  intros n.
  intros F.
  destruct F as [_ U].
  apply (f_equal2_inv 0 0)%nat in U.
  revert U.
  rewrite Mmult_0_r.
  unfold I, Zero.
  simpl.
  bdestruct (0 <? 2 ^ n).
  intros F. inversion F. lra.
  specialize (pow_positive 2 n) as P.
  lia.
Qed.

Lemma kron_unitary : forall {m n} (A : Matrix m m) (B : Matrix n n),
  WF_Unitary A -> WF_Unitary B -> WF_Unitary (A ⊗ B).
Proof.
  intros m n A B [WFA UA] [WFB UB].
  unfold WF_Unitary in *.
  split.
  auto with wf_db.
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
  intros n A B [WFA UA] [WFB UB].
  split.
  auto with wf_db.
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

Definition id_sa := id_adjoint_eq.

Lemma hadamard_sa : hadamard† = hadamard.
Proof.
  prep_matrix_equality.
  repeat (try destruct x; try destruct y; try lca; trivial).
Qed.

Lemma σx_sa : σx† = σx.
Proof. 
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try lca; trivial).
Qed.

Lemma σy_sa : σy† = σy.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try lca; trivial).
Qed.

Lemma σz_sa : σz† = σz.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try lca; trivial).
Qed.

Lemma cnot_sa : cnot† = cnot.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try lca; trivial).
Qed.

Lemma swap_sa : swap† = swap.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try lca; trivial).
Qed.

Lemma control_adjoint : forall n (U : Square n), (control U)† = control (U†).
Proof.
  intros n U.
  unfold control, adjoint.
  prep_matrix_equality.
  rewrite Nat.eqb_sym.
  bdestruct (y =? x). 
  - subst.
    bdestruct (x <? n); bdestruct (n <=? x); try lia; simpl; lca.
  - rewrite 2 andb_false_r.
    rewrite andb_comm.
    rewrite (if_dist _ _ _ Cconj).
    rewrite Cconj_0.
    reflexivity.
Qed.

Lemma control_sa : forall (n : nat) (A : Square n), 
    A† = A -> (control A)† = (control A).
Proof.
  intros n A H.
  rewrite control_adjoint.
  rewrite H.
  easy.
Qed.  

Lemma phase_adjoint : forall ϕ, (phase_shift ϕ)† = phase_shift (-ϕ). 
Proof.
  intros ϕ.
  unfold phase_shift, adjoint.
  prep_matrix_equality.
  destruct_m_eq; try lca.
  unfold Cexp, Cconj. 
  rewrite cos_neg, sin_neg.
  easy.
Qed.

(* x and y rotation adjoints aren't x and rotations? *)

Lemma rotation_adjoint : forall θ ϕ λ, (rotation θ ϕ λ)† = rotation (-θ) (-λ) (-ϕ).
Proof.
  intros.
  unfold rotation, adjoint.
  prep_matrix_equality.
  destruct_m_eq; try lca;
  unfold Cexp, Cconj;
  apply injective_projections; simpl;
  try rewrite <- Ropp_plus_distr;
  autorewrite with R_db;
  autorewrite with trig_db;
  try rewrite (Rplus_comm λ ϕ);
  autorewrite with R_db;
  reflexivity.
Qed.

Lemma braqubit0_sa : ∣0⟩⟨0∣† = ∣0⟩⟨0∣. Proof. lma. Qed.
Lemma braqubit1_sa : ∣1⟩⟨1∣† = ∣1⟩⟨1∣. Proof. lma. Qed.

Hint Rewrite hadamard_sa σx_sa σy_sa σz_sa cnot_sa swap_sa braqubit1_sa braqubit0_sa control_adjoint phase_adjoint rotation_adjoint : Q_db.

(* Rather use control_adjoint :
Hint Rewrite control_sa using (autorewrite with M_db; reflexivity) : M_db. *)

Lemma cnot_decomposition : ∣1⟩⟨1∣ ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 2 = cnot.
Proof. solve_matrix. Qed.                                               

Lemma notc_decomposition : σx ⊗ ∣1⟩⟨1∣ .+ I 2 ⊗ ∣0⟩⟨0∣ = notc.
Proof. solve_matrix. Qed.                                               

(*********************)
(** ** Phase Lemmas **)
(*********************)

Lemma phase_0 : phase_shift 0 = I 2.
Proof. 
  unfold phase_shift, I. 
  rewrite Cexp_0.
  solve_matrix.
Qed.

Lemma phase_2pi : phase_shift (2 * PI) = I 2.
  unfold phase_shift, I. 
  rewrite Cexp_2PI.
  solve_matrix.
Qed.

Lemma phase_pi : phase_shift PI = σz.
Proof.
  unfold phase_shift, σz.
  rewrite Cexp_PI.
  replace (RtoC (-1)) with (Copp (RtoC 1)) by lca.
  reflexivity.
Qed.

Lemma phase_neg_pi : phase_shift (-PI) = σz.
Proof.
  unfold phase_shift, σz.
  rewrite Cexp_neg.
  rewrite Cexp_PI.
  replace (/ -1) with (Copp (RtoC 1)) by lca.
  reflexivity.
Qed.

Lemma phase_mul : forall θ θ', phase_shift θ × phase_shift θ' = phase_shift (θ + θ').
Proof.
  intros. solve_matrix. rewrite Cexp_add. reflexivity.
Qed.  

(* Old, can probably remove *)
Lemma phase_PI4_m8 : forall k,
  phase_shift (IZR k * PI / 4) = phase_shift (IZR (k - 8) * PI / 4).
Proof.
  intros. unfold phase_shift. rewrite Cexp_PI4_m8. reflexivity.
Qed.

Lemma phase_mod_2PI : forall k, phase_shift (IZR k * PI) = phase_shift (IZR (k mod 2) * PI).
Proof.
  intros. unfold phase_shift. rewrite Cexp_mod_2PI. reflexivity.
Qed.

Lemma phase_mod_2PI_scaled : forall (k sc : Z), 
  sc <> 0%Z ->
  phase_shift (IZR k * PI / IZR sc) = phase_shift (IZR (k mod (2 * sc)) * PI / IZR sc).
Proof.
  intros. unfold phase_shift. rewrite Cexp_mod_2PI_scaled; easy. 
Qed.


Hint Rewrite phase_0 phase_2pi phase_pi phase_neg_pi : Q_db.


(*****************************)
(* Positive Semidefiniteness *)
(*****************************)

Definition positive_semidefinite {n} (A : Square n) : Prop :=
  forall (z : Vector n), WF_Matrix z -> fst ((z† × A × z) O O) >= 0.  

Lemma pure_psd : forall (n : nat) (ϕ : Vector n), (WF_Matrix ϕ) -> positive_semidefinite (ϕ × ϕ†). 
Proof.
  intros n ϕ WFϕ z WFZ.
  repeat rewrite Mmult_assoc.
  remember (ϕ† × z) as ψ.
  repeat rewrite <- Mmult_assoc.
  rewrite <- (adjoint_involutive _ _ ϕ).
  rewrite <- Mmult_adjoint.
  rewrite <- Heqψ.
  unfold Mmult. simpl.
  rewrite <- Ropp_mult_distr_l.
  rewrite Rplus_0_l.
  unfold Rminus.
  rewrite Ropp_involutive.
  replace (fst (z 1%nat 0%nat) * fst (z 1%nat 0%nat))%R with ((fst (z 1%nat 0%nat))²) by easy. 
  replace (snd (z 1%nat 0%nat) * snd (z 1%nat 0%nat))%R with ((snd (z 1%nat 0%nat))²) by easy. 
  apply Rle_ge.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Lemma braket0_psd : positive_semidefinite ∣0⟩⟨0∣.
Proof. apply pure_psd. auto with wf_db. Qed.

Lemma braket1_psd : positive_semidefinite ∣1⟩⟨1∣.
Proof. apply pure_psd. auto with wf_db. Qed.

Lemma H0_psd : positive_semidefinite (hadamard × ∣0⟩⟨0∣ × hadamard).
Proof.
  repeat rewrite Mmult_assoc.
  rewrite <- hadamard_sa at 2.
  rewrite <- Mmult_adjoint.
  repeat rewrite <- Mmult_assoc.
  apply pure_psd.
  auto with wf_db.
Qed.


(*************************)
(* Pure and Mixed States *)
(*************************)

Notation Density n := (Matrix n n) (only parsing). 

Definition Classical {n} (ρ : Density n) := forall i j, i <> j -> ρ i j = 0.

Definition Pure_State_Vector {n} (φ : Vector n): Prop := 
  WF_Matrix φ /\ φ† × φ = I  1.

Definition Pure_State {n} (ρ : Density n) : Prop := 
  exists φ, Pure_State_Vector φ /\ ρ = φ × φ†.

Inductive Mixed_State {n} : Matrix n n -> Prop :=
| Pure_S : forall ρ, Pure_State ρ -> Mixed_State ρ
| Mix_S : forall (p : R) ρ1 ρ2, 0 < p < 1 -> Mixed_State ρ1 -> Mixed_State ρ2 ->
                                       Mixed_State (p .* ρ1 .+ (1-p)%R .* ρ2).  

Lemma WF_Pure : forall {n} (ρ : Density n), Pure_State ρ -> WF_Matrix ρ.
Proof. intros. destruct H as [φ [[WFφ IP1] Eρ]]. rewrite Eρ. auto with wf_db. Qed.
Hint Resolve WF_Pure : wf_db.

Lemma WF_Mixed : forall {n} (ρ : Density n), Mixed_State ρ -> WF_Matrix ρ.
Proof. induction 1; auto with wf_db. Qed.
Hint Resolve WF_Mixed : wf_db.

Lemma pure0 : Pure_State ∣0⟩⟨0∣. 
Proof. exists ∣0⟩. intuition. split. auto with wf_db. solve_matrix. Qed.

Lemma pure1 : Pure_State ∣1⟩⟨1∣. 
Proof. exists ∣1⟩. intuition. split. auto with wf_db. solve_matrix. Qed.

Lemma pure_id1 : Pure_State (I  1).
Proof. exists (I  1). split. split. auto with wf_db. solve_matrix. solve_matrix. Qed.

Lemma pure_dim1 : forall (ρ : Square 1), Pure_State ρ -> ρ = I  1.
Proof.
  intros ρ [φ [[WFφ IP1] Eρ]]. 
  apply Minv_flip in IP1.
  rewrite Eρ; easy.
Qed.    
                              
Lemma pure_state_kron : forall m n (ρ : Square m) (φ : Square n),
  Pure_State ρ -> Pure_State φ -> Pure_State (ρ ⊗ φ).
Proof.
  intros m n ρ φ [u [[WFu Pu] Eρ]] [v [[WFv Pv] Eφ]].
  exists (u ⊗ v).
  split; [split |]. 
  - replace (S O) with (S O * S O)%nat by reflexivity.
    apply WF_kron; auto.
  - Msimpl. rewrite Pv, Pu. Msimpl. easy.
  - Msimpl. subst. easy.
Qed.

Lemma mixed_state_kron : forall m n (ρ : Square m) (φ : Square n),
  Mixed_State ρ -> Mixed_State φ -> Mixed_State (ρ ⊗ φ).
Proof.
  intros m n ρ φ Mρ Mφ.
  induction Mρ.
  induction Mφ.
  - apply Pure_S. apply pure_state_kron; easy.
  - rewrite kron_plus_distr_l.
    rewrite 2 Mscale_kron_dist_r.
    apply Mix_S; easy.
  - rewrite kron_plus_distr_r.
    rewrite 2 Mscale_kron_dist_l.
    apply Mix_S; easy.
Qed.

Lemma pure_state_trace_1 : forall {n} (ρ : Density n), Pure_State ρ -> trace ρ = 1.
Proof.
  intros n ρ [u [[WFu Uu] E]]. 
  subst.
  clear -Uu.
  unfold trace.
  unfold Mmult, adjoint in *.
  simpl in *.
  match goal with
    [H : ?f = ?g |- _] => assert (f O O = g O O) by (rewrite <- H; easy)
  end. 
  unfold I in H; simpl in H.
  rewrite <- H.
  apply Csum_eq.
  apply functional_extensionality.
  intros x.
  rewrite Cplus_0_l, Cmult_comm.
  easy.
Qed.

Lemma mixed_state_trace_1 : forall {n} (ρ : Density n), Mixed_State ρ -> trace ρ = 1.
Proof.
  intros n ρ H. 
  induction H. 
  - apply pure_state_trace_1. easy.
  - rewrite trace_plus_dist.
    rewrite 2 trace_mult_dist.
    rewrite IHMixed_State1, IHMixed_State2.
    lca.
Qed.

(* The following two lemmas say that for any mixed states, the elements along the 
   diagonal are real numbers in the [0,1] interval. *)

Lemma mixed_state_diag_in01 : forall {n} (ρ : Density n) i , Mixed_State ρ -> 
                                                        0 <= fst (ρ i i) <= 1.
Proof.
  intros.
  induction H.
  - destruct H as [φ [[WFφ IP1] Eρ]].
    destruct (lt_dec i n). 
    2: rewrite Eρ; unfold Mmult, adjoint; simpl; rewrite WFφ; simpl; [lra|lia].
    rewrite Eρ.
    unfold Mmult, adjoint in *.
    simpl in *.
    rewrite Rplus_0_l.
    match goal with
    [H : ?f = ?g |- _] => assert (f O O = g O O) by (rewrite <- H; easy)
    end. 
    unfold I in H. simpl in H. clear IP1.
    match goal with
    [ H : ?x = ?y |- _] => assert (H': fst x = fst y) by (rewrite H; easy); clear H
    end.
    simpl in H'.
    rewrite <- H'.    
    split.
    + unfold Rminus. rewrite <- Ropp_mult_distr_r. rewrite Ropp_involutive.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat; apply Rle_0_sqr.    
    + match goal with 
      [ |- ?x <= fst (Csum ?f ?m)] => specialize (Csum_member_le f n) as res
      end.
      simpl in *.
      unfold Rminus in *.
      Search (_ * - _)%R.
      rewrite <- Ropp_mult_distr_r.
      rewrite Ropp_mult_distr_l.
      apply res with (x := i); trivial. 
      intros x.
      unfold Rminus. rewrite <- Ropp_mult_distr_l. rewrite Ropp_involutive.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat; apply Rle_0_sqr.    
  - simpl.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rminus_0_r.
    split.
    assert (0 <= p * fst (ρ1 i i)).
      apply Rmult_le_pos; lra.
    assert (0 <= (1 - p) * fst (ρ2 i i)).
      apply Rmult_le_pos; lra.
    lra.
    assert (p * fst (ρ1 i i) <= p)%R. 
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l; lra.
    assert ((1 - p) * fst (ρ2 i i) <= (1-p))%R. 
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l; lra.
    lra.
Qed.

Lemma mixed_state_diag_real : forall {n} (ρ : Density n) i , Mixed_State ρ -> 
                                                        snd (ρ i i) = 0.
Proof.
  intros.
  induction H.
  + unfold Pure_State in H. 
  - destruct H as [φ [[WFφ IP1] Eρ]].
    rewrite Eρ.
    simpl. 
    lra.
  + simpl.
    rewrite IHMixed_State1, IHMixed_State2.
    repeat rewrite Rmult_0_r, Rmult_0_l.
    lra.
Qed.

Lemma mixed_dim1 : forall (ρ : Square 1), Mixed_State ρ -> ρ = I  1.
Proof.
  intros.  
  induction H.
  + apply pure_dim1; trivial.
  + rewrite IHMixed_State1, IHMixed_State2.
    prep_matrix_equality.
    lca.
Qed.  

(* Useful to be able to normalize vectors *)

Definition norm {n} (ψ : Vector n) : R :=
  sqrt (fst ((ψ† × ψ) O O)).

Definition normalize {n} (ψ : Vector n) :=
  / (norm ψ) .* ψ.

Lemma inner_product_ge_0 : forall {d} (ψ : Vector d),
  0 <= fst ((ψ† × ψ) O O).
Proof.
  intros.
  unfold Mmult, adjoint.
  apply Csum_ge_0.
  intro.
  rewrite <- Cmod_sqr.
  simpl.
  autorewrite with R_db.
  apply Rmult_le_pos; apply Cmod_ge_0.
Qed.

Lemma norm_scale : forall {n} c (v : Vector n), norm (c .* v) = ((Cmod c) * norm v)%R.
Proof.
  intros n c v.
  unfold norm.
  rewrite Mscale_adj.
  distribute_scale.
  unfold scale.
  simpl.
  replace (fst c * snd c + - snd c * fst c)%R with 0%R.
  autorewrite with R_db C_db.
  replace (fst c * fst c)%R with (fst c ^ 2)%R by lra.
  replace (snd c * snd c)%R with (snd c ^ 2)%R by lra.
  rewrite sqrt_mult_alt.
  reflexivity.
  apply Rplus_le_le_0_compat; apply pow2_ge_0.
  lra.
Qed.

(** Density matrices and superoperators **)

Definition Superoperator m n := Density m -> Density n.

Definition WF_Superoperator {m n} (f : Superoperator m n) := 
  (forall ρ, Mixed_State ρ -> Mixed_State (f ρ)).   

Definition super {m n} (M : Matrix m n) : Superoperator n m := fun ρ => 
  M × ρ × M†.

Lemma super_I : forall n ρ,
      WF_Matrix ρ ->
      super (I n) ρ = ρ.
Proof.
  intros.
  unfold super.
  Msimpl.
  reflexivity.
Qed.

Lemma WF_super : forall  m n (U : Matrix m n) (ρ : Square n), 
  WF_Matrix U -> WF_Matrix ρ -> WF_Matrix (super U ρ).
Proof.
  unfold super.
  auto with wf_db.
Qed.

Hint Resolve WF_super : wf_db.

Lemma super_outer_product : forall m (φ : Matrix m 1) (U : Matrix m m), 
    super U (outer_product φ φ) = outer_product (U × φ) (U × φ).
Proof.
  intros. unfold super, outer_product.
  autorewrite with M_db Q_db.
  repeat rewrite Mmult_assoc. reflexivity.
Qed.

Definition compose_super {m n p} (g : Superoperator n p) (f : Superoperator m n)
                      : Superoperator m p := fun ρ => g (f ρ).

Lemma WF_compose_super : forall m n p (g : Superoperator n p) (f : Superoperator m n) 
  (ρ : Square m), 
  WF_Matrix ρ ->
  (forall A, WF_Matrix A -> WF_Matrix (f A)) ->
  (forall A, WF_Matrix A -> WF_Matrix (g A)) ->
  WF_Matrix (compose_super g f ρ).
Proof.
  unfold compose_super.
  auto.
Qed.

Hint Resolve WF_compose_super : wf_db.


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
  fun ρ => (1/2)%R .* f ρ .+ (1 - 1/2)%R .* g ρ.

Lemma sum_super_correct : forall m n (f g : Superoperator m n),
      WF_Superoperator f -> WF_Superoperator g -> WF_Superoperator (sum_super f g).
Proof.
  intros m n f g wf_f wf_g ρ pf_ρ.
  unfold sum_super. 
  set (wf_f' := wf_f _ pf_ρ).
  set (wf_g' := wf_g _ pf_ρ).
  apply (Mix_S (1/2) (f ρ) (g ρ)); auto. 
  lra.
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
  intros n U ρ [WFU H] [φ [[WFφ IP1] Eρ]].
  rewrite Eρ.
  exists (U × φ).
  split.
  - split; auto with wf_db.
    rewrite (Mmult_adjoint U φ).
    rewrite Mmult_assoc.
    rewrite <- (Mmult_assoc (U†)).
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
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    rewrite 2 Mscale_mult_dist_r.
    rewrite 2 Mscale_mult_dist_l.
    apply Mix_S; trivial.
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

Lemma compose_super_eq : forall {m n p} (A : Matrix m n) (B : Matrix n p), 
      compose_super (super A) (super B) = super (A × B).
Proof.
  intros.
  unfold compose_super, super.
  apply functional_extensionality. intros ρ.
  rewrite Mmult_adjoint.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.


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

(**************)
(* Automation *)
(**************)

Ltac Qsimpl := try restore_dims; autorewrite with M_db_light M_db Q_db.


(****************************************)
(* Tests and Lemmas about swap matrices *)
(****************************************)

Lemma swap_spec : forall (q q' : Vector 2), WF_Matrix q -> 
                                       WF_Matrix q' ->
                                       swap × (q ⊗ q') = q' ⊗ q.
Proof.
  intros q q' WF WF'.
  solve_matrix.
  - destruct y. lca. 
    rewrite WF by lia. 
    rewrite (WF' O (S y)) by lia.
    lca.
  - destruct y. lca. 
    rewrite WF by lia. 
    rewrite (WF' O (S y)) by lia.
    lca.
  - destruct y. lca. 
    rewrite WF by lia. 
    rewrite (WF' 1%nat (S y)) by lia.
    lca.
  - destruct y. lca. 
    rewrite WF by lia. 
    rewrite (WF' 1%nat (S y)) by lia.
    lca.
Qed.  

Hint Rewrite swap_spec using (auto 100 with wf_db) : Q_db.

Example swap_to_0_test_24 : forall (q0 q1 q2 q3 : Vector 2), 
  WF_Matrix q0 -> WF_Matrix q1 -> WF_Matrix q2 -> WF_Matrix q3 ->
  swap_to_0 4 2 × (q0 ⊗ q1 ⊗ q2 ⊗ q3) = (q2 ⊗ q1 ⊗ q0 ⊗ q3). 
Proof.
  intros q0 q1 q2 q3 WF0 WF1 WF2 WF3.
  unfold swap_to_0, swap_to_0_aux.
  simpl.
  rewrite Mmult_assoc.
  repeat rewrite Mmult_assoc.
  rewrite (kron_assoc q0 q1). Qsimpl.
  replace 4%nat with (2*2)%nat by reflexivity.
  repeat rewrite kron_assoc.
  restore_dims.
  rewrite <- (kron_assoc q0 q2). Qsimpl.
  rewrite (kron_assoc q2). Qsimpl.
  rewrite <- kron_assoc. Qsimpl.
  repeat rewrite <- kron_assoc.
  reflexivity.
Qed.

Lemma swap_two_base : swap_two 2 1 0 = swap.
Proof. unfold swap_two. simpl. apply kron_1_r. Qed.

Lemma swap_second_two : swap_two 3 1 2 = I 2 ⊗ swap.
Proof.
  unfold swap_two.
  simpl.
  rewrite kron_1_r.
  reflexivity.
Qed.

Lemma swap_0_2 : swap_two 3 0 2 = (I 2 ⊗ swap) × (swap ⊗ I 2) × (I 2 ⊗ swap).
Proof.
  unfold swap_two.
  simpl.
  Qsimpl.
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
  WF_Matrix q0 -> WF_Matrix q1 -> WF_Matrix q2 -> WF_Matrix q3 ->
  move_to_0 4 2 × (q0 ⊗ q1 ⊗ q2 ⊗ q3) = (q2 ⊗ q0 ⊗ q1 ⊗ q3). 
Proof.
  intros q0 q1 q2 q3 WF0 WF1 WF2 WF3.
  unfold move_to_0, move_to_0_aux.
  repeat rewrite Mmult_assoc.
  rewrite (kron_assoc q0 q1).
  simpl.
  restore_dims.
  replace 4%nat with (2*2)%nat by reflexivity.
  Qsimpl.
  rewrite <- kron_assoc.
  restore_dims.
  repeat rewrite (kron_assoc _ q1). 
  Qsimpl.
  reflexivity.
Qed.

(* *)


