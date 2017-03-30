Require Import Program.
Require Import Psatz.
Require Import Omega.
Require Import Reals.
Require Import Bool.
Require Export Coquelicot.Complex.
Require Export Matrix.

(* Using our (complex, unbounded) matrices, their complex numbers *)

Open Scope R_scope.
Open Scope C_scope.
Open Scope matrix_scope.

Definition ket0 : Matrix 2 1:= 
  fun x y => match x, y with 
          | 0, 0 => 1
          | 1, 0 => 0
          | _, _ => 0
          end.

Definition ket1 : Matrix 2 1 := 
  fun x y => match x, y with 
          | 0, 0 => 0
          | 1, 0 => 1
          | _, _ => 0
          end.
Definition ket (x : nat) : Matrix 2 1 := if x =? 0 then ket0 else ket1.

Notation "|0⟩" := ket0.
Notation "|1⟩" := ket1.
Notation "⟨0|" := ket0†.
Notation "⟨1|" := ket1†.
Notation "|0⟩⟨0|" := ( |0⟩×⟨0| ).
Notation "|1⟩⟨1|" := (|1⟩×⟨1|).

Notation "√ n" := (sqrt n) (at level 20).

Definition hadamard : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 0 => (1 / √2)
          | 0, 1 => (1 / √2)
          | 1, 0 => (1 / √2)
          | 1, 1 => -(1 / √2)
          | _, _ => 0
          end.

Fixpoint hadamard_k (k : nat) : Matrix (2^k) (2^k):= 
  match k with
  | 0 => Id 1
  | S k' => hadamard ⊗ hadamard_k k'
  end. 

Lemma hadamard_1 : hadamard_k 1 = hadamard.
Proof. apply kron_1_r. Qed.

Definition pauli_x : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 0 => 0
          | 0, 1 => 1
          | 1, 0 => 1
          | 1, 1 => 0
          | _, _ => 0
          end.

Definition pauli_y : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 0 => 0
          | 0, 1 => -Ci
          | 1, 0 => Ci
          | 1, 1 => 0
          | _, _ => 0
          end.

Definition pauli_z : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 0 => 1
          | 0, 1 => 0
          | 1, 0 => 0
          | 1, 1 => -1
          | _, _ => 0
          end.

Definition control {n : nat} (A : Matrix n n) : Matrix (2*n) (2*n) :=
  fun x y => if (x <? n) && (y <? n) then Id n x y 
          else if (n <=? x) && (n <=? y) then A (x-n)%nat (y-n)%nat
          else 0.

Definition cnot := control pauli_x.
          
(* Tactics *)

(* Would rather use something more basic than lra - but fourier and ring 
   aren't always up to the task *)
Ltac Rsimpl := 
  simpl;
  unfold Rminus;
  unfold Rdiv;
  repeat (
    try rewrite Ropp_0;
    try rewrite Ropp_involutive;
    try rewrite Rplus_0_l;
    try rewrite Rplus_0_r;
    try rewrite Rmult_0_l;
    try rewrite Rmult_0_r;
    try rewrite Rmult_1_l;
    try rewrite Rmult_1_r;
    try rewrite <- Ropp_mult_distr_l;
    try rewrite <- Ropp_mult_distr_r;
    try (rewrite Rinv_l; [|lra]);
    try (rewrite Rinv_r; [|lra]);
    try (rewrite sqrt_sqrt; [|lra])        
).

(* Seems like this could loop forever *)
Ltac group_radicals := 
  repeat (
  match goal with
    | [ |- context[(?r1 * √ ?r2)%R] ] => rewrite (Rmult_comm r1 (√r2)) 
    | [ |- context[(?r1 * (√ ?r2 * ?r3))%R] ] => rewrite <- (Rmult_assoc _ (√ r2) _)
    | [ |- context[((√?r * ?r1) + (√?r * ?r2))%R ] ] => 
        rewrite <- (Rmult_plus_distr_l r r1 r2)
  end).

Ltac Rsolve := repeat (try Rsimpl; try group_radicals); lra.

Ltac Csolve := eapply c_proj_eq; simpl; Rsolve.

Ltac well_formed N :=
  unfold WF_Matrix, N;
  intros x y [H | H];
  repeat (destruct x; try reflexivity; try omega);
  repeat (destruct y; try reflexivity; try omega).

(** Unitaries are well-formed **)

Lemma WF_hadamard : WF_Matrix hadamard. Proof. well_formed hadamard. Qed.
Lemma WF_pauli_x : WF_Matrix pauli_x. Proof. well_formed hadamard. Qed.
Lemma WF_pauli_y : WF_Matrix pauli_y. Proof. well_formed hadamard. Qed.
Lemma WF_pauli_z : WF_Matrix pauli_z. Proof. well_formed hadamard. Qed.

Lemma WF_control : forall {n} (U : Matrix n n), WF_Matrix U -> WF_Matrix (control U).
Proof.
  intros n U WFU.
  unfold control, WF_Matrix in *.
  intros x y [Hx | Hy].
  + replace (x <? n) with false by (symmetry; apply Nat.ltb_ge; omega). simpl.
    rewrite WFU.
    destruct (n <=? x), (n <=? y); reflexivity.
    left. omega.
  + replace (y <? n) with false by (symmetry; apply Nat.ltb_ge; omega). 
    rewrite andb_false_r.
    rewrite WFU.
    destruct (n <=? x), (n <=? y); reflexivity.
    right. omega.
Qed.

(** Unitaries are unitary **)

Definition unitary_matrix {n: nat} (A : Matrix n n): Prop :=
  A† × A = Id n.

(* More precise *)
Definition unitary_matrix' {n: nat} (A : Matrix n n): Prop := Minv A A†.

Lemma H_unitary : unitary_matrix hadamard.
Proof.
  unfold unitary_matrix, Minv.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold conj_transpose, Mmult, Id.
  simpl.
  destruct x as [|x]; destruct y as [|y].
  + Csolve.
  + destruct y; Csolve.
  + destruct x; Csolve.
  + destruct x, y; try Csolve.
    - replace ((S (S x) <? 2)) with (false) by reflexivity.
      rewrite andb_false_r.
      clra.
Qed.

Lemma σx_unitary : unitary_matrix pauli_x.
Proof.
  unfold unitary_matrix.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold conj_transpose, Mmult, Id.
  simpl.
  destruct x as [|x]; destruct y as [|y].
  + clra.
  + destruct y; clra.
  + destruct x; clra.
  + destruct x, y; try clra.
    - replace ((S (S x) <? 2)) with (false) by reflexivity.
      rewrite andb_false_r.
      clra.
Qed.

Lemma σy_unitary : unitary_matrix pauli_y.
Proof.
  unfold unitary_matrix.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold conj_transpose, Mmult, Id.
  simpl.
  destruct x as [|x]; destruct y as [|y].
  + clra.
  + destruct y; clra.
  + destruct x; clra.
  + destruct x, y; try clra.
    - replace ((S (S x) <? 2)) with (false) by reflexivity.
      rewrite andb_false_r.
      clra.
Qed.

Lemma σz_unitary : unitary_matrix pauli_z.
Proof.
  unfold unitary_matrix.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold conj_transpose, Mmult, Id.
  simpl.
  destruct x as [|x]; destruct y as [|y].
  + clra.
  + destruct y; clra.
  + destruct x; clra.
  + destruct x, y; try clra.
    - replace ((S (S x) <? 2)) with (false) by reflexivity.
      rewrite andb_false_r.
      clra.
Qed.

Lemma control_unitary : forall n (A : Matrix n n), 
                          unitary_matrix A -> unitary_matrix (control A). 
Proof.
  induction n.
  + intros A H.
    unfold control, unitary_matrix, conj_transpose, Mmult, Id.
    apply functional_extensionality; intros x.
    apply functional_extensionality; intros y.
    simpl.
    replace (x <? 0) with false by reflexivity.
    rewrite andb_false_r.
    reflexivity.

(*
  intros.
  unfold control.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold conj_transpose, Mmult, Id in *.
  destruct (x <? n) eqn:Ltxn, (y <? n) eqn:Ltyn.
  simpl.
*)

Admitted.

Lemma cnot_unitary : unitary_matrix cnot.
Proof.
  unfold unitary_matrix.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold conj_transpose, Mmult, Id.
  simpl.
  do 4 (try destruct x; try destruct y; try clra).
  replace ((S (S (S (S x))) <? 4)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma id_unitary : forall n, unitary_matrix (Id n). 
Proof.
  intros n.
  unfold unitary_matrix.
  rewrite id_conj_transpose_eq.
  apply Mmult_1_l.
  apply WF_Id.
Qed.


(* Density matrices and superoperators *)

Definition Density (n : nat) := Matrix n n.
Definition Superoperator m n := Density m -> Density n.

Definition super {m n} (M : Matrix m n) : Superoperator m n := fun ρ => 
  M × ρ × M†.

(* To do: correctness conditions for density matrices and superoperators *)

Definition new0 : Superoperator 2 2 := super |0⟩⟨0|.
Definition new1 : Superoperator 2 2 := super |1⟩⟨1|.
Definition meas : Superoperator 2 2 := fun ρ => super |0⟩⟨0| ρ .+ super |1⟩⟨1| ρ.
Definition discard : Superoperator 2 1 := fun ρ => super ⟨0| ρ .+ super ⟨1| ρ.

(* *)