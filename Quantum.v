Require Import Program.
Require Import Psatz.
Require Import Omega.
Require Import Reals.
Require Import Bool.
Require Import Coquelicot.Complex.
Require Import Matrix.

(* Using our (complex, unbounded) matrices, their complex numbers *)

Open Scope R_scope.
Open Scope C_scope.
Open Scope matrix_scope.

Definition ket0 : Matrix 1 2 := 
  fun x y => match x, y with 
          | 0, 0 => 1
          | 0, 1 => 0
          | _, _ => 0
          end.

Definition ket1 : Matrix 1 2 := 
  fun x y => match x, y with 
          | 0, 0 => 0
          | 0, 1 => 1
          | _, _ => 0
          end.

Notation "|0⟩" := ket0.
Notation "|1⟩" := ket1.

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
                                  else A (x-n)%nat (y-n)%nat.
          

(* *)