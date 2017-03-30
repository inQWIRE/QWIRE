Require Import Program. 
Require Import Contexts.
Require Import TypedCircuits.
Require Import Examples.
Require Import List.
Require Import Arith.

Require Import Quantum.
Import ListNotations.

Open Scope circ_scope.

Class Denote source target :=
{
    correctness : target -> Type;
    denote : source -> target;
    denote_correct : forall (x : source), correctness (denote x)
}.
Notation "〚 s 〛" := (denote s) (at level 10).


Fixpoint num_wires (W : WType) : nat := 
  match W with
  | One => 0
  | Qubit => 1
  | Bit => 1
  | W1 ⊗ W2 => num_wires W1 + num_wires W2
  end.

Instance denote_WType : Denote WType nat :=
{|
    correctness := fun _ => True;
    denote := num_wires;
    denote_correct := fun _ => I
|}.

Fixpoint denote_unitary {W} (U : Unitary W) : Matrix (2^〚W〛) (2^〚W〛) :=
  match U with  
  | H => hadamard 
  | σx => pauli_x
  | σy => pauli_y
  | σz => pauli_z
  | CNOT => control pauli_x
  | TypedCircuits.control _ g => control (denote_unitary g)
  | TypedCircuits.bit_control _ g => control (denote_unitary g)  
  | TypedCircuits.transpose _ g => (denote_unitary g)†
  end. 
Instance denote_Unitary {W} : Denote (Unitary W) (Matrix (2^〚W〛) (2^〚W〛)) :=
{|
    correctness := unitary_matrix;
    denote := denote_unitary
|}.
Proof.
  induction x.
  + apply H_unitary.
  + apply σx_unitary.
  + apply σy_unitary.
  + apply σz_unitary.
  + apply cnot_unitary.
  + simpl. apply control_unitary; assumption. (* NB: Admitted lemma *)
  + simpl. apply control_unitary; assumption. (* NB: Admitted lemma *)
  + simpl.
    unfold unitary_matrix in *.
    rewrite conj_transpose_involutive.
    apply Minv_left in IHx as [_ S]. (* NB: Admitted lemma *)
    assumption.
Qed.


(*Definition denote_gate {W1 W2} (g : Gate W1 W2) : Matrix (2^(#W1)) (2^(#W2)).*)


(*Fixpoint denote_circuit {Γ : Ctx} {W : WType} (c : Flat_Circuit Γ W)*)

(* *)