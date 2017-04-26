Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import Contexts.
Require Import HOASCircuits.
Require Import MachineCircuits.
Require Import Omega.
Import ListNotations.
Open Scope list_scope.

Module M.

(*** Paper Examples ***)

(* Infix "↦" := m_box (at level 12, left associativity). *)
Notation "'gate' g 'on' l ; C" := (m_gate l g C) (at level 10, right associativity).
Notation "# l " := (length l) (at level 0).

Notation out l := (m_output l). 
Open Scope circ_scope.


(* Basic Circuits *)

Definition id_circ l : Machine_Circuit #l #l := out l.

Definition new_discard : Machine_Circuit 0 0 := 
  gate new0 on [];
  gate discard on [0];
  out [].

Definition init_discard : Machine_Circuit 0 0 :=
  gate init0 on [];
  gate meas on [0];
  gate discard on [0];
  out [].

Definition hadamard_measure : Machine_Circuit 1 1 :=
  gate H on [0];
  gate meas on [0];
  out [0].


(* Repeated Unitaries *)

Definition repeat_hadamard : Machine_Circuit 1 1 :=
  gate H on [0];
  gate H on [0];
  out [0].

Definition U_U_trans_qubit (U : Unitary Qubit): Machine_Circuit 1 1 :=
  gate U on [0];
  gate (transpose U) on [0];
  out [0].

Definition U_U_trans {W} (U : Unitary W): Machine_Circuit (size_WType W) (size_WType W) :=
  let l := seq 0 (size_WType W) in  
  gate U on l;
  gate (transpose U) on l;
  out l.


(* Deutsch's Algorithm *)

Parameter U_f : Unitary (Qubit ⊗ Qubit).
Definition deutsch : Machine_Circuit 0 1 :=
  gate init0 on [];
  gate H on [0];
  gate init1 on [];
  gate H on [1];
  gate U_f on [0;1];
  gate meas on [0];
  gate discard on [0];
  out [1].


(* Teleport *)

Definition init (b : bool) : Machine_Circuit 0 1:=
  if b then (gate init1 on []; out [0]) 
       else (gate init0 on []; out [0]).

(** Teleport **)

Definition bell00 : Machine_Circuit 0 2 :=
  gate init0 on [];
  gate init0 on [];
  gate H on [0];
  gate CNOT on [0;1];
  out [0;1].

Definition alice : Machine_Circuit 2 2 :=
  gate CNOT on [0;1];
  gate H on [0];
  gate meas on [0];
  gate meas on [1];
  out [0;1].

Definition bob : Machine_Circuit 3 1 :=
  gate (bit_ctrl σx) on [1;2];
  gate (bit_ctrl σz) on [0;2];
  gate discard on [1];
  gate discard on [0]; 
  out [2].

Definition teleport : Machine_Circuit 1 1 :=
  (* bell00 *) (* shifted from above *)
  gate init0 on [];
  gate init0 on [];
  gate H on [1];
  gate CNOT on [1;2];
  
  (* alice *)
  gate CNOT on [0;1];
  gate H on [0];
  gate meas on [0];
  gate meas on [1];

  (* bob *)  
  gate (bit_ctrl σx) on [1;2];
  gate (bit_ctrl σz) on [0;2];
  gate discard on [1];
  gate discard on [0]; 
  out [0].


(* Coin Flip *)

Definition coin_flip : Machine_Circuit 0 1 :=
  gate init0 on [];
  gate H on [0];
  gate meas on [0];
  out [0].


(* Old teleport for IO-less circuits.
Definition teleport : Machine_Circuit := bell00 ↦ alice ↦ bob.

Print teleport.
Eval compute in teleport.
*)

Close Scope circ_scope.

(* *)

Require Import Denotation.

(* Verifying Properties of MachineExamples *)

(* Why can't I compose these? *)
Definition InitT := 〚M.init true〛 I1. 

Lemma Ex : InitT = |1⟩⟨1|.
Proof.
  intros.
  unfold InitT, I1. simpl.
  unfold apply_new1. simpl.
  unfold compose_super, super.
  unfold swap_list, swap_list_aux, swap_two. simpl.
  Msimpl.
Qed.




Lemma had_meas_toss : 〚hadamard_measure〛 |0⟩⟨0| = even_toss.
Proof.
  simpl.
  repeat (unfold apply_U, apply_meas, swap_list, swap_two, pad; simpl).
  Msimpl.
  prep_matrix_equality.
  unfold compose_super, super, ket0, ket1, Mplus, Mmult, conj_transpose; simpl.
  Csimpl.
  destruct x, y; Csimpl; [ Csolve | Csolve | destruct_Csolve | destruct_Csolve].
Qed.

Definition FLIP : Square (2^1) := 〚coin_flip〛 I1.
Lemma flip_toss : 〚coin_flip〛 I1  = even_toss.
Proof.
  simpl.
  repeat (unfold apply_U, apply_meas, apply_new0, swap_list, swap_two, pad; simpl).
  Msimpl. 
  prep_matrix_equality.
  unfold compose_super, super, ket0, ket1, Mplus, Mmult, conj_transpose. 
  Csimpl.
  destruct x, y; Csimpl; [ Csolve | Csolve | destruct_Csolve | destruct_Csolve].
Qed.

Lemma unitary_trans_qubit_id : forall (U : Unitary Qubit) (ρ : Density (2^1)), 
  WF_Matrix 2 2 ρ -> 〚U_U_trans_qubit U〛 ρ = ρ.
Proof.
  intros U ρ WF.
  simpl.
  specialize WF_unitary with U; intros wf.
  repeat (unfold apply_U, swap_list, swap_two, pad; simpl).
  Msimpl; auto. 
  unfold compose_super, super. Msimpl.
  specialize (unitary_gate_unitary U). unfold is_unitary. simpl. intros [_ H].
  repeat rewrite <- Mmult_assoc.
  rewrite H.
  repeat rewrite Mmult_assoc.
  rewrite H.
  Msimpl. 
Qed.  

Lemma unitary_trans_id : forall W (U : Unitary W) (ρ : Density (2^〚W〛 )), 
  WF_Matrix (2^〚W〛) (2^〚W〛) ρ -> 〚U_U_trans U〛 ρ = ρ.
Proof.
  intros W U ρ WF.
  simpl.
  unfold U_U_trans. 
  rewrite leb_correct; try omega.
  rewrite leb_correct; try omega.
  unfold apply_U.
  replace (size_WType W + size_WType W - size_WType W)%nat with (size_WType W) by omega.
  rewrite swap_list_n_id.
  unfold pad.
  replace (size_WType W - size_WType W)%nat with O by omega.   
  specialize (unitary_gate_unitary U). unfold is_unitary. simpl. intros [WFU H]. 
  Msimpl.
  unfold super, compose_super.
  rewrite conj_transpose_involutive.
  Msimpl.
  repeat rewrite <- Mmult_assoc. 
  rewrite H.
  repeat rewrite Mmult_assoc.
  rewrite H.
  Msimpl.
Qed.  

(* Corresponds to f(0) = 1, f(1) = 0. See Watrous p25. *)
Definition f10 : Matrix 2 2 := fun x y => 
  match x, y with
  | 0, 1 => 1 
  | 1, 0 => 1
  | 2, 2 => 1
  | 3, 3 => 1
  | _, _ => 0
  end.


(*
Lemma deutsch_odd : denote_unitary U_f = f10 -> 〚deutsch〛(Id 1) = |1⟩⟨1| .
Proof.
  intros H.
  simpl.
  rewrite H. clear H.
  repeat (unfold apply_U, apply_discard, apply_meas, apply_new1, swap_list, swap_two, pad; simpl).
  Msimpl. 
  prep_matrix_equality.
  unfold super, ket0, ket1. simpl.
  unfold Mplus, conj_transpose. simpl.
  unfold Mmult. 
  simpl. (* Hangs *)
  destruct x, y; simpl.
  + Csolve.
  + destruct y; Csolve.
  + destruct x; Csolve.
  + destruct x. destruct y; Csolve. 
    Csolve.
*)

End M.


