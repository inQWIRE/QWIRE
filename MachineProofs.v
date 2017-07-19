Require Import MachineCircuits.
Require Import MachineExamples.
Require Import Denotation.
Require Import Arith.
Require Import Omega.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

Module VM.
Import M.
(* Verifying Properties of MachineExamples *)

(* Why can't I compose these? *)
Definition InitT := 〚init true〛 I1. 

Lemma Ex : InitT = |1⟩⟨1|.
Proof.
  intros.
  unfold InitT, I1. simpl.
  unfold apply_new1. simpl.
  unfold compose_super, super.
  unfold swap_list, swap_list_aux, swap_two. simpl.
  Msimpl.
Qed.

Definition fair_coin : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => 1/2
          | 1, 1 => 1/2
          | _, _ => 0
          end.

Definition biased_coin (c : C) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => (1 - c) 
          | 1, 1 => c
          | _, _ => 0
          end.

Lemma had_meas_toss : 〚hadamard_measure〛 |0⟩⟨0| = fair_coin.
Proof.
  simpl.
  repeat (unfold apply_U, apply_meas, swap_list, swap_two, pad; simpl).
  Msimpl.
  prep_matrix_equality.
  unfold compose_super, super, ket0, ket1, Mplus, Mmult, conj_transpose; simpl.
  Csimpl.
  destruct x, y; Csimpl; [ Csolve | Csolve | destruct_Csolve | destruct_Csolve].
Qed.

Lemma flip_toss : 〚coin_flip〛 I1  = fair_coin.
Proof.
  simpl.
  repeat (unfold apply_U, apply_meas, apply_new0, swap_list, swap_two, pad; simpl).
  Msimpl. 
  prep_matrix_equality.
  unfold compose_super, super, ket0, ket1, Mplus, Mmult, conj_transpose. 
  Csimpl.
  destruct x, y; Csimpl; [ Csolve | Csolve | destruct_Csolve | destruct_Csolve].
Qed.

Lemma unitary_trans_qubit_id : forall (U : Unitary Qubit) (ρ : Density 2), 
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


Lemma unitary_trans_id : forall W (U : Unitary W) (ρ : Density (2^〚W〛)%nat ), 
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

End VM.

(* *)
