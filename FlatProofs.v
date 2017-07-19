Require Import FlatCircuits.
Require Import FlatExamples.
Require Import Denotation.
Require Import Program. 
Require Import List.
Require Import Arith.
Require Import Omega.
Import ListNotations.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

Import F.

Definition initT' := init true.
Definition InitT' := 〚init true〛 I1.  

Lemma Ex' : InitT' = (|1⟩⟨1| : Density 2).
Proof.
  unfold InitT', I1. 
  simpl.
  repeat (unfold compose_super, super, swap_list, swap_two, denote_pat_in). simpl.
  unfold swap_two; simpl.
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

Lemma flip_toss' : 〚coin_flip〛 I1  = fair_coin.
Proof.
  simpl.
  repeat (unfold compose_super, super, swap_list, swap_two, pad, 
          apply_new0, apply_U, apply_meas, denote_pat_in; simpl).
  Msimpl.
  prep_matrix_equality.
  unfold fair_coin, ket0, ket1, Mplus, Mmult, conj_transpose.
  Csimpl.
  destruct x, y; Csimpl; destruct_Csolve. Csolve.
Qed.

Definition Flat_Equiv {W1 W2} (b1 b2 : Flat_Box W1 W2) :=
  forall ρ, WF_Matrix (2^〚W1〛) (2^〚W1〛) ρ -> 〚b1〛 ρ = 〚b2〛 ρ.

Lemma unitary_transpose_qubit' : forall (U : Unitary Qubit), 
  Flat_Equiv (unitary_transpose U) id_circ.
Proof.
  intros U ρ pf_ρ.
  assert (unitary_U : is_unitary (denote_unitary U)) 
    by apply unitary_gate_unitary.
  destruct unitary_U as [WF inv].
  simpl in *.
  repeat (unfold apply_U, compose_super, super, swap_list, swap_two, pad, 
          denote_pat_in; simpl).
  Msimpl.
  repeat rewrite Mmult_assoc; rewrite inv.
  repeat rewrite <- Mmult_assoc; rewrite inv.
  Msimpl.
Qed.

Lemma unitary_transpose_id' : forall W (U : Unitary W) (ρ : Density (2^〚W〛 )), 
  WF_Matrix (2^〚W〛) (2^〚W〛) ρ -> 〚unitary_transpose U〛 ρ = 〚@id_circ W〛 ρ.
Proof.
  intros W U ρ pf_ρ. 
  Msimpl.
  unfold super, compose_super, denote_pat_in; simpl.
  repeat rewrite merge_nil_r.
  repeat rewrite size_fresh_ctx.
  repeat rewrite fresh_pat_empty.
  repeat rewrite map_num_wires_before.
  repeat rewrite swap_list_n_id.
  specialize (WF_unitary U); intros wf_U.
  specialize (unitary_gate_unitary U). unfold is_unitary. simpl. intros [_ unitary_U].
  rewrite conj_transpose_involutive. 
  rewrite mult_1_r. (* Rewrite implicit arguments *)
  Msimpl. 
  repeat rewrite Mmult_assoc.
  rewrite unitary_U.
  repeat rewrite <- Mmult_assoc.
  rewrite unitary_U.
  Msimpl.
Qed.

Lemma teleport_eq : forall (ρ : Density 2), 
  WF_Matrix 2 2 ρ -> 〚teleport_direct〛 ρ = ρ.
Proof.
  intros ρ H.
  simpl.
  repeat (unfold compose_super, super, swap_list, swap_two, pad, 
          apply_new0, apply_U, apply_meas, denote_pat_in; simpl).
  simpl.
(* Commented because slow: 
  repeat rewrite id_conj_transpose_eq.
  repeat rewrite Mmult_1_r.
  repeat rewrite Mmult_1_l.
  repeat (repeat rewrite kron_1_l; repeat rewrite kron_1_r; repeat rewrite Mmult_1_l;
   repeat rewrite Mmult_1_r; repeat rewrite id_conj_transpose_eq;
   repeat rewrite conj_transpose_involutive).
  Search "†".
  repeat rewrite kron_conj_transpose. *)
Admitted.




