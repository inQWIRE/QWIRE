Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Denotation.
Require Import Arith.
Require Import Omega.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

Lemma Ex : 〚init true〛 I1 = (|1⟩⟨1| : Density 2).
Proof.
  unfold I1. 
  simpl.
  repeat (unfold compose_super, super, swap_list, swap_two, denote_pat_in; simpl).
  Msimpl.
Qed.

Definition HOAS_Equiv {W1 W2} (b1 b2 : Box W1 W2) :=
  forall ρ, WF_Matrix (2^〚W1〛) (2^〚W1〛) ρ -> 〚b1〛 ρ = 〚b2〛 ρ.

Lemma unitary_transpose_id_qubit : forall (U : Unitary Qubit), forall ρ,
    WF_Matrix (2^〚Qubit〛) (2^〚Qubit〛) ρ -> 〚unitary_transpose U〛ρ = 〚@id_circ Qubit〛ρ.
Proof.
  intros U ρ pf_ρ.
  assert (unitary_U : is_unitary (denote_unitary U)) 
    by apply unitary_gate_unitary.
  destruct unitary_U as [WF inv].
  simpl in *.
  repeat (unfold apply_U, compose_super, super, swap_list, swap_two, pad, denote_pat_in; simpl).
  Msimpl.
  repeat rewrite Mmult_assoc; try rewrite inv.
  repeat rewrite <- Mmult_assoc; try rewrite inv.
  Msimpl.
Qed.

Lemma unitary_transpose_id : forall W (U : Unitary W) (ρ : Density (2^〚W〛 )), 
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

(*
Definition flips_mat n : Density (2^1) := 
  fun x y => match x, y with
  | 0, 0 => 1 - (1 / (2^n))
  | 1, 1 => 1 / (2^n)
  | _, _ => 0
  end.
*)

Lemma bias1 : biased_coin 1 = |1⟩⟨1|.
Proof.
  unfold biased_coin.
  prep_matrix_equality; simpl.
  destruct_Csolve.
Qed.

Lemma even_bias : biased_coin (1/2) = fair_coin.
Proof. 
  unfold biased_coin, fair_coin.
  prep_matrix_equality; simpl.
  destruct_Csolve.
Qed.

Lemma fair_toss : 〚coin_flip〛 I1  = fair_coin.
Proof.
  repeat (unfold compose_super, super, swap_list, 
          swap_two, pad, apply_new0, apply_U, 
          apply_meas, denote_pat_in; simpl).
  Msimpl. 
  prep_matrix_equality.
  unfold fair_coin, ket0, ket1, Mplus, Mmult, conj_transpose.
  Csimpl.
  destruct x, y; Csimpl; destruct_Csolve. Csolve.
Qed.

(*
Print teleport_direct.
Print teleport.
*)

Lemma teleport_direct_eq : forall (ρ : Density 2), 
  WF_Matrix 2 2 ρ -> 〚teleport_direct〛 ρ = ρ.
Proof.
  intros ρ H.
  unfold teleport_direct.
  unfold eq_ind_r, eq_ind.
  unfold eq_rect, eq_sym.
Admitted.

Lemma teleport_eq : forall (ρ : Density 2), 
  WF_Matrix 2 2 ρ -> 〚teleport〛 ρ = ρ.
Proof.
  intros ρ WF.
  unfold teleport.
  
(*simpl.
  unfold compose_super, super, denote_pat_in.
  unfold swap_list, swap_list_aux.
  simpl.*)
Admitted.

(* Do these belong back in Denotation? *)
Program Lemma compose_correct : forall W1 W2 W3 (g : Box W2 W3) (f : Box W1 W2),
      〚inSeq f g〛 = compose_super (〚g〛) (〚f〛).
Admitted.

Lemma boxed_gate_correct : forall W1 W2 (g : Gate W1 W2) (ρ : Density (2^〚W1〛)) ,
      WF_Matrix (2^〚W1〛) (2^〚W1〛) ρ -> 〚boxed_gate g〛 ρ = 〚g〛 ρ.
Proof.
  intros W1 W2 g ρ wf_ρ. simpl.
  unfold denote_pat_in.
  repeat rewrite merge_nil_r.
  repeat rewrite size_fresh_ctx.
  repeat rewrite fresh_pat_empty.
  repeat rewrite map_num_wires_before.
  repeat rewrite swap_list_n_id.
  unfold super, compose_super.
  repeat rewrite mult_1_r.
  assert (wf_g : WF_Matrix (2^〚W2〛) (2^〚W2〛) (〚g〛 ρ)).
    generalize (WF_denote_gate 0 _ _ g ρ); intros.
    simpl in *. repeat rewrite mult_1_r in *. unfold denote_gate. apply (H wf_ρ).
  Msimpl.
Qed.



Lemma lift_meas_correct : forall (ρ : Density 2), WF_Matrix 2 2 ρ
      -> 〚lift_meas〛 ρ = 〚boxed_gate meas〛 ρ.
Proof.
  intros ρ wf_ρ.
  simpl.
  repeat (unfold denote_pat_in, swap_list, swap_two; simpl).
  Msimpl.
  unfold super, compose_super, Splus, SZero.
  Msimpl.
  rewrite braket0_conj_transpose, braket1_conj_transpose.
  prep_matrix_equality; simpl.
  unfold Mplus, Mmult, Id, conj_transpose, Zero. simpl.
  Csimpl. rewrite Cplus_comm. reflexivity.
Qed.

Lemma lift_eta_correct : forall (ρ : Density 2), WF_Matrix 2 2 ρ
      -> 〚lift_eta Bit〛 ρ = 〚@id_circ Bit〛 ρ.
Abort (* This is only true if ρ is a classical state *).
(* Proof.
  intros ρ wf_ρ.
  simpl.
  repeat (unfold denote_pat_in, swap_list, swap_two; simpl).
  Msimpl.
  unfold super, compose_super, Splus, SZero. 
  Msimpl.
  prep_matrix_equality.
  unfold Mmult, Mplus, Zero, conj_transpose, ket0, ket1. simpl.
  Csimpl.
  destruct x; Csimpl. 
  destruct y; Csimpl.
*)

Lemma flips_correct : forall n, 〚coin_flips n〛 I1 = biased_coin (2^n).
Proof.
  induction n; simpl.
  + Msimpl. repeat (unfold super, compose_super, denote_pat_in, swap_list, swap_two, I1; simpl).
    Msimpl.
    prep_matrix_equality. unfold biased_coin; simpl. 
    unfold Mmult, conj_transpose, ket0, ket1; simpl.
    Csimpl. 
    destruct_Csolve; Csimpl. 
  + simpl in *.
    unfold eq_ind_r; simpl.
Abort.
