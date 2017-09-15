Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Denotation.
Require Import Arith.
Require Import Omega.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.


Hint Unfold I1 compose_super super swap_list swap_two denote_pat_in pad : Den_db.


Lemma Ex : 〚init true〛 I1 = (|1⟩⟨1| : Density 2).
Proof.
  repeat (autounfold with Den_db; simpl).
  autorewrite with M_db.
  reflexivity.
Qed.

Definition HOAS_Equiv {W1 W2} (b1 b2 : Box W1 W2) :=
  forall ρ, WF_Matrix (2^〚W1〛) (2^〚W1〛) ρ -> 〚b1〛 ρ = 〚b2〛 ρ.

Lemma unitary_transpose_id_qubit : forall (U : Unitary Qubit), forall ρ,
    WF_Matrix (2^〚Qubit〛) (2^〚Qubit〛) ρ -> 〚unitary_transpose U〛ρ = 〚@id_circ Qubit〛ρ.
Proof.
  intros U ρ pf_ρ.
  assert (unitary_U : is_unitary (denote_unitary U)) by apply unitary_gate_unitary.
  destruct unitary_U as [WF inv].
  repeat (autounfold with Den_db; simpl in *).
  autorewrite with M_db.
  repeat rewrite Mmult_assoc; try rewrite inv.
  repeat rewrite <- Mmult_assoc; try rewrite inv.
  autorewrite with M_db.
  reflexivity.
Qed.

Lemma unitary_transpose_id : forall W (U : Unitary W) (ρ : Density (2^〚W〛 )), 
  WF_Matrix (2^〚W〛) (2^〚W〛) ρ -> 〚unitary_transpose U〛 ρ = 〚@id_circ W〛 ρ.
Proof.
  intros W U ρ pf_ρ. 
  autorewrite with M_db.  
  repeat (unfold super, compose_super, denote_pat_in; simpl).
  repeat rewrite merge_nil_r.
  repeat rewrite size_fresh_ctx.
  repeat rewrite fresh_pat_empty.
  repeat rewrite map_num_wires_before.
  repeat rewrite swap_list_n_id.
  specialize (WF_unitary U); intros wf_U.
  specialize (unitary_gate_unitary U). unfold is_unitary. simpl. intros [_ unitary_U].
  autorewrite with M_db.
  rewrite mult_1_r. (* Rewrite implicit arguments *)
  autorewrite with M_db.
  repeat rewrite Mmult_assoc.
  rewrite unitary_U.
  repeat rewrite <- Mmult_assoc.
  rewrite unitary_U.
  autorewrite with M_db.
  reflexivity.
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
  destruct_m_eq; clra.
Qed.

Lemma even_bias : biased_coin (1/2) = fair_coin.
Proof. 
  unfold biased_coin, fair_coin.
  prep_matrix_equality; simpl.
  destruct_m_eq; clra.
Qed.

Lemma fair_toss : 〚coin_flip〛 I1  = fair_coin.
Proof.
  repeat (autounfold with Den_db; simpl).
  autorewrite with M_db.
  prep_matrix_equality.
  autounfold with M_db.
  simpl; autorewrite with C_db.
  destruct x, y; simpl; autorewrite with C_db; destruct_m_eq; clra.
Qed.

Definition EPR00 : Matrix 4 4 :=
  fun x y => match x, y with
             | 0, 0 => 1/2
             | 0, 3 => 1/2
             | 3, 0 => 1/2
             | 3, 3 => 1/2
             | _, _ => 0
             end.


Lemma cnot_eq : cnot = control pauli_x.
Proof.
  autounfold with M_db.
  simpl.
  prep_matrix_equality.
  repeat (try destruct x; try destruct y; autorewrite with C_db; trivial).
Qed.

(*
Opaque Nat.div.
Opaque Nat.modulo.
*)

Lemma divmod_eq : forall x y n z, fst (Nat.divmod x y n z) = (n + fst (Nat.divmod x y 0 z))%nat.
Proof.
  induction x.
  + intros. simpl. omega.
  + intros. simpl. 
    destruct z.
    rewrite IHx.
    rewrite IHx with (n:=1%nat).
    omega.
    rewrite IHx.
    reflexivity.
Qed.

(* Construct matrices full of evars *)
Ltac mk_evar t T := match goal with _ => evar (t : T) end.

Ltac evar_list n := 
  match n with 
  | O => constr:(@nil C)
  | S ?n' => let e := fresh "e" in
            let none := mk_evar e C in 
            let ls := evar_list n' in 
            constr:(e :: ls)
            
  end.

Ltac evar_list_2d m n := 
  match m with 
  | O => constr:(@nil (list C))
  | S ?m' => let ls := evar_list n in 
            let ls2d := evar_list_2d m' n in  
            constr:(ls :: ls2d)
  end.

Ltac evar_matrix m n := let ls2d := (evar_list_2d m n) 
                        in constr:(list2D_to_matrix ls2d).   

(* Unify A × B with list (list (evars)) *)
Ltac crunch_matrix := repeat match goal with
                             | [ H : C |- _ ] => unfold H; clear H
                             end; 
                      simpl;
                      unfold list2D_to_matrix;    
                      autounfold with M_db;
                      prep_matrix_equality;
                      simpl;
                      destruct_m_eq;
                      try rewrite divmod_eq; 
                      autorewrite with C_db; reflexivity.

Ltac reduce_aux M := 
  match M with 
  |  @Mmult ?m ?n ?o ?A ?B        => let M := evar_matrix m o in
                                    replace (@Mmult m n o A B) with M;
                                    [| crunch_matrix ] 
  end.

(* Find two basic matrices to multiply *)
Ltac find_smallest M := 
  match M with 
  | (@Mmult ?m ?n ?o ?A ?B) × ?C  => find_smallest (@Mmult m n o A B)
  | ?A                            => A
  end.                    

(* Replace smallest A × B with their product *)
Ltac reduce_matrix := match goal with [ |- ?M = _] => let M' := find_smallest M in
                                                              reduce_aux M' end;
                      repeat match goal with | [ H : C |- _ ] => unfold H; clear H end.

Ltac solve_matrix := repeat reduce_matrix; crunch_matrix.


Lemma bell00_eq :  〚bell00〛 I1  = EPR00.
Proof.
  repeat (simpl; autounfold with Den_db). 
  simpl. 
  rewrite <- cnot_eq.
  autorewrite with M_db.
  repeat rewrite <- Mmult_assoc.

(* solve_matrix: 50s ?, 36s, 34s, 32s *)
  solve_matrix.
Qed.


(* Slow approach #1: 1:25 ?, 1:00, 1:03, 1:00 *)
(*
  prep_matrix_equality.
  autounfold with M_db.
  simpl.
  autorewrite with C_db.
  destruct x. repeat (destruct y; autorewrite with C_db; trivial).
  destruct x. repeat (destruct y; autorewrite with C_db; trivial).
  destruct x. repeat (destruct y; autorewrite with C_db; trivial).
  destruct x. repeat (destruct y; autorewrite with C_db; trivial).
  repeat (destruct y; autorewrite with C_db; trivial).
  Qed.
*)

(* Slow approach #2: 5:32s *)
(*
  prep_matrix_equality.
  autounfold with M_db.
  destruct x. repeat (destruct y; simpl; autorewrite with C_db; trivial).
  destruct x. repeat (destruct y; simpl; autorewrite with C_db; trivial).
  destruct x. repeat (destruct y; simpl; autorewrite with C_db; trivial).
  destruct x. repeat (destruct y; simpl; autorewrite with C_db; trivial).
  repeat (destruct y; simpl; autorewrite with C_db; trivial).
Qed.
*)

Lemma teleport_direct_eq : forall (ρ : Density 2), 
  WF_Matrix 2 2 ρ -> 〚teleport_direct〛 ρ = ρ.
Proof.
  intros ρ H.
  unfold teleport_direct.
  unfold eq_ind_r, eq_ind.
  unfold eq_rect, eq_sym.
  repeat (autounfold with Den_db; simpl).
  simpl.

  idtac.

Admitted.

(*
Lemma teleport_eq : forall (ρ : Density 2), 
  WF_Matrix 2 2 ρ -> 〚teleport〛 ρ = ρ.
Proof.
  intros ρ WF.
  native_compute.
  vm_compute.
  simpl.
  unfold teleport.
  
  simpl.
  unfold compose_super, super, denote_pat_in.
  unfold swap_list, swap_list_aux.
  simpl.*)

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
  autorewrite with M_db.
  reflexivity.
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
  autorewrite with C_db.
  rewrite Cplus_comm. reflexivity.
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
  + autorewrite with M_db.
    repeat (unfold super, compose_super, denote_pat_in, swap_list, swap_two, I1; simpl).
    autorewrite with M_db.
    prep_matrix_equality. unfold biased_coin; simpl. 
    unfold Mmult, conj_transpose, ket0, ket1; simpl.
    destruct_Csolve; autorewrite with C_db; trivial. 
  + simpl in *.
    unfold eq_ind_r; simpl.
Abort.
