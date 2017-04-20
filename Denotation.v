Require Import Program. 
Require Import Contexts.
Require Import HOASCircuits.
Require Import FlatCircuits.
Require Import List.
Require Import Arith.
Require Import Quantum.
Require Import Omega.
Import ListNotations.

Class Denote source target :=
{
    correctness : target -> Prop;
    denote : source -> target;
    denote_correct : forall (x : source), correctness (denote x)
}.
Notation "〚 s 〛" := (denote s) (at level 10).

(** Wire and Context Denotation **)


Instance Denote_WType : Denote WType nat :=
{|
    correctness := fun _ => True;
    denote := size_WType;
    denote_correct := fun _ => I
|}.


Instance Denote_Ctx : Denote Ctx nat :=
{|
    correctness := fun _ => True;
    denote := size_Ctx;
    denote_correct := fun _ => I
|}.
Instance Denote_OCtx : Denote OCtx nat :=
{|
    correctness := fun _ => True;
    denote := size_OCtx;
    denote_correct := fun _ => I
|}.

(** Unitary Denotation **)
Fixpoint denote_unitary {W} (U : Unitary W) : Square (2^〚W〛) :=
  match U with  
  | H => hadamard 
  | σx => pauli_x
  | σy => pauli_y
  | σz => pauli_z
  | CNOT => control pauli_x
  | ctrl _ g => control (denote_unitary g)
  | bit_ctrl _ g => control (denote_unitary g)  
  | Contexts.transpose _ g => (denote_unitary g)†
  end. 

Lemma unitary_wf : forall {W} (U : Unitary W), 
      WF_Matrix (2^〚W〛) (2^〚W〛) (denote_unitary U).
Proof.
  induction U.
  + apply WF_hadamard.
  + apply WF_pauli_x.
  + apply WF_pauli_y.
  + apply WF_pauli_z.
  + apply WF_control. apply WF_pauli_x.
  + simpl. apply WF_control. assumption.    
  + simpl. apply WF_control. assumption.    
  + simpl. apply WF_conj_transpose. assumption.    
Qed.
Hint Resolve unitary_wf.

Lemma unitary_gate_unitary : forall {W} (U : Unitary W), unitary_matrix (denote_unitary U).
Proof.
  induction U.
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
    apply Minv_left in IHU as [_ S]. (* NB: Admitted lemma *)
    assumption.
Qed.
Hint Resolve unitary_gate_unitary.

Instance Denote_Unitary {W} : Denote (Unitary W) (Square (2^〚W〛)) :=
{|
    correctness := fun m => WF_Matrix (2^〚W〛) (2^〚W〛) m /\ unitary_matrix m;
    denote := denote_unitary;
    denote_correct := fun U => conj (unitary_wf U) (unitary_gate_unitary U)
|}.

(** Gate Denotation *)

Definition denote_gate {W1 W2} (g : Gate W1 W2) : 
  Superoperator (2^〚W1〛) (2^〚W2〛) :=
  match g with
  | U _ u  => super (〚u〛)
  | init0 => new0_op 
  | init1 => new1_op
  | new0 => new0_op
  | new1 => new1_op 
  | meas => meas_op
  | discard => discard_op
  end.


Lemma denote_gate_correct : forall {W1} {W2} (g : Gate W1 W2), 
                            WF_Superoperator (denote_gate g). 
Proof.
  unfold WF_Superoperator.
Admitted.

Instance Denote_Gate {W1 W2} : Denote (Gate W1 W2) (Superoperator (2^〚W1〛) (2^〚W2〛)) :=
{|
    correctness := WF_Superoperator;
    denote := denote_gate;
    denote_correct := denote_gate_correct
|}.

(*
Eval compute in (denote_unitary CNOT 0%nat 0%nat).
Eval compute in (denote_unitary CNOT 0%nat 1%nat).
Eval compute in (denote_unitary CNOT 1%nat 0%nat).
Eval compute in (denote_unitary CNOT 1%nat 1%nat).
Eval compute in (denote_unitary CNOT 2%nat 2%nat).
Eval compute in (denote_unitary CNOT 2%nat 3%nat).
Eval compute in (denote_unitary CNOT 3%nat 2%nat).
Eval compute in (denote_unitary CNOT 3%nat 3%nat).
*)


(*
Eval simpl in (from_HOAS_Box hadamard_measure).
Eval compute in (from_HOAS_Box hadamard_measure).
Eval vm_compute in (from_HOAS_Box hadamard_measure).
*)

Definition zip_to (m n : nat) (l : list nat) := combine (seq m n) l.

Fixpoint swap_list_aux (n : nat) (l : list (nat * nat)) : Square  (2^n) :=
  match l with
  | nil => Id (2^n)
  | cons (a,b) xs => swap_two n a b × swap_list_aux n xs
  end. 

Definition swap_list (n : nat) (l : list nat) := swap_list_aux n (zip_to 0 n l). 

Lemma swap_list_swap : swap_list 2 [S O] = swap.
Proof.
  simpl.
  unfold swap_list, swap_list_aux.
  simpl.
  rewrite Mmult_1_r.
  apply swap_two_base. 
  unfold swap_two. simpl.
  rewrite kron_1_r.
  show_wf.
Qed.

Local Obligation Tactic := program_simpl; unify_pows_two; try omega.

(* Requires m < n *)
Definition pad {m} n (A : Square (2^m)) : Square (2^n) := (A ⊗ Id (2^ (n - m))).

Definition apply_U {m n} (U : Square (2^m)) (l : list nat) 
           : Superoperator (2^n) (2^n) :=
  let S := swap_list n l in 
  let SU := S × (pad n U) × S† in  
  super SU.

(* Moving new qubits to the end *)
Definition apply_new0 {n} : Superoperator (2^n) (2^(n+1)) :=
  super (Id (2^n) ⊗ |0⟩).

Definition apply_new1 {n} : Superoperator (2^n) (2^(n+1)) :=
  super (Id (2^n) ⊗ |1⟩).

Program Definition apply_discard {n} (k : nat) : Superoperator (2^n) (2^(n-1)) :=
  let S := swap_two n 0 k in 
  fun ρ => super ((⟨0| ⊗ Id (2^(n-1))) × S) ρ .+ super ((⟨1| ⊗ Id (2^(n-1))) × S) ρ.

(* Confirm tranposes are in the right place *)
Program Definition apply_meas {n} (k : nat) : Superoperator (2^n) (2^n) :=
  let S := swap_two n 0 k in 
  fun ρ => super (S × (|0⟩⟨0| ⊗ Id (2^(n-1))) × S†) ρ 
        .+ super (S × (|1⟩⟨1| ⊗ Id (2^(n-1))) × S†) ρ.

Definition super_Zero {m n} : Superoperator m n  :=
  fun _ => Zero _ _.

Definition apply_gate {n w1 w2} (g : Gate w1 w2) (l : list nat) 
           : Superoperator (2^n) (2^(n+〚w2〛-〚w1〛)) :=
  match g with 
  | U _ u   => match 〚w1〛 <=? n with
              | true => apply_U (denote_unitary u) l
              | false => super_Zero
              end
  | init0   => apply_new0 
  | init1   => apply_new1
  | new0    => apply_new0
  | new1    => apply_new1
  | meas    => match l with 
              | x :: _ => apply_meas x
              | _      => super_Zero
              end                               
  | discard => match l with 
              | x :: _ => apply_discard x
              | _      => super_Zero
              end
  end.

(* Denoting Machine Circuits *)

Require Import MachineCircuits.

Fixpoint denote_machine_circuit m n (c : Machine_Circuit m n) : Superoperator (2^m) (2^n) :=
  match c with 
  | m_output l         => super (swap_list n l)
  | m_gate w1 w2 l g c => compose_super (denote_machine_circuit (m+〚w2〛-〚w1〛) n c)
                                        (apply_gate g l)
  end.

(* Need a richer description of correctness because we need to refer to the
circuit in the condition, and we also need a stronger condition thatn WF_Machie_Circuit *)

Instance Denote_Machine_Circuit {m n} : Denote (Machine_Circuit m n) (Superoperator (2^m) (2^n)) :=
{| 
    denote      := fun C => denote_machine_circuit m n C;
    correctness := fun _ => True;
    denote_correct := fun _ => I
|}.

Require Import Reals.

Lemma WF_k0 : WF_Matrix 2 1 |0⟩. Proof. show_wf. Qed.
Hint Resolve WF_k0.
Lemma WF_k1 : WF_Matrix 2 1 |1⟩. Proof. show_wf. Qed.
Hint Resolve WF_k1.


(** Checking example circuits **)

Require Import MachineExamples.

Definition I1 := Id (2^0).
Lemma WF_I1 : WF_Matrix 1 1 I1.
Proof.
  unfold I1. apply WF_Id.
Qed.
Hint Resolve WF_I1.

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


Definition even_toss : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => 1/2
          | 1, 1 => 1/2
          | _, _ => 0
          end.


Ltac destruct1 :=
  match goal with
  | [ |- context[match ?x with 
                 | 0   => _
                 | S _ => _
                 end] ] => destruct x
  end.
Ltac destruct_Csolve := repeat (destruct1; try Csolve).

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
  specialize unitary_wf with U; intros wf.
  repeat (unfold apply_U, swap_list, swap_two, pad; simpl).
  Msimpl; auto. 
  unfold compose_super, super. Msimpl.
  rewrite conj_transpose_involutive.
  specialize (unitary_gate_unitary U). unfold unitary_matrix. simpl. intros H.
  repeat rewrite <- Mmult_assoc.
  rewrite H.
  repeat rewrite Mmult_assoc.
  rewrite H.
  Msimpl. 
Qed.  


Lemma swap_list_aux_id : forall n l, swap_list_aux n (combine l l) = Id (2 ^ n).
Proof.
  intros n l.
  induction l.
  + simpl. reflexivity.
  + simpl. rewrite IHl. unfold swap_two. rewrite <- beq_nat_refl. Msimpl.
Qed.

Lemma swap_list_n_id : forall n, swap_list n (seq 0 n) = Id (2^n).
Proof.
  intros.
  unfold swap_list.
  unfold zip_to.
  apply swap_list_aux_id.
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
  Msimpl.
  unfold super, compose_super.
  rewrite conj_transpose_involutive.
  specialize (unitary_gate_unitary U). unfold unitary_matrix. simpl. intros H. 
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

(* Flat Circuits *)  


Definition cross_list {A B} (ls1 : list A) (ls2 : list B) : list (A * B) :=
  let f := fun ls0 a => fold_left (fun ls0' b => (a,b)::ls0') ls2 ls0 in
  fold_left f ls1 [].

Lemma cross_nil_r : forall {A B} (ls : list A), cross_list ls ([] : list B) = [].
Proof.
  induction ls; simpl; auto.
Defined.

Lemma cross_list_distr_l : forall {A B} a (ls1 : list A) (ls2 : list B),
      length (cross_list (a :: ls1) ls2) 
    = (length ls2 + length (cross_list ls1 ls2))%nat.
Admitted.

Lemma cross_list_distr_r : forall {A B} b (ls1 : list A) (ls2 : list B),
      length (cross_list ls1 (b :: ls2))
    = (length ls1 + length (cross_list ls1 ls2))%nat.
Admitted.

Lemma length_cross_list : forall {A B} (ls1 : list A) (ls2 : list B),
      length (cross_list ls1 ls2) = (length ls1 * length ls2)%nat.
Proof.
  induction ls1 as [ | a ls1]; destruct ls2 as [ | b ls2]; simpl; try omega.
  - rewrite cross_nil_r. simpl. omega.
  - rewrite cross_list_distr_l. simpl. rewrite cross_list_distr_r.
    rewrite IHls1. 
    f_equal.
    f_equal.
    apply eq_trans with ((length ls1 * 1 + length ls1 * length ls2))%nat; try omega.
    rewrite <- Nat.mul_add_distr_l. simpl. reflexivity.
Defined.
Fixpoint get_interpretations (W : WType) : list (interpret W) :=
  match W with
  | One => [tt]
  | Tensor W1 W2 => cross_list (get_interpretations W1) (get_interpretations W2)
  | Qubit => [true;false]
  | Bit   => [true;false]
  end.


Lemma interp_nonzero : forall W, (0 < # (get_interpretations W))%nat.
Proof.
  induction W; simpl; try omega.
  rewrite length_cross_list.
  apply Nat.mul_pos_pos; auto. 
Defined.

Fixpoint sum_superoperators_with {m n} 
                 (s : Superoperator m n) (ls : list (Superoperator m n)) 
                 : Superoperator m n :=
  match ls with
  | []        => s
  | s' :: ls' => fun ρ => s ρ .+ sum_superoperators_with s' ls' ρ
  end.


Definition sum_over_interpretations {W m n} 
        (f : interpret W -> Superoperator m n)
        : Superoperator m n.
  set (vs := get_interpretations W).
  assert (H_neq : 0%nat <> length vs ). { apply lt_0_neq. apply interp_nonzero. }
  destruct vs as [ | v vs]; [absurd (0 <> 0); auto | ].
  exact (sum_superoperators_with (f v) (map f vs)).
Defined.


Definition discard_left : forall m n, Superoperator (2 ^ m * 2 ^ n) (2 ^ n).
  induction m; intros n ρ.
  - simpl in ρ. rewrite plus_0_r in ρ. exact ρ.
  - rewrite <- Nat.pow_add_r in ρ.
    apply (apply_discard 0) in ρ. 
    apply IHm.
    simpl in ρ. 
    rewrite <- minus_n_O in ρ.
    rewrite Nat.pow_add_r in ρ.
    exact ρ.
Defined.

Definition denote_lift {w m n} 
                      (f : interpret w -> Superoperator (2^m) (2^n))
                     : Superoperator (2 ^ 〚w〛 * 2^m) (2^n) :=
  let supers : interpret w -> Superoperator (2 ^ 〚w〛 * (2^m)) (2^n)
              := fun v ρ => f v (discard_left (〚w〛) m ρ) in
  sum_over_interpretations supers.

About apply_gate.
(* swap_list 〚Γ2'〛 : Square (2^Γ2') (2^Γ2') *)
Fixpoint denote_flat_circuit {Γ W} (C : Flat_Circuit Γ W) 
                 : Superoperator (2^〚Γ〛) (2^〚W〛) :=
  match C with
  | flat_output _ _ _ _ p => super (swap_list (〚W〛) (pat_to_list p))
  | flat_gate Γ Γ1 Γ1' Γ2 Γ2' W1 W2 W m1 m2 v1 v2 g p1 p2 C' => 
    let l1 := pat_to_list p1 in
    let l2 := pat_to_list p2 in
                  (* Superoperator (2^Γ2') (2^W) *)
    compose_super (denote_flat_circuit C') (
                  (* Superoperator (2^Γ2') (2^Γ2') *)
    compose_super (super (swap_list (〚Γ2'〛) l2)†) 
                  (* Superoperator (2^Γ) (2^(Γ + 〚W2〛-〚W1〛)) *)
                  (apply_gate g l1) )
  | flat_lift _ _ _ _ _ _ _ _ f => denote_lift (fun x => denote_flat_circuit (f x))
  end.



Instance Denote_Flat_Circuit {Γ W} : Denote (Flat_Circuit Γ W) (Superoperator (2^〚Γ〛) (2^〚W〛)) :=
{| 
    denote      := denote_flat_circuit;
    correctness := fun _ => True;
    denote_correct := fun _ => I
|}.

Definition denote_flat_box {W1 W2} (b : Flat_Box W1 W2) 
                           : Superoperator (2^〚W1〛) (2^〚W2〛) :=
  match b with
  | flat_box _ _ _ p C => let l := pat_to_list p in
                          compose_super (denote_flat_circuit C)
                                        (super (swap_list (〚W1〛) l)†)
                                        
  end.

Instance Denote_Flat_Box {W1 W2} 
         : Denote (Flat_Box W1 W2) (Superoperator (2^〚W1〛) (2^〚W2〛)) :=
{| 
    denote      := denote_flat_box;
    correctness := fun _ => True;
    denote_correct := fun _ => I
|}.

Require Import FlatExamples.

Definition initT' := FlatExamples.init true. Check initT'.
Definition InitT' := 〚init true〛 I1.  

Lemma Ex' : InitT' = (|1⟩⟨1| : Density 2).
Proof.
  unfold InitT', I1. 
  simpl.
  unfold compose_super, super, swap_list, swap_two. simpl.
  unfold swap_two, apply_new1, super; simpl.
  Msimpl.
Qed.

Lemma flip_toss' : 〚coin_flip〛 I1  = even_toss.
Proof.
  simpl.
  repeat (unfold compose_super, super, swap_list, swap_two, pad, apply_new0, apply_U, apply_meas; simpl).
  Msimpl. 
  prep_matrix_equality.
  unfold even_toss, ket0, ket1, Mplus, Mmult, conj_transpose.
  Csimpl.
  destruct x, y; Csimpl; destruct_Csolve. Csolve.
Qed.

Lemma unitary_trans_qubit' : forall (U : Unitary Qubit) (ρ : Density (2^〚Qubit〛)),
  WF_Matrix (2^〚Qubit〛) (2^〚Qubit〛) ρ -> 〚U_U_trans U〛 ρ = ρ.    
Proof.
  intros.
  simpl.
  assert (wf_U : WF_Matrix (2^〚Qubit〛) (2^〚Qubit〛) (denote_unitary U))
    by apply unitary_wf.
  simpl in wf_U.
  repeat (unfold apply_U, compose_super, super, swap_list, swap_two, pad; simpl).
  Msimpl.
  repeat rewrite Mmult_assoc.
  rewrite conj_transpose_involutive. 
  assert (unitary_U : unitary_matrix (denote_unitary U))
    by apply unitary_gate_unitary.
  unfold unitary_matrix in unitary_U.
  rewrite <- (Mmult_1_r ρ) at 2; auto.
  rewrite <- (Mmult_1_l ρ) at 2; auto.
  rewrite <- unitary_U.
  repeat rewrite Mmult_assoc. reflexivity.
Qed.

(* To Do:
Lemma unitary_trans_id' : forall W (U : Unitary W) (ρ : Density (2^〚W〛 )), 
  WF_Matrix (2^〚W〛) (2^〚W〛) ρ -> 〚U_U_trans U〛 ρ = ρ.
*)
