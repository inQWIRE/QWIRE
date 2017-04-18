Require Import Program. 
Require Import Contexts.
Require Import TypedCircuits.
Require Import FlatCircuits.
Require Import List.
Require Import Arith.
Require Import UQuantum. (* Less typed! *)
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

Instance denote_WType : Denote WType nat :=
{|
    correctness := fun _ => True;
    denote := num_wires;
    denote_correct := fun _ => I
|}.

Fixpoint num_elts (Γ : Ctx) : nat :=
  match Γ with
  | [] => 0
  | None :: Γ' => num_elts Γ'
  | Some _ :: Γ' => S (num_elts Γ')
  end.
Definition num_elts_o (Γ : OCtx) : nat :=
  match Γ with
  | Invalid => 0
  | Valid Γ' => num_elts Γ'
  end.


Instance denote_Ctx : Denote Ctx nat :=
{|
    correctness := fun _ => True;
    denote := num_elts;
    denote_correct := fun _ => I
|}.
Instance denote_OCtx : Denote OCtx nat :=
{|
    correctness := fun _ => True;
    denote := num_elts_o;
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
  | TypedCircuits.control _ g => control (denote_unitary g)
  | TypedCircuits.bit_control _ g => control (denote_unitary g)  
  | TypedCircuits.transpose _ g => (denote_unitary g)†
  end. 

Lemma unitary_wf : forall {W} (U : Unitary W), WF_Matrix (denote_unitary U).
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

Instance denote_Unitary {W} : Denote (Unitary W) (Square (2^〚W〛)) :=
{|
    correctness := fun m => WF_Matrix m /\ unitary_matrix m;
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

Definition super_op_correctness {m n} (f : Superoperator m n) := 
  (forall ρ, Mixed_State ρ -> Mixed_State (f ρ)).   

Lemma denote_gate_correct : forall {W1} {W2} (g : Gate W1 W2), 
                            super_op_correctness (denote_gate g). 
Proof.
  unfold super_op_correctness.
Admitted.

Instance denote_Gate {W1 W2} : Denote (Gate W1 W2) (Superoperator (2^〚W1〛) (2^〚W2〛)) :=
{|
    correctness := super_op_correctness;
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

Fixpoint zip_to (m n: nat) (l : list nat) :
  list (nat * nat) :=
  match l with
  | nil => nil 
  | x :: xs => match m <? n with 
              | true => (m, x) :: zip_to (S m) n xs
              | false => nil
              end
  end.

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

Definition apply_U {m n} (U : Square (2^m)) (ρ : Density (2^n)) 
  (l : list nat) : Density (2^n) := 
  let S := swap_list n l in 
  let SU := S × (pad n U) × S† in  
  super SU ρ.

(* Moving new qubits to the end *)
Definition apply_new0 {n} (ρ : Density (2^n)) : Square (2^(n+1)) := 
  super (Id (2^n) ⊗ |0⟩) ρ.

Program Definition apply_new1 {n} (ρ : Density (2^n)) : Square (2^(n+1)) := 
  super (Id (2^n) ⊗ |1⟩) ρ.

Program Definition apply_discard {n} (ρ : Density (2^n)) (k : nat) : 
  Square (2^(n-1)) := 
  let S := swap_two n 0 k in 
  super ((⟨0| ⊗ Id (2^(n-1))) × S) ρ .+ super ((⟨1| ⊗ Id (2^(n-1))) × S) ρ.

(* Confirm tranposes are in the right place *)
Program Definition apply_meas {n} (ρ : Density (2^n)) (k : nat) : 
  Square (2^n) := 
  let S := swap_two n 0 k in 
  super (S × (|0⟩⟨0| ⊗ Id (2^(n-1))) × S†) ρ .+ 
  super (S × (|1⟩⟨1| ⊗ Id (2^(n-1))) × S†) ρ.

Definition apply_gate {n w1 w2} (g : Gate w1 w2) (ρ : Density (2^n)) (l : list nat) : 
  Density (2 ^ (n + 〚w2〛 - 〚w1〛)) :=
  match g with 
  | U _ u   => match 〚w1〛 <=? n with
              | true => apply_U (denote_unitary u) ρ l
              | false => Zero _ _
              end
  | init0   => apply_new0 ρ  
  | init1   => apply_new1 ρ
  | new0    => apply_new0 ρ
  | new1    => apply_new1 ρ
  | meas    => match l with 
              | x :: _ => apply_meas ρ x
              | _      => Zero _ _
              end                               
  | discard => match l with 
              | x :: _ => apply_discard ρ x
              | _      => Zero _ _
              end
  end.

(* Denoting Machine Circuits *)

Require Import MachineCircuits.

Fixpoint denote_machine_circuit_tail (m : nat) {n : nat} (c : Tail_Circuit n) 
  : Superoperator (2^m) (2^n) :=
  match c with 
  | m_output l => fun ρ => ρ (* resize ρ (2^n) (2^n) ? *)
  | m_gate l w1 w2 n' eq g c => fun ρ => let ρ' := apply_gate g ρ l in
                            (denote_machine_circuit_tail (m + 〚w2〛 - 〚w1〛) c ρ')
  end.

Fixpoint denote_machine_circuit {m n : nat} (c : Machine_Circuit m n) 
  : Superoperator (2^m) (2^n) :=
  match c with 
  | m_input l n' c => denote_machine_circuit_tail m c
  end.

Instance denote_Machine_Circuit {m n} : Denote (Machine_Circuit m n) (Superoperator (2^m) (2^n)) :=
{|
    correctness := fun _ => True;
    denote := denote_machine_circuit;
    denote_correct := fun _ => I
|}.

(** Checking example circuits **)

Require Import MachineExamples.

Definition I1 := Id (2^0).

(* Why can't I compose these? *)
Definition InitT := 〚init true〛 I1. Check InitT. 

Lemma Ex : InitT = |1⟩⟨1|.
Proof.
  intros.
  unfold InitT, I1. simpl.
  unfold apply_new1. simpl.
  unfold super. 
  rewrite kron_1_l; try omega; try show_wf.
  rewrite Mmult_1_r; try show_wf.
Qed.

(*
Lemma Ex2 : InitT ≡ |1⟩⟨1|.
  unfold mat_equiv.
  simpl.
  intros.
  destruct x as [x lx], y as [y ly]. simpl.
  destruct x,y.
  + Msolve.
  + Msolve.
  + Msolve.
  + destruct x,y. Msolve.
    all : omega.
Qed.
*)

Lemma WF_k0 : WF_Matrix |0⟩. Proof. show_wf. Qed.
Lemma WF_k1 : WF_Matrix |1⟩. Proof. show_wf. Qed.
Search WF_Matrix.

Ltac show_wf_safe :=
  repeat match goal with
  | [ |- WF_Matrix hadamard ]     => apply WF_hadamard
  | [ |- WF_Matrix |0⟩ ]          => apply WF_k0 
  | [ |- WF_Matrix |1⟩ ]          => apply WF_k1 
  | [ |- WF_Matrix (Zero ?m ?n) ] => apply WF_Zero
  | [ |- WF_Matrix (Id ?n) ]      => apply WF_Id 
  | [ |- WF_Matrix (?A × ?B) ]    => apply WF_mult 
  | [ |- WF_Matrix (?A .+ ?B) ]   => apply WF_plus 
  | [ |- WF_Matrix (?A ⊗ ?B) ]    => apply WF_kron
  | [ |- WF_Matrix (?A⊤) ]        => apply WF_transpose 
  | [ |- WF_Matrix (?A†) ]        => apply WF_conj_transpose 
  (* specialize and simpl to make the types line up. Maybe for kron too? *)
  | [ |- WF_Matrix (denote_unitary ?U) ] => specialize (unitary_wf U); simpl; auto
  end; trivial.

Require Import Reals.

Lemma Cconj_R : forall r : R, Cconj r = r. Proof. intros. clra. Qed.

(* More basic for the moment *)
Ltac Csimpl := 
  simpl;
  repeat (
    try rewrite Cconj_R;
    try rewrite Cplus_0_l;
    try rewrite Cplus_0_r;
    try rewrite Cmult_0_l;
    try rewrite Cmult_0_r;
    try rewrite Cmult_1_l;
    try rewrite Cmult_1_r
).

Ltac Msimpl := 
  simpl; 
  repeat (
  try rewrite kron_1_l;
  try rewrite kron_1_r;
  try rewrite Mmult_1_l; 
  try rewrite Mmult_1_r; 
  try rewrite id_conj_transpose_eq;
  try rewrite id_conj_transpose_eq); 
  try show_wf_safe; try omega.

Definition even_toss : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => 1/2
          | 1, 1 => 1/2
          | _, _ => 0
          end.

Lemma had_meas_toss : 〚hadamard_measure〛 |0⟩⟨0| = even_toss.
Proof.
  simpl.
  repeat (unfold apply_U, apply_meas, swap_list, swap_two, pad; simpl).
  Msimpl.
  prep_matrix_equality.
  unfold super, ket0, ket1, Mplus, Mmult, conj_transpose. simpl.
  Csimpl.
  destruct x, y; simpl.
  + Csolve.
  + destruct y; Csolve.
  + destruct x; Csolve.
  + destruct x. destruct y; Csolve. 
    Csolve.
Qed.

Check InitT.
Check flip.
Definition FLIP : Square (2^1) := 〚coin_flip〛 I1.
Lemma flip_toss : 〚coin_flip〛 I1  = even_toss.
Proof.
  simpl.
  repeat (unfold apply_U, apply_meas, apply_new0, swap_list, swap_two, pad; simpl).
  Msimpl. 
  prep_matrix_equality.
  unfold super, ket0, ket1, Mplus, Mmult, conj_transpose. simpl.
  Csimpl.
  destruct x, y; simpl.
  + Csolve.
  + destruct y; Csolve.
  + destruct x; Csolve.
  + destruct x. destruct y; Csolve. 
    Csolve.
Qed.

Lemma unitary_trans_id : forall (U : Unitary Qubit) (ρ : Density (2^1)), 
  WF_Matrix ρ -> 〚U_U_trans U〛 ρ = ρ.
Proof.
  intros U ρ WF.
  simpl.
  repeat (unfold apply_U, swap_list, swap_two, pad; simpl).
  Msimpl. 
  unfold super.
  rewrite conj_transpose_involutive.
  specialize (unitary_gate_unitary U). unfold unitary_matrix. simpl. intros H.
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
  
