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

(** Wire Denotation **)

Instance denote_WType : Denote WType nat :=
{|
    correctness := fun _ => True;
    denote := num_wires;
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


Notation bnat n := (sig (fun i => i < n)).

Program Fixpoint zip_to (m n: nat) (l : list (bnat n)) :
  list (bnat n * bnat n) :=
  match l with
  | nil => nil 
  | x :: xs => match m <? n with 
              | true => (m, x) :: zip_to (S m) n xs
              | false => nil
              end
  end.
Next Obligation. apply Nat.ltb_lt. auto. Defined. 

Program Fixpoint swap_list_aux 
  (n : nat) (l : list (bnat n * bnat n)) : Square  (2^n) :=
  match l with
  | nil => Id (2^n)
  | cons (a,b) xs => swap_two n a b × swap_list_aux n xs
  end. 

Definition swap_list (n : nat) (l : list (bnat n)) :=
  swap_list_aux n (zip_to 0 n l). 

Program Definition my_one : {i : nat | i < 2} := S O.
Lemma swap_list_swap : swap_list 2 [my_one] = swap.
Proof.
  simpl.
  unfold swap_list, swap_list_aux.
  simpl.
  rewrite Mmult_1_r.
  apply swap_two_base.
  (* .. and we're done here *)
Admitted.

(*
(*
Require Import Coq.Vectors.Vector.
Definition LList := t.
*)
Program Fixpoint swap_list {m n} (v : LList (sig (fun i => i < n)) m) : Square (2^n) :=
  match v with 
  | nil => Id (2^(n-m))
  | cons i _ v' => (swap_to_0 n i) × ((Id 2) ⊗ (@swap_list (m-1) (n-1) v'))
  end.
Next Obligation. rewrite Nat.sub_0_r. reflexivity. Defined.
Next Obligation. rewrite Nat.sub_0_r. reflexivity. Defined.
Next Obligation. rewrite plus_0_r.  reflexivity. Defined.
Next Obligation. rewrite Nat.sub_0_r. reflexivity. Defined.
*)

Local Obligation Tactic := program_simpl; unify_pows_two; try omega.

Program Definition pad {m} n (pf: m <= n) (A : Square (2^m)) : Square (2^n) :=
  (A ⊗ Id (2^ (n - m))).

Definition apply_U {m n} (U : Square (2^m)) (ρ : Density (2^n)) 
  (l : list (bnat n)) {pf : m <= n} : Density (2^n) := 
  let S := swap_list n l in 
  let SU := S × (pad n pf U) × S† in  
  super SU ρ.

(* Moving new qubits to the end *)
Program Definition apply_new0 {n} (ρ : Density (2^n)) : Square (2^(n+1)) := 
  super (Id (2^n) ⊗ |0⟩) ρ.

Program Definition apply_new1 {n} (ρ : Density (2^n)) : Square (2^(n+1)) := 
  super (Id (2^n) ⊗ |1⟩) ρ.

Program Definition apply_discard {n} (ρ : Density (2^n)) (k : bnat n) : 
  Square (2^(n-1)) := 
  let S := @swap_two n 0 k _ _ in 
  super ((⟨0| ⊗ Id (2^(n-1))) × S) ρ .+ super ((⟨1| ⊗ Id (2^(n-1))) × S) ρ.

Program Definition apply_meas {n} (ρ : Density (2^n)) (k : bnat n) : 
  Square (2^n) := 
  let S := @swap_two n 0 k _ _ in 
  super (S† × (|0⟩⟨0| ⊗ Id (2^(n-1))) × S) ρ .+ 
  super (S† × (|1⟩⟨1| ⊗ Id (2^(n-1))) × S) ρ.

Program Definition apply_gate {n w1 w2} (g : Gate w1 w2) (ρ : Density (2^n)) 
  (l : list (bnat n)) : Density (2 ^ (n + 〚w2〛 - 〚w1〛)) :=
  match g with 
  | U _ u   => match 〚w1〛 <=? n with
              | true => @apply_U _ _ (denote_unitary u) ρ l _
              | false => Zero (2 ^ (n + 〚w2〛 - 〚w1〛)) (2 ^ (n + 〚w2〛 - 〚w1〛))
              end
  | init0   => apply_new0 ρ  
  | init1   => apply_new1 ρ
  | new0    => apply_new0 ρ
  | new1    => apply_new1 ρ
  | meas    => match l with 
              | x :: _ => apply_meas ρ x
              | _      => Zero (2 ^ (n + 〚w2〛 - 〚w1〛)) (2 ^ (n + 〚w2〛 - 〚w1〛))
              end                               
  | discard => match l with 
              | x :: _ => apply_discard ρ x
              | _      => Zero (2 ^ (n + 〚w2〛 - 〚w1〛)) (2 ^ (n + 〚w2〛 - 〚w1〛))
              end
  end.
Next Obligation. apply Nat.leb_le. auto. Defined.

(* Denoting Machine Circuits *)

Require Import MachineCircuits.

(* Now easy! *)
Definition resize {m1 n1 : nat} (A : Matrix m1 n1) (m n : nat) : Matrix m n := A.

Program Fixpoint bound_list (l : list nat) (n: nat) : list (bnat n) :=
  match l with
  | [] => []
  | x :: xs => match x <? n with 
              | true => x :: bound_list xs n
              | false => bound_list xs n
              end
  end.
Next Obligation. apply Nat.ltb_lt. auto. Defined.

Fixpoint denote_machine_circuit (m n : nat) (c : Machine_Circuit) 
  : Superoperator (2^m) (2^n) :=
  match c with 
  | m_output => fun ρ => ρ (* resize ρ (2^n) (2^n) ? *)
  | m_gate l w1 w2 eq g c => fun ρ => let ρ' := apply_gate g ρ (bound_list l m) in
                                  (denote_machine_circuit (m + 〚w2〛 - 〚w1〛) n c ρ')
  end.

(* Checking example circuits *)

Require Import MachineExamples.

Definition Sup := (denote_machine_circuit 0 1 (init true)).
Definition InitT := (Sup (Id (2 ^ 〚One〛))). Check InitT.

Lemma Ex : InitT ≡ |1⟩ × ⟨1|.
Proof.
  unfold mat_equiv.
  intros.
  destruct x as [x lx], y as [y ly]. simpl.
  unfold InitT. unfold Sup. simpl.
  unfold apply_new1. simpl.
  unfold super. simpl.
  rewrite kron_1_l; try omega. 2: show_wf.
  

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



Lemma Ex : Mat ≡ |1⟩ × ⟨1|.
Proof.
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





(*Fixpoint denote_circuit {Γ : Ctx} {W : WType} (c : Flat_Circuit Γ W)*)

(* *)
