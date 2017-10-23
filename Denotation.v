Require Import Program. 
Require Export Contexts.
Require Import HOASCircuits.
Require Import FlatCircuits.
Require Import Arith.
Require Export Quantum.
Require Import Omega.
Require Import List.
Import ListNotations.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.


Class Denote source target := {denote : source -> target}.
Notation "〚 s 〛" := (denote s) (at level 10).

Class Denote_Correct {source target} `(Denote source target) :=
{
    correctness : target -> Prop;
    denote_correct : forall (x : source), correctness (denote x)
}.

(** Unitary Denotation **)

Instance Denote_WType : Denote WType nat := {| denote := size_WType |}.

Fixpoint denote_unitary {W} (U : Unitary W) : Square (2^〚W〛) :=
  match U with  
  | H => hadamard 
  | σx => pauli_x
  | σy => pauli_y
  | σz => pauli_z
  | ctrl g => control (denote_unitary g)
  | bit_ctrl g => control (denote_unitary g)  
  | Contexts.transpose g => (denote_unitary g)†
  end. 
Instance Denote_Unitary W : Denote (Unitary W) (Square (2^〚W〛)) := 
    {| denote := denote_unitary |}.

Lemma WF_unitary : forall {W} (U : Unitary W), 
      WF_Matrix (2^〚W〛) (2^〚W〛) (〚U〛).
Proof.
  induction U; simpl; auto with wf_db.
Qed.
Hint Resolve WF_unitary : wf_db.

Lemma unitary_gate_unitary : forall {W} (U : Unitary W), is_unitary (〚U〛).
Proof.
  induction U.
  + apply H_unitary.
  + apply σx_unitary.
  + apply σy_unitary.
  + apply σz_unitary.
  + simpl. apply control_unitary; assumption. (* NB: Admitted lemma *)
  + simpl. apply control_unitary; assumption. (* NB: Admitted lemma *)
  + simpl. apply transpose_unitary; assumption.
Qed.
(* Hint Resolve unitary_gate_unitary. Do we need this? Where? *)
Instance Denote_Unitary_Correct W : Denote_Correct (Denote_Unitary W) :=
{|
    correctness := fun A => is_unitary A;
    denote_correct := fun U => unitary_gate_unitary U
|}.

(** Gate Denotation **)

Definition denote_gate' n {w1 w2} (g : Gate w1 w2)
           : Superoperator (2^〚w1〛 * 2^n) (2^〚w2〛 * 2^n) :=
  match g with 
  | U u   => super (〚u〛 ⊗ Id (2^n))
  | init0   => super (|0⟩ ⊗ Id (2^n))
  | init1   => super (|1⟩ ⊗ Id (2^n))
  | new0    => super (|0⟩ ⊗ Id (2^n))
  | new1    => super (|1⟩ ⊗ Id (2^n))
  | meas    => fun ρ => super (|0⟩⟨0| ⊗ Id (2^n)) ρ .+ super (|1⟩⟨1| ⊗ Id (2^n)) ρ
  | discard => fun ρ => super (⟨0| ⊗ Id (2^n)) ρ .+ super (⟨1| ⊗ Id (2^n)) ρ
  end.

Definition denote_gate {W1 W2} (g : Gate W1 W2) : 
  Superoperator (2^〚W1〛) (2^〚W2〛) := denote_gate' 0 g.
(*  match g with
  | U _ u  => super (〚u〛)
  | init0 => new0_op 
  | init1 => new1_op
  | new0 => new0_op
  | new1 => new1_op 
  | meas => meas_op
  | discard => discard_op
  end.*)

Lemma pow_gt_0 : forall n, (2^n > O)%nat.
Proof.
  induction n; auto. 
  simpl. apply gt_trans with (2^n)%nat; auto. omega.
Qed.


Lemma WF_denote_gate : forall n W1 W2 (g : Gate W1 W2) ρ,
    WF_Matrix (2^〚W1〛 * 2^n) (2^〚W1〛 * 2^n) ρ 
 -> WF_Matrix (2^〚W2〛 * 2^n) (2^〚W2〛 * 2^n) (denote_gate' n g ρ).
Proof.
  intros n W1 W2 g ρ wf_ρ.
  assert (0 < 2^n)%nat by apply pow_gt_0.
  assert (0 <> 2^n)%nat by omega.
  destruct g; simpl; unfold super; auto with wf_db; try omega.
  specialize (WF_unitary u). intros wf_u. auto with wf_db.
Qed.
Hint Resolve WF_denote_gate : wf_db.

Lemma denote_gate_correct : forall {W1} {W2} (g : Gate W1 W2), 
                            WF_Superoperator (denote_gate g). 
Proof.
  unfold WF_Superoperator.
  intros.
  induction g.
  + simpl.
    rewrite kron_1_r.
    rewrite Nat.mul_1_r.
    apply mixed_unitary.
    apply WF_unitary.
    apply unitary_gate_unitary.
    assumption.
  + simpl in *.
    rewrite kron_1_r.
    unfold super.
    rewrite (mixed_state_id1 ρ); trivial.
    rewrite Mmult_1_r.
    constructor; apply pure0.
    auto with wf_db.
  + simpl in *.
    rewrite kron_1_r.
    unfold super.
    rewrite (mixed_state_id1 ρ); trivial.
    rewrite Mmult_1_r.
    constructor; apply pure1.
    auto with wf_db.
  + simpl in *.
    rewrite kron_1_r.
    unfold super.
    rewrite (mixed_state_id1 ρ); trivial.
    rewrite Mmult_1_r.
    constructor; apply pure0.
    auto with wf_db.
  + simpl in *.
    rewrite kron_1_r.
    unfold super.
    rewrite (mixed_state_id1 ρ); trivial.
    rewrite Mmult_1_r.
    constructor; apply pure1.
    auto with wf_db.
  + admit.
  + simpl in *.
    rewrite 2 kron_1_r.
    autounfold with M_db; simpl.
    admit.
Admitted.

Instance Denote_Gate W1 W2 : Denote (Gate W1 W2) (Superoperator (2^〚W1〛) (2^〚W2〛)):=
    {| denote := denote_gate |}.
Instance Denote_Gate_Correct W1 W2 : Denote_Correct (Denote_Gate W1 W2) :=
{|
    correctness := WF_Superoperator;
    denote_correct := denote_gate_correct
|}.

(* Require Import Recdef. *)

(* m is to show structural decreasing *)
Fixpoint swap_list_aux (m n : nat) (l : list (nat * nat)) : Square  (2^n) :=
  match m with
  | 0 => Id (2^n)
  | S m' => match l with
           | nil => Id (2^n)
           | cons (a,b) xs => swap_two n a b × 
             swap_list_aux m' n (map (fun z => if a =? snd z then (fst z, b) else z) xs)
           end
  end. 

Definition zip_to (m n : nat) (l : list nat) := combine (seq m n) l.

Definition swap_list (n : nat) (l : list nat) : Square (2^n) := 
  swap_list_aux n n (zip_to 0 n l). 

Lemma swap_list_swap : swap_list 2 [S O] = swap.
Proof.
  simpl.
  unfold swap_list, swap_list_aux.
  simpl.
  rewrite Mmult_1_r.
  apply swap_two_base. 
  unfold swap_two.
  simpl.
  rewrite kron_1_r.
  auto with wf_db.
Qed.

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

Definition apply_discard {n} (k : nat) : Superoperator (2^n) (2^(n-1)) :=
  let S := swap_two n 0 k in 
  fun ρ => super ((⟨0| ⊗ Id (2^(n-1))) × S) ρ .+ super ((⟨1| ⊗ Id (2^(n-1))) × S) ρ.

(* Confirm transposes are in the right place *)
Definition apply_meas {n} (k : nat) : Superoperator (2^n) (2^n) :=
  let S := swap_two n 0 k in 
  fun ρ => super (S × (|0⟩⟨0| ⊗ Id (2^(n-1))) × S†) ρ 
        .+ super (S × (|1⟩⟨1| ⊗ Id (2^(n-1))) × S†) ρ.

Definition super_Zero {m n} : Superoperator m n  :=
  fun _ => Zero _ _.

Definition apply_gate {n w1 w2} (g : Gate w1 w2) (l : list nat) 
           : Superoperator (2^n) (2^(n+〚w2〛-〚w1〛)) :=
  match g with 
  | U u   => match 〚w1〛 <=? n with
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

(* Can also use map_id and map_ext *)
Lemma map_same_id : forall a l, (map (fun z : nat * nat => if a =? snd z then (fst z, a) else z)
                                (combine l l)) = combine l l.
Proof.
  intros a l.
  induction l. reflexivity.
  simpl.
  rewrite IHl.
  destruct (a =? a0) eqn:eq; try reflexivity.
  apply beq_nat_true in eq.
  subst; reflexivity.
Qed.

Lemma swap_list_aux_id : forall m n l, swap_list_aux m n (combine l l) = Id (2 ^ n).
Proof.
  intros m n l.
  generalize dependent m.
  induction l; intros m.
  + simpl. destruct m; reflexivity.
  + simpl. 
    destruct m; [reflexivity|].
    simpl.
    rewrite map_same_id.
    rewrite IHl. 
    unfold swap_two. 
    rewrite <- beq_nat_refl. 
    autorewrite with M_db.
    reflexivity.
Qed.

Lemma swap_list_n_id : forall n, swap_list n (seq 0 n) = Id (2^n).
Proof.
  intros.
  unfold swap_list.
  unfold zip_to.
  apply swap_list_aux_id.
Qed.

Definition SZero {n} : Superoperator n n := fun ρ => Zero n n.
Definition Splus {m n} (S T : Superoperator m n) : Superoperator m n :=
  fun ρ => S ρ .+ T ρ.


(** Denoting Min Circuits **)

Fixpoint pat_size {W} (p : Pat W) : nat := 
  match p with
  | unit       => 0
  | bit x      => 1
  | qubit x    => 1
  | pair p1 p2 => (pat_size p1) + (pat_size p2)
  end.

Lemma pat_size_hash_pat : forall w (p : Pat w) ls, 
      pat_size (hash_pat p ls) = pat_size p.
Proof. 
  induction p; intros; auto.
  simpl. rewrite IHp1, IHp2. reflexivity.
Qed.

(*
Fixpoint get_output_size {w} (c : Min_Circuit w) :=
  match c with
  | min_output p     => pat_size p
  | min_gate g p c'  => get_output_size c'
  | min_lift p c'    => get_output_size (c' true)
  end.

Definition get_box_output_size {W} (c : Min_Box W) :=
  match c with
  | min_box W c'     => get_output_size c'
  end. 
*)

(* n is the input size *)
Fixpoint denote_min_circuit {w}  (n : nat) (c : Min_Circuit w) : Superoperator (2^n) (2^〚w〛) 
  := 
  match c with 
  | min_output p            => super (swap_list (〚w〛) (pat_to_list p))
  | @min_gate _ W1 W2 g p c'  => compose_super 
                                (denote_min_circuit (n + 〚W2〛 - 〚W1〛) c')
                                (apply_gate g (pat_to_list p))
  (* I think we need a weighing here - also a measure-discard *)
  | min_lift p c'   => Splus (denote_min_circuit n (c' true))
                             (denote_min_circuit n (c' false))
  end.

Definition denote_min_box {W1 W2} (c : Min_Box W1 W2) : 
  Superoperator (2 ^ 〚 W1 〛) (2 ^ 〚 W2 〛) :=
  match c with
  | min_box _ c' => denote_min_circuit (〚W1〛) c'  
  end.

(** Denoting hoas circuits **)

Definition denote_box {W1 W2 : WType} (c : Box W1 W2) := 
    denote_min_box (hoas_to_min_box c).
Instance Denote_Box {W1 W2} : Denote (Box W1 W2) (Superoperator (2^〚W1〛) (2^〚W2〛)) :=
         {| denote := denote_box |}.

Print compose.
Program Fixpoint hoas_to_min_aux {w} (c: Circuit w) (li : list Var) (n : nat) 
                          : list Var * nat * Min_Circuit w :=

  match c with
  | output p        => (li,n,min_output (hash_pat p li))
  | gate g p c' => 
    let p0 := hash_pat p li in
    match g with
    | U u           => let (ls0,n0,c0) := hoas_to_min_aux (c' p) li n in
                       (ls0,n0,min_gate g p0 c0)
    | init0 | init1 => let li0 := li ++ [n] in
                       let n0 := S n in
                       let (ls0',n0',c0') := hoas_to_min_aux (c' (qubit n)) li0 n0 in
                       (ls0',n0',min_gate g p0 c0')
    | new0 | new1   => let li0 := li ++ [n] in
                       let n0 := S n in
                       let (ls0',n0',c0') := hoas_to_min_aux (c' (bit n)) li0 n0 in
                       (ls0',n0',min_gate g p0 c0')
    | meas          => let (ls0,n0,c0) := hoas_to_min_aux (c' (qubit_to_bit p)) li n in
                       (ls0,n0, min_gate g p0 c0)
    | discard       => let li' := List.remove Nat.eq_dec (get_var p) li in
                       let (ls0,n0,c0) := has_to_min_aux (c' unit) li' n in
                       (ls0,n0,min_gate g p0 c0)
    end
  | lift p c'   =>  let li' := List.remove Nat.eq_dec (get_var p) li in
                    min_lift (hash_pat p li) (fun b => hoas_to_min (c' b) li' n) 
  end.
