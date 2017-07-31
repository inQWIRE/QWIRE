Require Import Program. 
Require Export Contexts.
Require Import HOASCircuits.
Require Import FlatCircuits.
Require Import List.
Require Import Arith.
Require Export Quantum.
Require Import Omega.
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

(** Wire and Context Denotation **)


Instance Denote_WType : Denote WType nat := {| denote := size_WType |}.
Instance Denote_Ctx : Denote Ctx nat := {| denote := size_Ctx |}.
Instance Denote_OCtx : Denote OCtx nat := {| denote := size_OCtx |}.

(** Unitary Denotation **)
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
  induction U.
  + apply WF_hadamard.
  + apply WF_pauli_x.
  + apply WF_pauli_y.
  + apply WF_pauli_z.
  + simpl. auto with wf_db. 
  + simpl. auto with wf_db. 
  + simpl. auto with wf_db. 
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

(** Gate Denotation *)

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

Lemma pow_gt_0 : forall n, 2^n > O.
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
Admitted.

Instance Denote_Gate W1 W2 : Denote (Gate W1 W2) (Superoperator (2^〚W1〛) (2^〚W2〛)):=
    {| denote := denote_gate |}.
Instance Denote_Gate_Correct W1 W2 : Denote_Correct (Denote_Gate W1 W2) :=
{|
    correctness := WF_Superoperator;
    denote_correct := denote_gate_correct
|}.

Require Import Recdef.

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

(*
Function swap_list_aux (n : nat) (l : list (nat * nat)) {measure length l} : Square  (2^n) :=
  match l with
  | nil => Id (2^n)
  | cons (a,b) xs => swap_two n a b × 
        swap_list_aux n (map (fun z => if a =? snd z then (fst z, b) else z) xs)
  end. 
  intros n l p xs a b teq0 teq.
  rewrite map_length.
  simpl.
  apply Nat.lt_succ_diag_r.
Defined.
*)
  
(* Old and missing remapping:
Function swap_list_aux (n : nat) (l : list (nat * nat)) {measure length l} : Square  (2^n) :=
  match l with
  | nil => Id (2^n)
  | cons (a,b) xs => swap_two n a b × (swap_list_aux n xs)
  end. 
*)

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
  unfold swap_two. simpl.
  rewrite kron_1_r.
  auto with wf_db.
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

(* Confirm transposes are in the right place *)
Program Definition apply_meas {n} (k : nat) : Superoperator (2^n) (2^n) :=
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
Notation "# l " := (length l) (at level 0).


Lemma interp_nonzero : forall W, (0 < #(get_interpretations W))%nat.
Proof.
  induction W; simpl; try omega.
  rewrite length_cross_list.
  apply Nat.mul_pos_pos; auto. 
Defined.

Definition SZero {n} : Superoperator n n := fun ρ => Zero n n.
Definition Splus {m n} (S T : Superoperator m n) : Superoperator m n :=
  fun ρ => S ρ .+ T ρ.

Definition sum_over_interpretations {W m n}
           (f : interpret W -> Superoperator m n) 
  := fold_left Splus (map f (get_interpretations W)) SZero.

Program Fixpoint kets {W} : interpret W -> Matrix (2^〚W〛) 1 :=
  match W with
  | One     => fun _ => Id 1
  | Qubit   => fun x => if x then ket1 else ket0
  | Bit     => fun x => if x then ket1 else ket0
  | Tensor W1 W2 => fun x => let (x1,x2) := x in
                             kets x1 ⊗ kets x2
  end.

(* Often we want to consider a pattern as a swap list for a larger context *)
Fixpoint pat_to_list {Γ W} (p : Pat Γ W) : list nat :=
  match p with
  | pair Γ1 Γ2 Γ0 W1 W2 valid merge p1 p2 => 
      let ls1 := pat_to_list p1 in
      let ls2 := pat_to_list p2 in 
      ls1 ++ ls2
  | qubit x Γ sing => [x]
  | bit   x Γ sing => [x]
  | unit => []
  end.
Lemma pat_to_list_length : forall Γ W (p : Pat Γ W), length (pat_to_list p) = size_WType W.
Proof.
  induction p; simpl; auto.
  rewrite app_length. auto.
Qed.

Fixpoint num_wires_before (Γ : Ctx) i : nat :=
  match Γ, i with
  | [], i => i
  | _, 0 => 0
  | None :: Γ', S i' => num_wires_before Γ' i'
  | Some _ :: Γ', S i' => S (num_wires_before Γ' i')
  end.
Definition num_wires_before_o (Γ : OCtx) : nat -> nat :=
  match Γ with
  | Valid Γ' => num_wires_before Γ'
  | Invalid => id
  end.

Definition denote_pat_in Γ' {Γ W} (p : Pat Γ W): Matrix (2^〚Γ ⋓ Γ'〛) (2^〚W〛 * 2^〚Γ'〛):=
    let ls := map (num_wires_before_o (Γ ⋓ Γ')) (pat_to_list p) in
    swap_list (〚Γ ⋓ Γ'〛) ls.


Instance Denote_Pat {Γ W} : Denote (Pat Γ W) (Matrix (2^〚Γ〛) (2^〚W〛)) := 
   {| denote := denote_pat_in ∅ |}.

Fixpoint denote_flat_circuit {Γ W} (C : Flat_Circuit Γ W) 
                 : Superoperator (2^〚Γ〛) (2^〚W〛) :=
  match C with
  | flat_output p => super (〚p〛)
  | @flat_gate Γ Γ1 _ Γ2 Γ2' W1 W2 _ _ _ _ _ g p1 p2 C' => 
                  (* Superoperator (2^Γ2') (2^W) *)
    compose_super (denote_flat_circuit C') (
                  (* Superoperator (2^〚W2〛 * 2^Γ) (2^Γ2') *)
    compose_super (super (denote_pat_in Γ p2)†) (
                  (* Superoperator (2^〚W1〛 * 2^Γ) (2^〚W2〛 * 2^Γ) *)
    compose_super (denote_gate' (〚Γ〛) g) (
                  (* Superoperator (2^(Γ1⋓Γ)) (2^W1 * 2^Γ) *)
                  (super (denote_pat_in Γ p1)))))

  | @flat_lift Γ1 Γ2 _ w _ _ _ p f => 
     let supers   : interpret w -> Superoperator (2^〚Γ1 ⋓ Γ2〛) (2^〚Γ2〛)
                  := fun x => compose_super (denote_flat_circuit (f x)) (
                              compose_super (super ((kets x)† ⊗ Id (2^〚Γ2〛)))
                                            (super (denote_pat_in Γ2 p)))
     in
     let branches := map supers (get_interpretations w) in
     fold_left Splus branches SZero
  end.

(* Old version, using apply_gate:
  | flat_gate _ _ _ _ Γ2' _ _ _ _ _ _ _ g p1 p2 C' => 
    let l1 := pat_to_list p1 in
    let l2 := pat_to_list p2 in
                  (* Superoperator (2^Γ2') (2^W) *)
    compose_super (denote_flat_circuit C') (
                  (* Superoperator (2^Γ2') (2^Γ2') *)
    compose_super (super (swap_list (〚Γ2'〛) l2)†) 
                  (* Superoperator (2^Γ) (2^(Γ + 〚W2〛-〚W1〛)) *)
                  (apply_gate g l1) )
  | flat_lift _ _ _ _ _ _ _ _ f => denote_lift (fun x => denote_flat_circuit (f x))
*)


Instance Denote_Flat_Circuit Γ W 
    : Denote (Flat_Circuit Γ W) (Superoperator (2^〚Γ〛) (2^〚W〛)) :=
    {| denote := denote_flat_circuit |}.
Instance Denote_Flat_Circuit_Correct Γ W : Denote_Correct (Denote_Flat_Circuit Γ W):=
    {| correctness := WF_Superoperator |}.
Admitted.

Definition denote_flat_box {W1 W2} (b : Flat_Box W1 W2) 
                           : Superoperator (2^〚W1〛) (2^〚W2〛) :=
  match b with
  | flat_box p C => compose_super (denote_flat_circuit C)
                                        (super (denote_pat_in ∅ p)†)
                                        
  end.

Instance Denote_Flat_Box W1 W2
         : Denote (Flat_Box W1 W2) (Superoperator (2^〚W1〛) (2^〚W2〛)) :=
{| 
    denote      := denote_flat_box;
|}.
Instance Denote_Flat_Box_Correct W1 W2 : Denote_Correct (Denote_Flat_Box W1 W2):=
    {| correctness := WF_Superoperator |}.
Proof.
Admitted.

Definition I1 := Id (2^0).
Lemma WF_I1 : WF_Matrix 1 1 I1. Proof. unfold I1. apply WF_Id. Qed.
Hint Resolve WF_I1 : wf_db.

Ltac destruct1 :=
  match goal with
  | [ |- context[match ?x with 
                 | 0   => _
                 | S _ => _
                 end] ] => destruct x
  end.
Ltac destruct_Csolve := repeat (destruct1; try Csolve).

(*Set Printing All.*)
(* Unset Printing Notations.*)
  
Lemma size_singleton : forall x W, size_Ctx (singleton x W) = 1%nat.
Proof.
  induction x; auto.
Qed.

Lemma fresh_pat_empty : forall W, pat_to_list (fresh_pat ∅ W) = seq 0 (〚W〛).
Proof.
  intros W.
  simpl.
  induction W; trivial.
  simpl in *.
  specialize (fresh_ctx_valid W1 ∅); intros H.
  destruct H as [Γ]. 
(*  destruct (fresh_ctx ∅ W1).
    rewrite H. *)
Admitted.

Lemma size_fresh_ctx : forall Γ_in W, size_OCtx (fresh_ctx Γ_in W) = 〚W〛.
Proof.
  intros Γ_in W.
  revert Γ_in.
  induction W; intros Γ_in; simpl; auto; try apply size_singleton.
Admitted.
Lemma map_num_wires_before : forall W, 
      map (num_wires_before_o (fresh_ctx ∅ W)) (seq 0 (〚W〛)) = seq 0 (〚W〛).
Admitted.


(****************** HOAS ********************)

Instance Denote_HOAS_Circuit Γ W 
    : Denote (Circuit Γ W) (Superoperator (2^〚Γ〛) (2^〚W〛)) :=
{| 
    denote      := fun C => 〚from_HOAS C〛;
|}.
Instance Denote_HOAS_Circuit_Correct Γ W : Denote_Correct (Denote_HOAS_Circuit Γ W):=
    {| correctness := WF_Superoperator |}.
Admitted.

Instance Denote_HOAS_Box W1 W2 
    : Denote (Box W1 W2) (Superoperator (2^〚W1〛) (2^〚W2〛)) :=
    {| denote := fun C => 〚from_HOAS_Box C〛 |}.
Instance Denote_HOAS_Box_Correct W1 W2 : Denote_Correct (Denote_HOAS_Box W1 W2) :=
    {| correctness := WF_Superoperator |}.
Admitted.
 


