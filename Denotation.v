Require Import Program. 
Require Import Arith.
Require Import Omega.

Require Import Monad.
Require Export Contexts.
Require Import HOASCircuits.
Require Import DBCircuits.
Require Export Quantum.


Require Import List.
Import ListNotations.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.


Class Denote source target := {denote : source -> target}.

Notation "⟦ s ⟧" := (denote s) (at level 10).

Class Denote_Correct {source target} `(Denote source target) :=
{
    correctness : target -> Prop;
    denote_correct : forall (x : source), correctness (denote x)
}.

(** Unitary Denotation **)

Instance Denote_WType : Denote WType nat := {| denote := size_WType |}.

Fixpoint denote_Ctx (Γ : Ctx) : nat :=
  match Γ with
  | nil => 0
  | Some _ :: Γ' => S (denote_Ctx Γ')
  | None :: Γ' => denote_Ctx Γ'
  end.
Definition denote_OCtx (Γ : OCtx) : nat :=
  match Γ with
  | Invalid => 0
  | Valid Γ' => denote_Ctx Γ'
  end.
Instance Denote_Ctx : Denote Ctx nat := {| denote := denote_Ctx |}.
Instance Denote_OCtx : Denote OCtx nat := {| denote := denote_OCtx |}.

Fixpoint denote_unitary {W} (U : Unitary W) : Square (2^⟦W⟧) :=
  match U with  
  | H => hadamard 
  | X => σx
  | Y => σy
  | Z => σz
  | ctrl g => control (denote_unitary g)
  | bit_ctrl g => control (denote_unitary g)  
  | Contexts.transpose g => (denote_unitary g)†
  end. 
Instance Denote_Unitary W : Denote (Unitary W) (Square (2^⟦W⟧)) := 
    {| denote := denote_unitary |}.

Lemma WF_unitary : forall {W} (U : Unitary W), 
      WF_Matrix (2^⟦W⟧) (2^⟦W⟧) (⟦U⟧).
Proof.
  induction U; simpl; auto with wf_db.
Qed.
Hint Resolve WF_unitary : wf_db.

Lemma unitary_gate_unitary : forall {W} (U : Unitary W), is_unitary (⟦U⟧).
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


Definition denote_gate' (safe : bool) n {w1 w2} (g : Gate w1 w2)
           : Superoperator (2^⟦w1⟧ * 2^n) (2^⟦w2⟧ * 2^n) :=
  match g with 
  | U u     => super (⟦u⟧ ⊗ Id (2^n))
  | NOT     => super (σx ⊗ Id (2^n))
  | init0   => super (|0⟩ ⊗ Id (2^n))
  | init1   => super (|1⟩ ⊗ Id (2^n))
  | new0    => super (|0⟩ ⊗ Id (2^n))
  | new1    => super (|1⟩ ⊗ Id (2^n))
  | meas    => fun ρ => super (|0⟩⟨0| ⊗ Id (2^n)) ρ .+ super (|1⟩⟨1| ⊗ Id (2^n)) ρ
  | discard => Splus (super (⟨0| ⊗ Id (2^n))) (super (⟨1| ⊗ Id (2^n)))
  (* Safe performs a standard measure-discard, unsafe takes for granted that the 
     qubit to be removed is in the desired state. *)
  | assert0 => if safe then Splus (super (⟨0| ⊗ Id (2^n))) (super (⟨1| ⊗ Id (2^n)))
                      else super (⟨0| ⊗ Id (2^n))
  | assert1 => if safe then Splus (super (⟨0| ⊗ Id (2^n))) (super (⟨1| ⊗ Id (2^n)))
                      else super (⟨1| ⊗ Id (2^n))
  end.

Definition denote_gate safe {W1 W2} (g : Gate W1 W2) : 
  Superoperator (2^⟦W1⟧) (2^⟦W2⟧) := denote_gate' safe 0 g.
(*  match g with
  | U _ u  => super (⟦u⟧)
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


Lemma WF_denote_gate : forall safe n W1 W2 (g : Gate W1 W2) ρ,
    WF_Matrix (2^⟦W1⟧ * 2^n) (2^⟦W1⟧ * 2^n) ρ 
   -> WF_Matrix (2^⟦W2⟧ * 2^n) (2^⟦W2⟧ * 2^n) (denote_gate' safe n g ρ).
Proof.
  intros safe n W1 W2 g ρ wf_ρ.
  assert (0 < 2^n)%nat by apply pow_gt_0.
  assert (0 <> 2^n)%nat by omega.
  destruct g; simpl; unfold super, Splus; try destruct safe; 
    auto with wf_db; try omega.
  specialize (WF_unitary u). intros wf_u. auto with wf_db.
  specialize (WF_unitary u). intros wf_u. auto with wf_db.
Qed.
Hint Resolve WF_denote_gate : wf_db.

(* This is only true for "safe" gate denotation *)
Lemma denote_gate_correct : forall {W1} {W2} (g : Gate W1 W2), 
                            WF_Superoperator (denote_gate true g). 
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
  + simpl.
    rewrite kron_1_r.
    apply mixed_unitary.
    apply WF_σx.
    apply σx_unitary.
    assumption.
  + simpl in *.
    rewrite kron_1_r.
    unfold super.
    rewrite (mixed_dim1 ρ); trivial.
    rewrite Mmult_1_r.
    constructor; apply pure0.
    auto with wf_db.
  + simpl in *.
    rewrite kron_1_r.
    unfold super.
    rewrite (mixed_dim1 ρ); trivial.
    rewrite Mmult_1_r.
    constructor; apply pure1.
    auto with wf_db.
  + simpl in *.
    rewrite kron_1_r.
    unfold super.
    rewrite (mixed_dim1 ρ); trivial.
    rewrite Mmult_1_r.
    constructor; apply pure0.
    auto with wf_db.
  + simpl in *.
    rewrite kron_1_r.
    unfold super.
    rewrite (mixed_dim1 ρ); trivial.
    rewrite Mmult_1_r.
    constructor; apply pure1.
    auto with wf_db.
  + simpl in *.
    rewrite kron_1_r.
    unfold super.
    Msimpl.
    specialize (WF_Mixed _ H) as WF.
    replace (|0⟩⟨0| × ρ × |0⟩⟨0|) with (ρ 0%nat 0%nat .* |0⟩⟨0|) by solve_matrix.
    replace (|1⟩⟨1| × ρ × |1⟩⟨1|) with (ρ 1%nat 1%nat .* |1⟩⟨1|) by solve_matrix.
    specialize (mixed_state_trace_1 _ H) as TR1. unfold trace in TR1. simpl in TR1.
    replace (ρ 1%nat 1%nat) with (1 - ρ O O) by (rewrite <- TR1; clra).
    replace (ρ O O) with ((fst (ρ O O)), snd (ρ O O)) by clra. 
    rewrite mixed_state_diag_real by assumption.
    replace (1 - (fst (ρ O O), 0)) with (RtoC (1 - fst (ρ O O))) by clra.
    replace (fst (ρ O O), 0) with (RtoC (fst (ρ O O))) by reflexivity.
    apply Mix_S.
    (* here's probably where we need positive semidefiniteness *)
    admit.
    constructor; apply pure0.
    constructor; apply pure1.
  + simpl in *.
    unfold super, Splus.
    Msimpl.
    specialize (WF_Mixed _ H) as WF.
    repeat reduce_matrices.
    constructor.
    apply mixed_state_trace_1 in H.
    unfold trace in H. simpl in H. rewrite Cplus_0_l in H.
    rewrite H.
    specialize (@WF_Id 1%nat) as WFI. 
    replace (list2D_to_matrix [[C1]]) with ('I_ 1).     
    apply pure_id1.
    crunch_matrix. 
    bdestruct (S (S x) <? 1). omega. rewrite andb_false_r. reflexivity.
  + simpl in *.
    unfold super, Splus.
    Msimpl.
    specialize (WF_Mixed _ H) as WF.
    repeat reduce_matrices.
    constructor.
    apply mixed_state_trace_1 in H.
    unfold trace in H. simpl in H. rewrite Cplus_0_l in H.
    rewrite H.
    specialize (@WF_Id 1%nat) as WFI. 
    replace (list2D_to_matrix [[C1]]) with ('I_ 1).     
    apply pure_id1.
    crunch_matrix. 
    bdestruct (S (S x) <? 1). omega. rewrite andb_false_r. reflexivity.
  + simpl in *.
    unfold super, Splus.
    Msimpl.
    specialize (WF_Mixed _ H) as WF.
    repeat reduce_matrices.
    constructor.
    apply mixed_state_trace_1 in H.
    unfold trace in H. simpl in H. rewrite Cplus_0_l in H.
    rewrite H.
    specialize (@WF_Id 1%nat) as WFI. 
    replace (list2D_to_matrix [[C1]]) with ('I_ 1).     
    apply pure_id1.
    crunch_matrix. 
    bdestruct (S (S x) <? 1). omega. rewrite andb_false_r. reflexivity.
Admitted.

Instance Denote_Gate W1 W2 : Denote (Gate W1 W2) (Superoperator (2^⟦W1⟧) (2^⟦W2⟧)):=
    {| denote := denote_gate true |}.
Instance Denote_Gate_Correct W1 W2 : Denote_Correct (Denote_Gate W1 W2) :=
{|
    correctness := WF_Superoperator;
    denote_correct := denote_gate_correct
|}.


(* for (i,x) ∈ l, 
    swaps the position of qubits i and x in the n-qubit system 
*)
(* Requires: (i,x) ∈ l implies i < n and x < n *)
(* Requires: m <= n (m is structurally decreasing) *)
(* Invariant: m = length l *)
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

(* for l[i]=x, swaps the position of qubits i and x in the n-qubit system *)
(* Requires: length l <= n *)
(* Requires: x ∈ l implies x < n *)
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

Lemma WF_pad : forall m n (A : Square m),
      (m <= n)%nat ->
      WF_Matrix (2^m) (2^m) A ->
      WF_Matrix (2^n) (2^n) (@pad m n A).
Proof.
  intros. unfold pad.
  apply WF_kron; auto.
  rewrite <- Nat.pow_add_r.
  replace (m + (n - m))%nat with n by omega.
  reflexivity.
  rewrite <- Nat.pow_add_r.
  replace (m + (n - m))%nat with n by omega.
  reflexivity.
  apply WF_Id.
Qed.

Lemma pad_nothing : forall m A, @pad m m A = A.
Proof.
  intros.
  unfold pad.
  rewrite Nat.sub_diag.
  simpl.
  autorewrite with M_db.
  reflexivity.
Qed.

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

(*
(* Discard the qubit k in an n-qubit system *)
(* Now using move_to_0 k n instead of swap_two k 0 n *)
(* Requires: k < n *)
Definition apply_discard {n} (k : nat) : Superoperator (2^n) (2^(n-1)) :=
  let S := move_to_0 n k in 
  Splus (super ((⟨0| ⊗ Id (2^(n-1))) × S)) (super ((⟨1| ⊗ Id (2^(n-1))) × S)).

(* Discard the qubit k, assuming it has the value |0⟩ *)
Definition apply_assert0 {n} (k : nat) : Superoperator (2^n) (2^(n-1)) :=
  let S := move_to_0 n k in super ((⟨0| ⊗ Id (2^(n-1))) × S).

Definition apply_assert1 {n} (k : nat) : Superoperator (2^n) (2^(n-1)) :=
  let S := move_to_0 n k in super ((⟨1| ⊗ Id (2^(n-1))) × S).

(* Confirm transposes are in the right place *)
Definition apply_meas {n} (k : nat) : Superoperator (2^n) (2^n) :=
  let S := swap_two n 0 k in 
  fun ρ => super (S × (|0⟩⟨0| ⊗ Id (2^(n-1))) × S†) ρ 
        .+ super (S × (|1⟩⟨1| ⊗ Id (2^(n-1))) × S†) ρ.
  (* super S ∘ super (|0⟩⟨0| ⊗ Id (2^(n-1))) *)
*)

(* Trying to do measure and discard in-place *)

(* Discard the qubit k in an n-qubit system *)
(* Requires: k < n *)
Definition apply_discard {n} (k : nat) : Superoperator (2^n) (2^(n-1)) :=
  Splus (super (Id (2^k) ⊗ ⟨0| ⊗ Id (2^(n-k-1)))) 
        (super (Id (2^k) ⊗ ⟨1| ⊗ Id (2^(n-k-1)))).

(* Discard the qubit k, assuming it has the value |0⟩ *)
Definition apply_assert0 {n} (k : nat) : Superoperator (2^n) (2^(n-1)) :=
  (super (Id (2^k) ⊗ ⟨0| ⊗ Id (2^(n-k-1)))).
        
Definition apply_assert1 {n} (k : nat) : Superoperator (2^n) (2^(n-1)) :=
  (super (Id (2^k) ⊗ ⟨1| ⊗ Id (2^(n-k-1)))).

Definition apply_meas {n} (k : nat) : Superoperator (2^n) (2^n) :=
  Splus (super (Id (2^k) ⊗ |0⟩⟨0| ⊗ Id (2^(n-k-1)))) 
        (super (Id (2^k) ⊗ |1⟩⟨1| ⊗ Id (2^(n-k-1)))).

Definition super_Zero {m n} : Superoperator m n  :=
  fun _ => Zero _ _.

Definition apply_gate {n w1 w2} (safe : bool) (g : Gate w1 w2) (l : list nat) 
           : Superoperator (2^n) (2^(n+⟦w2⟧-⟦w1⟧)) :=
  match g with 
  | U u   => match ⟦w1⟧ <=? n with
            | true => apply_U (denote_unitary u) l
              | false => super_Zero
              end
  | NOT   => match 1 <=? n with
              | true => apply_U σx l (m := 1)
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
  | assert0 => match l with 
              | x :: _ => if safe then apply_discard x else apply_assert0 x 
              | _      => super_Zero
              end
  | assert1 => match l with 
              | x :: _ => if safe then apply_discard x else apply_assert1 x
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

Lemma apply_U_σ : forall m n (U : Square (2^m)),
      WF_Matrix (2^m) (2^m) U ->
      (m <= n)%nat -> 
      @apply_U m n U (σ_{n}) = super (pad n U).
Proof.
  intros. unfold apply_U.
  rewrite swap_list_n_id.
  apply WF_pad with (n := n) in H; auto.
  autorewrite with M_db.
  reflexivity.
Qed.

(** Denoting Min Circuits **)

Definition get_var (p : Pat Bit) := match p with
                                    | bit x => x
                                    end.

Definition denote_pat {w} (p : Pat w) : Matrix (2^⟦w⟧) (2^⟦w⟧) :=
  swap_list (⟦w⟧) (pat_to_list p).
Instance Denote_Pat {w} : Denote (Pat w) (Matrix (2^⟦w⟧) (2^⟦w⟧)) :=
  { denote := denote_pat }.

Print Gate_State.
(* here, the state represents the number of qubits in a system. *)
Instance nat_gate_state : Gate_State nat :=
  { get_fresh := fun _ n => (n,S n)
  ; remove_var := fun _ n => (n-1)%nat
  ; change_type := fun _ _ n => n
  ; maps_to := fun _ _ => None
  }.

Fixpoint denote_db_circuit {w} safe padding input (c : DeBruijn_Circuit w)
                         : Superoperator (2^(padding+input)) (2^(padding+⟦w⟧)) :=
  match c with
  | db_output p    => super (pad (padding+input) (⟦p⟧))
  | db_gate g p c' => let input' := process_gate_state g p input in
                      compose_super (denote_db_circuit safe padding input' c')
                                    (apply_gate safe g (pat_to_list p))
  | db_lift p c'   => let S := swap_two input 0 (get_var p) in
                      Splus (compose_super 
                               (denote_db_circuit safe padding (input-1) (c' false))
                                     (super (⟨0| ⊗ 'I_(2^(input-1)) × S)))
                             (compose_super 
                                (denote_db_circuit safe padding (input-1) (c' true))
                                     (super (⟨1| ⊗ 'I_(2^(input-1)) × S)))
  end.
                    
(*
Fixpoint denote_db_circuit {w} Γ0 Γ (c : DeBruijn_Circuit w) 
                         : Superoperator (2^(⟦Γ0⟧ + ⟦Γ⟧)) (2^(⟦Γ0⟧ + ⟦w⟧)) :=
  match c with
  | db_output p    => super (pad (⟦Γ0⟧ + ⟦Γ⟧) (⟦p⟧))
  | db_gate g p c' => let Γ' := process_gate_state g p Γ in
                      compose_super (denote_db_circuit Γ0 Γ' c')
                                    (apply_gate g (pat_to_list p))
  | db_lift p c'   => let S := swap_two (⟦Γ⟧) 0 (get_var p) in
                      let Γ' := remove_pat p Γ in
               Splus (compose_super (denote_db_circuit Γ0 Γ' (c' false))
                                    (super (⟨0| ⊗ 'I_ (2^⟦Γ'⟧) × S)))
                     (compose_super (denote_db_circuit Γ0 Γ' (c' true))
                                    (super (⟨1| ⊗ 'I_ (2^⟦Γ'⟧) × S)))
  end.
*)


(*
(* n is the input size *) 
Fixpoint denote_db_circuit {w}  (pad n : nat) (c : DeBruijn_Circuit w) 
                          : Superoperator (2^(n+pad)) (2^(⟦w⟧ + pad))
  := 
  match c with 
  | db_output p              => super (swap_list (⟦w⟧) (pat_to_list p))
  | @db_gate _ W1 W2 g p c'  => compose_super 
                                (denote_db_circuit pad (n + ⟦W2⟧ - ⟦W1⟧) c')
                                (apply_gate g (pat_to_list p))
  | db_lift p c'   =>    let S := swap_two n 0 (get_var p) in 
                         Splus (compose_super (denote_db_circuit pad (n-1) (c' false)) 
                                            (super (⟨0| ⊗ Id (2^(n-1)) × S)))
                               (compose_super (denote_db_circuit pad (n-1) (c' true)) 
                                            (super (⟨1| ⊗ Id (2^(n-1))× S)))         
  end.
*)


Definition denote_db_box {w1 w2} (safe : bool) (c : DeBruijn_Box w1 w2) := 
  match c with
  | db_box _ c' => denote_db_circuit safe 0 (⟦w1⟧) c'
  end.

(** Denoting hoas circuits **)


Definition denote_box (safe : bool) {W1 W2 : WType} (c : Box W1 W2) := 
    denote_db_box safe (hoas_to_db_box c).
Instance Denote_Box {W1 W2} : Denote (Box W1 W2) (Superoperator (2^⟦W1⟧) (2^⟦W2⟧)) :=
         {| denote := denote_box true |}.

Definition denote_circuit (safe : bool) {W : WType} (c : Circuit W) (Γ0 Γ : OCtx) := 
  denote_db_circuit safe (⟦Γ0⟧) (⟦Γ⟧) (hoas_to_db Γ c).

(* safe variant *)
Notation "⟨ Γ0 | Γ ⊩ c ⟩" := (denote_circuit true c Γ0 Γ) (at level 20).

(* unsafe variant *)
Notation "⟨! Γ0 | Γ ⊩ c !⟩" := (denote_circuit false c Γ0 Γ) (at level 20).

(*
Lemma denote_db_subst : forall pad n σ w (c : DeBruijn_Circuit w),
      denote_db_circuit pad n (subst_db σ c)
    = compose_super (denote_db_circuit pad n c)
                    (super (swap_list (length (get_σ σ)) (get_σ σ))).
Admitted.
*)

Lemma denote_output : forall Γ0 Γ {w} (p : Pat w),
    ⟨ Γ0 | Γ ⊩ output p ⟩ 
  = super (pad (⟦Γ0⟧ + ⟦Γ⟧) (denote_pat (subst_pat (OCtx_dom Γ) p))).
Proof.
  intros.
  simpl.
  unfold hoas_to_db_pat.
  reflexivity.
Qed.


Ltac fold_denote :=
  repeat match goal with
  | [ |- context[ denote_OCtx ?Γ ] ] => replace (denote_OCtx Γ) with (⟦Γ⟧); auto
  end.

Lemma size_WType_length : forall {w} (p : Pat w),
    length (pat_to_list p) = size_WType w.
Proof.
  induction p; simpl; auto.
  rewrite app_length.
  rewrite IHp1, IHp2.
  auto.
Qed.

Lemma compose_super_assoc : forall {m n p q}
      (f : Superoperator m n) (g : Superoperator n p) (h : Superoperator p q), 
      compose_super (compose_super f g) h
    = compose_super f (compose_super h h).
Admitted.

(* n is the number of inputs to c'. the number of inputs to c might be less than
that. *)
(* TODO: might need to add a hypothesis relating n1 and n2 to the actual inputs
of c1 and c2 *)
(*⟦⟧*)
(*
Lemma denote_db_compose : forall pad w1 w2 Γ1 Γ n m
                          (c1 : DeBruijn_Circuit w1) (c2 : DeBruijn_Circuit w2),
    Types_DB Γ1 c1 ->
    Types_DB (Valid (WType_to_Ctx w1 ++ Γ)) c2 ->
    
    n = (⟦Γ1⟧+ ⟦Γ⟧)%nat ->
    m = (⟦Γ⟧) ->
    
    denote_db_circuit pad n (db_compose m c1 c2)
  = compose_super (denote_db_circuit pad (⟦w1⟧+ ⟦Γ⟧) c2)
                  (denote_db_circuit (pad +⟦Γ⟧) (⟦Γ1⟧) c1).

Admitted.
*)


Lemma denote_pat_fresh_id : forall w,
      denote_pat (fresh_pat w []) = Id (2^⟦w⟧).
Proof.
  intros.
  unfold denote_pat.
  rewrite swap_fresh_seq by validate.
  unfold get_fresh_var. simpl.
  rewrite swap_list_n_id.
  reflexivity.
Qed.

Open Scope circ_scope.
Lemma hoas_to_db_pat_fresh : forall w Γ w',
      Γ = fresh_state w' ∅ ->
      hoas_to_db_pat (fresh_state w Γ) (fresh_pat w Γ) 
    = fresh_pat w (OCtx_dom Γ).
Proof.
  induction w; intros; 
    (assert (is_valid Γ) by (subst; apply is_valid_fresh; validate));
    (destruct Γ as [ | Γ]; [invalid_contradiction | ]);
    unfold hoas_to_db_pat in *; simpl in *; auto.

  * rewrite Ctx_dom_app; simpl.
    unfold subst_var.
    rewrite Nat.add_0_r.
    admit (* maps_to (length Γ) (Ctx_dom Γ ++ [length Γ]) = length Γ *).
  * admit (* same as above *).

  * f_equal.
    +admit. (* more general lemma *)
    + rewrite IHw2 with (w' := w' ⊗ w1).
      - f_equal. Search OCtx_dom fresh_state.
        rewrite OCtx_dom_fresh; auto.
        simpl.
        admit (* lemma *).
      - rewrite H.
        reflexivity.
Admitted.

Lemma hoas_to_db_pat_fresh_empty : forall w,
      hoas_to_db_pat (fresh_state w ∅) (fresh_pat w ∅)
    = fresh_pat w [].
Proof.
  intros.
  apply hoas_to_db_pat_fresh with (w' := One).
  auto.
Qed.

Lemma singleton_size : forall x w Γ, SingletonCtx x w Γ -> ⟦Γ⟧ = 1%nat.
Proof.
  induction 1; auto.
Qed.

Lemma singleton_size' : forall x w,
      ⟦Valid (singleton x w)⟧ = 1%nat.
Proof.
  intros.
  simpl.
  eapply singleton_size.
  apply singleton_singleton.
Qed.

Lemma denote_Ctx_app : forall Γ1 Γ2,
      denote_Ctx (Γ1 ++ Γ2) = (denote_Ctx Γ1 + denote_Ctx Γ2)%nat.
Proof.
  induction Γ1; intros; simpl; auto.
  destruct a; auto.
  rewrite IHΓ1; auto.
Qed.

Lemma denote_OCtx_fresh : forall w Γ,
      is_valid Γ ->
      ⟦fresh_state w Γ⟧ = (⟦Γ⟧ + ⟦w⟧)%nat.
Proof.
  induction w; intros;
    (destruct Γ as [ | Γ]; [invalid_contradiction | ]).
  * simpl. 
    rewrite denote_Ctx_app.
    auto.
  * simpl.
    rewrite denote_Ctx_app.
    auto.
  * simpl.
    omega.
  * simpl.
    rewrite IHw2 by (apply is_valid_fresh; auto).
    rewrite IHw1 by auto.
    simpl. 
    omega. 
Qed.


(* probably a more general form of this *)
Lemma denote_db_unbox : forall {w1 w2} (b : Box w1 w2),
    ⟦b⟧ = ⟨ ∅ | fresh_state w1 ∅ ⊩ unbox b (fresh_pat w1 ∅) ⟩.
Proof.
  destruct b.
  simpl. unfold denote_box.
  unfold denote_circuit.
  simpl. 
  rewrite denote_OCtx_fresh; [ | validate].
  reflexivity.
Qed.
  

Lemma merge_size : forall Γ1 Γ2,
      is_valid (Γ1 ⋓ Γ2) ->
      ⟦Γ1 ⋓ Γ2⟧ = (⟦Γ1⟧ + ⟦Γ2⟧)%nat.
Proof.
  destruct Γ1 as [ | Γ1]; [intros; invalid_contradiction | ].
  induction Γ1 as [ | [w1 | ] Γ1]; 
  intros [ | [ | [w2 | ] Γ2]] pf_valid; 
    try (simpl in pf_valid; invalid_contradiction; fail);
    auto.
  * specialize (IHΓ1 (Valid Γ2)); auto. 
    simpl in *.
    destruct (merge' Γ1 Γ2) as [ | Γ] eqn:HΓ; try invalid_contradiction.
    simpl in *.
    rewrite IHΓ1; auto. 
    apply valid_valid.
  * specialize (IHΓ1 (Valid Γ2)); auto. 
    simpl in *.
    destruct (merge' Γ1 Γ2) as [ | Γ] eqn:HΓ; try invalid_contradiction.
    simpl in *.
    rewrite IHΓ1; auto. 
    apply valid_valid.
  * specialize (IHΓ1 (Valid Γ2)); auto. 
    simpl in *.
    destruct (merge' Γ1 Γ2) as [ | Γ] eqn:HΓ; try invalid_contradiction.
    simpl in *.
    rewrite IHΓ1; auto. 
    apply valid_valid.
Qed.

Lemma types_pat_size : forall w (p : Pat w) Γ,
      Types_Pat Γ p -> (⟦w⟧ = ⟦Γ⟧)%nat.
Proof.
  induction 1; simpl; auto.
  * apply singleton_size in s. simpl in *. omega.
  * apply singleton_size in s. simpl in *. omega.
  * subst.
    rewrite merge_size; auto.
Qed.

Lemma denote_index_update : forall Γ x w w',
      index (Valid Γ) x = Some w ->
      ⟦update_at Γ x (Some w')⟧ = ⟦Γ⟧.
Proof.
  induction Γ as [ | o Γ]; intros; auto.
  destruct x; auto.
  * simpl in H. subst. auto.
  * simpl in H.
    simpl in *.
    rewrite (IHΓ _ w); auto.
Qed.

Lemma singleton_update : forall Γ W W' v,
    SingletonCtx v W Γ ->
    SingletonCtx v W' (update_at Γ v (Some W')).
Proof.
  intros Γ W W' v H.
  induction H.
  + simpl. constructor.
  + simpl. constructor.
    apply IHSingletonCtx.
Qed.

(* Remove_at lemmas may be redundant.  See update_none lemmas *)
Lemma remove_at_singleton : forall x w Γ,
      SingletonCtx x w Γ ->
      empty_Ctx (remove_at x Γ).
Proof.
  induction 1; simpl.
  * constructor.
  * constructor. auto.
Qed.

Lemma update_none_singleton : forall x w Γ,
      SingletonCtx x w Γ ->
      empty_Ctx (update_at Γ x None).
Proof.
  induction 1; simpl.
  * repeat constructor.
  * constructor. assumption.
Qed.

Lemma denote_empty_Ctx : forall Γ,
    empty_Ctx Γ ->
    ⟦Γ⟧ = 0%nat.
Proof.
  induction 1; auto.
Qed.

Lemma process_gate_Ctx_size : forall w1 w2 (g : Gate w1 w2) p (Γ : OCtx),
      (⟦w1⟧ <= ⟦Γ⟧)%nat ->
      ⟦process_gate_state g p Γ⟧ = (⟦Γ⟧ + ⟦w2⟧ - ⟦w1⟧)%nat.
Proof.
  destruct g; intros p Γ H; 
    try (simpl; omega);
    try (simpl; rewrite Nat.sub_add; auto; fail);
    try (simpl; rewrite denote_Ctx_app; simpl; omega).

  * dependent destruction p. 
    simpl. admit (* need slightly updated lemmas *).
(*
    rewrite denote_singleton_update.
    erewrite denote_singleton_update; 
      [eapply singleton_size; eauto | apply singleton_index; eauto].
*)

  * dependent destruction p. 
    simpl.
    admit (* need slightly updated lemmas *).
(*    rewrite (singleton_size _ _ _ s).
    simpl.
    unfold remove_pat. simpl.
    apply denote_empty_Ctx.
    eapply remove_at_singleton; eauto. *)
Admitted.
  


Lemma process_gate_state_merge : forall w1 w2 (g : Gate w1 w2) p Γ1 Γ2,
      Types_Pat Γ1 p ->
      process_gate_state g p (Γ1 ⋓ Γ2) = process_gate_state g p Γ1 ⋓ Γ2.
Proof.
  induction g; intros p Γ1 Γ2 types_p; auto.
  * dependent destruction p.
    dependent destruction types_p.
    rewrite merge_nil_l.
    unfold process_gate_state at 2.
    admit (* not true! *).
  * admit.
  * admit.
  * admit.
  * dependent destruction p.
    dependent destruction types_p.
    simpl.
    destruct Γ2 as [ | Γ2]; auto.
    admit (* true *).
  * dependent destruction p.
    dependent destruction types_p.
    destruct Γ2 as [ | Γ2]; auto.
    simpl.
    admit (* true *).
Admitted.

About get_fresh_pat.
Locate "_ ⊢ _ :Fun".


Lemma process_gate_nat : forall {w1 w2} (g : Gate w1 w2) (p1 p2 : Pat w1) (n : nat),
      process_gate_state g p1 n = process_gate_state g p2 n.
Proof.
  intros w1 w2 g p1 p2 n.
  unfold process_gate_state.
  destruct g; trivial.
  + dependent destruction p1.
    dependent destruction p2.
    simpl. reflexivity.
  + unfold remove_pat.
    dependent destruction p1.
    dependent destruction p2.
    simpl. reflexivity.
  + unfold remove_pat.
    dependent destruction p1.
    dependent destruction p2.
    simpl. reflexivity.
  + unfold remove_pat.
    dependent destruction p1.
    dependent destruction p2.
    simpl. reflexivity.
Qed.

Lemma denote_OCtx_merge : forall Γ Γ1 Γ2, Γ == Γ1 ∙ Γ2 -> 
                          (denote_OCtx Γ = denote_OCtx Γ1 + denote_OCtx Γ2)%nat.
Proof.
  intros Γ Γ1 Γ2 H.
  apply merge_fun_ind in H.
  induction H.
  + reflexivity.
  + rewrite plus_0_r. reflexivity.
  + inversion H. 
    - simpl. assumption.
    - simpl in *. rewrite IHmerge_ind. reflexivity.
    - simpl in *. rewrite IHmerge_ind. apply plus_n_Sm.  
Qed.      

Lemma index_merge_l : forall Γ Γ1 Γ2 n w, Γ == Γ1 ∙ Γ2 ->
                                     index Γ1 n = Some w -> 
                                     index Γ n = Some w.
Proof.
  intros Γ Γ1 Γ2 n w H H0.
  apply merge_fun_ind in H.
  generalize dependent n.
  induction H.
  + intros n H. destruct n; simpl in H; inversion H.
  + auto. 
  + intros n Hi. 
    inversion H; subst.
    - destruct n. simpl in Hi. inversion Hi.
      simpl in *.
      rewrite IHmerge_ind.
      reflexivity.
      assumption.
    - destruct n. simpl in *. assumption.
      simpl in *.
      rewrite IHmerge_ind.
      reflexivity.
      assumption.
    - destruct n. simpl in Hi. inversion Hi.
      simpl in *.
      rewrite IHmerge_ind.
      reflexivity.
      assumption.
Qed.

Lemma index_merge_r : forall Γ Γ1 Γ2 n w, Γ == Γ1 ∙ Γ2 ->
                                     index Γ2 n = Some w -> 
                                     index Γ n = Some w.
Proof.
  intros Γ Γ1 Γ2 n w H H0.
  apply (index_merge_l Γ Γ2 Γ1).
  destruct H.
  constructor.
  assumption.
  rewrite merge_comm; assumption.
  assumption.
Qed.

Lemma remove_at_merge : forall (Γ Γ1 Γ2 : Ctx) n, Γ == Γ1 ∙ Γ2 ->
       Valid (remove_at n Γ) == Valid (remove_at n Γ1) ∙ Valid (remove_at n Γ2).
Proof.
  intros Γ Γ1 Γ2 n H.
  apply merge_fun_ind in H.
  generalize dependent n.
  dependent induction H.
  + intros n.
    constructor.
    apply valid_valid.
    replace (remove_at n []) with (@nil (option WType)).    
    rewrite merge_nil_l.
    reflexivity.
    destruct n; reflexivity.
  + intros n.
    constructor.
    apply valid_valid.
    replace (remove_at n []) with (@nil (option WType)).    
    rewrite merge_nil_r.
    reflexivity.
    destruct n; reflexivity.
  + intros n.
    constructor.
    apply valid_valid.
    destruct n.
    simpl.
    apply merge_ind_fun in H0.
    destruct H0.
    apply pf_merge.
    simpl.
    edestruct IHmerge_ind with (n := n); try reflexivity.
    simpl in pf_merge.
    rewrite <- pf_merge.
    apply merge_o_ind_fun in H.
    rewrite H.
    reflexivity.
Qed.

Lemma update_none_merge : forall (Γ Γ1 Γ2 : Ctx) n, Γ == Γ1 ∙ Γ2 ->
  Valid (update_at Γ n None) == Valid (update_at Γ1 n None) ∙ 
                                Valid (update_at Γ2 n None).
Proof.
  intros Γ Γ1 Γ2 n H.
  apply merge_fun_ind in H.
  generalize dependent n.
  dependent induction H.
  - intros n.
    constructor.
    apply valid_valid.    
    replace (update_at [] n None) with (@nil (option WType)).    
    rewrite merge_nil_l.
    reflexivity.
    destruct n; reflexivity.
  - intros n.
    constructor.
    apply valid_valid.
    replace (update_at [] n None) with (@nil (option WType)).    
    rewrite merge_nil_r.
    reflexivity.
    destruct n; reflexivity.
  - intros n.
    constructor.
    apply valid_valid.
    destruct n.
    + simpl.
      apply merge_ind_fun in H0.
      destruct H0. inversion pf_merge. reflexivity.
    + simpl.
      edestruct IHmerge_ind with (n := n); try reflexivity.
    simpl in pf_merge.
    rewrite <- pf_merge.
    apply merge_o_ind_fun in H.
    rewrite H.
    reflexivity.
Qed.

Lemma remove_at_collision : forall n W (Γ Γ1 Γ2 : Ctx),  SingletonCtx n W Γ1 -> 
  Γ == Γ1 ∙ Γ2 -> denote_Ctx (remove_at n Γ2) = denote_Ctx Γ2.
Proof.
  intros n. 
  induction n.
  + intros W Γ Γ1 Γ2 H H0.
    simpl.
    destruct Γ2.
    reflexivity.
    inversion H; subst.
    destruct o. destruct H0. simpl in pf_merge. rewrite pf_merge in pf_valid.
      apply not_valid in pf_valid. contradiction.
    reflexivity.
  + intros W Γ Γ1 Γ2 H H0.
    simpl.
    destruct Γ2.
    reflexivity.
    simpl.
    inversion H; subst.
    apply merge_fun_ind in H0.
    inversion H0; subst.
    erewrite IHn.
    reflexivity.
    apply H2.
    apply merge_ind_fun. 
    apply H8.
Qed.

Lemma update_none_collision : forall n W (Γ Γ1 Γ2 : Ctx),  SingletonCtx n W Γ1 -> 
  Γ == Γ1 ∙ Γ2 -> denote_Ctx (update_at Γ2 n None) = denote_Ctx Γ2.
Proof.
  intros n. 
  induction n.
  + intros W Γ Γ1 Γ2 H H0.
    simpl.
    destruct Γ2.
    reflexivity.
    inversion H; subst.
    destruct o. destruct H0. simpl in pf_merge. rewrite pf_merge in pf_valid.
      apply not_valid in pf_valid. contradiction.
    reflexivity.
  + intros W Γ Γ1 Γ2 H H0.
    simpl.
    destruct Γ2.
    reflexivity.
    simpl.
    inversion H; subst.
    apply merge_fun_ind in H0.
    inversion H0; subst.
    erewrite IHn.
    reflexivity.
    apply H2.
    apply merge_ind_fun. 
    apply H8.
Qed.

Lemma process_gate_denote : forall {w1 w2} (g : Gate w1 w2) (p : Pat w1) Γ Γ1 Γ2,
    Γ == Γ1 ∙ Γ2 ->
    Γ1 ⊢ p :Pat -> 
    process_gate_state g p (⟦Γ⟧) = ⟦process_gate_state g p Γ⟧.
Proof.
  intros w1 w2 g p Γ Γ1 Γ2 U TP.
  unfold process_gate_state, add_fresh_state, denote_OCtx.
  destruct g; simpl; trivial.
  + unfold denote_OCtx.
    destruct U.  
    destruct pf_valid. subst. 
    simpl.
    rewrite denote_Ctx_app. 
    simpl; omega.
  + unfold denote_OCtx.
    destruct U.  
    destruct pf_valid. subst. 
    simpl.
    rewrite denote_Ctx_app. 
    simpl; omega.
  + unfold denote_OCtx.
    destruct U.  
    destruct pf_valid. subst. 
    simpl.
    rewrite denote_Ctx_app. 
    simpl; omega.
  + unfold denote_OCtx.
    destruct U.  
    destruct pf_valid. subst. 
    simpl.
    rewrite denote_Ctx_app. 
    simpl; omega.
  + dependent destruction p; simpl.
    inversion TP; subst.
    apply singleton_index in H1.
    specialize (index_merge_l Γ Γ0 Γ2 v Qubit U H1) as IM. 
    destruct Γ as [|Γ]. destruct U. apply not_valid in pf_valid. contradiction.
    specialize denote_index_update as DU. 
    eapply DU in IM.
    simpl in *. rewrite IM. 
    reflexivity.
  + dependent destruction p; simpl.
    inversion TP; subst. rename Γ0 into Γ1.
    unfold remove_pat.
    simpl.
    destruct Γ as [|Γ]. destruct U. apply not_valid in pf_valid. contradiction.
    destruct Γ2 as [|Γ2]. destruct U. simpl in pf_merge. rewrite pf_merge in *. 
      apply not_valid in pf_valid. contradiction.
    specialize (update_none_merge _ _ _ v U) as RM.
    rewrite denote_OCtx_merge with (Γ1 := Γ1) (Γ2 := Γ2) by assumption.
    rewrite denote_OCtx_merge with (Γ1 := Valid (update_at Γ1 v None)) 
                                   (Γ2 := Valid (update_at Γ2 v None)) 
                                   (Γ := Valid (update_at Γ v None)) by assumption.
    simpl.
    specialize (update_none_singleton _ _ _ H1) as E. simpl in E.
    apply denote_empty_Ctx in E. simpl in E. rewrite E.
    specialize (singleton_size _ _ _ H1) as SS. simpl in SS. rewrite SS.
    erewrite update_none_collision.
    omega.
    apply H1.
    apply U.
  + dependent destruction p; simpl.
    inversion TP; subst. rename Γ0 into Γ1.
    unfold remove_pat.
    simpl.
    destruct Γ as [|Γ]. destruct U. apply not_valid in pf_valid. contradiction.
    destruct Γ2 as [|Γ2]. destruct U. simpl in pf_merge. rewrite pf_merge in *. 
      apply not_valid in pf_valid. contradiction.
    specialize (update_none_merge _ _ _ v U) as RM.
    rewrite denote_OCtx_merge with (Γ1 := Γ1) (Γ2 := Γ2) by assumption.
    rewrite denote_OCtx_merge with (Γ1 := Valid (update_at Γ1 v None)) 
                                   (Γ2 := Valid (update_at Γ2 v None)) 
                                   (Γ := Valid (update_at Γ v None)) by assumption.
    simpl.
    specialize (update_none_singleton _ _ _ H1) as E. simpl in E.
    apply denote_empty_Ctx in E. simpl in E. rewrite E.
    specialize (singleton_size _ _ _ H1) as SS. simpl in SS. rewrite SS.
    erewrite update_none_collision.
    omega.
    apply H1.
    apply U.
  + dependent destruction p; simpl.
    inversion TP; subst. rename Γ0 into Γ1.
    unfold remove_pat.
    simpl.
    destruct Γ as [|Γ]. destruct U. apply not_valid in pf_valid. contradiction.
    destruct Γ2 as [|Γ2]. destruct U. simpl in pf_merge. rewrite pf_merge in *. 
      apply not_valid in pf_valid. contradiction.
    specialize (update_none_merge _ _ _ v U) as RM.
    rewrite denote_OCtx_merge with (Γ1 := Γ1) (Γ2 := Γ2) by assumption.
    rewrite denote_OCtx_merge with (Γ1 := Valid (update_at Γ1 v None)) 
                                   (Γ2 := Valid (update_at Γ2 v None)) 
                                   (Γ := Valid (update_at Γ v None)) by assumption.
    simpl.
    specialize (update_none_singleton _ _ _ H1) as E. simpl in E.
    apply denote_empty_Ctx in E. simpl in E. rewrite E.
    specialize (singleton_size _ _ _ H1) as SS. simpl in SS. rewrite SS.
    erewrite update_none_collision.
    omega.
    apply H1.
    apply U.
Qed.

(*
Lemma denote_gate_circuit : forall Γ0 (Γ : OCtx) Γ1 Γ1' {w1 w2 w'} 
                           (g : Gate w1 w2) p1 (f : Pat w2 -> Circuit w'),
      Γ1 ⊢ p1 :Pat ->
      Γ ⊢ f :Fun ->
      Γ1' == Γ1 ∙ Γ ->

    ⟨ Γ0 | Γ ⊩ gate g p1 f⟩ 
    = compose_super (⟨ Γ0 | process_gate_state g p1 Γ
                          ⊩f (process_gate_pat g p1 Γ) ⟩)
                    (apply_gate g (pat_to_list (hoas_to_db_pat Γ p1))).
Proof.
  intros.
  simpl. fold_denote.
  set (p1' := hoas_to_db_pat Γ p1).
  set (p2 := process_gate_pat g p1 Γ).
  rewrite (process_gate_nat _ p1' p1).
  rewrite process_gate_denote. 
  reflexivity.
Qed.
*)

Lemma denote_gate_circuit : forall {w1 w2 w'} 
      (g : Gate w1 w2) p1 (f : Pat w2 -> Circuit w') Γ0 Γ Γ1 Γ2 (* Γ Γ0,*),     
       Γ == Γ1 ∙ Γ2 -> Γ1 ⊢ p1 :Pat  ->   
  ⟨ Γ0 | Γ ⊩ gate g p1 f⟩ 
    = compose_super (⟨ Γ0 | process_gate_state g p1 Γ
                          ⊩ f (process_gate_pat g p1 Γ) ⟩)
                    (apply_gate true g (pat_to_list (hoas_to_db_pat Γ p1))).
Proof.
  intros.
  unfold denote_circuit.
  simpl; fold_denote.
  set (p1' := hoas_to_db_pat Γ p1).
  set (p2 := process_gate_pat g p1 Γ).
  rewrite (process_gate_nat _ p1' p1).
  rewrite (process_gate_denote _ _ Γ Γ1 Γ2) by assumption.   
  reflexivity.
Qed.
  
Lemma denote_gate_circuit_unsafe : forall {w1 w2 w'} 
      (g : Gate w1 w2) p1 (f : Pat w2 -> Circuit w') Γ0 Γ Γ1 Γ2 (* Γ Γ0,*),     
       Γ == Γ1 ∙ Γ2 -> Γ1 ⊢ p1 :Pat  ->   
  ⟨! Γ0 | Γ ⊩ gate g p1 f !⟩ 
    = compose_super (⟨! Γ0 | process_gate_state g p1 Γ
                          ⊩ f (process_gate_pat g p1 Γ) !⟩)
                    (apply_gate false g (pat_to_list (hoas_to_db_pat Γ p1))).
Proof.
  intros.
  unfold denote_circuit.
  simpl; fold_denote.
  set (p1' := hoas_to_db_pat Γ p1).
  set (p2 := process_gate_pat g p1 Γ).
  rewrite (process_gate_nat _ p1' p1).
  rewrite (process_gate_denote _ _ Γ Γ1 Γ2) by assumption.   
  reflexivity.
Qed.

Lemma denote_compose : forall w (c : Circuit w) Γ, Γ ⊢ c :Circ ->
     forall w' (f : Pat w -> Circuit w') (Γ0 Γ1 Γ1' : OCtx),
  Γ1 ⊢ f :Fun ->
  Γ1' == Γ1 ∙ Γ ->
      ⟨ Γ0 | Γ1' ⊩ compose c f ⟩ 
    = compose_super (⟨Γ0 | fresh_state w Γ1 ⊩ f (fresh_pat w Γ1)⟩)
                    (⟨Γ0 ⋓ Γ1 | Γ ⊩ c⟩).
Proof.
  induction 1; intros w' h Γ0 Γ3 Γ3' wf_f pf_merge.
  * simpl; fold_denote.
    admit. (* property about f being parametric *)
    (* ⟨ Γ0 | Γ1 ⋓ Γ2 ⊩ f p ⟩
    =  ⟨ Γ0 | fresh_state Γ2 ⊩ f (fresh_pat w Γ2) ⟩ ∘ ⟨ Γ1 ⊩ p ⟩ 
    *)
  * replace (compose (gate g p1 f) h) 
      with (gate g p1 (fun p2 => compose (f p2) h)) 
      by auto.
    repeat rewrite denote_gate_circuit; fold_denote.


    set (p2 := process_gate_pat g p1 Γ3').
    set (Γ3'' := process_gate_state g p1 Γ3').

    evar (Γ2 : OCtx).
    set (Γ2' := process_gate_state g p1 Γ1').
    assert (pf2 : Γ2' == Γ2 ∙ Γ) by admit.
    assert (H_p2 : Γ2 ⊢ process_gate_pat g p1 Γ3' :Pat) by admit.
    assert (H_h : Γ3 ⊢ h :Fun) by auto.
    assert (pf3 : Γ3'' == Γ3 ∙ Γ2') by admit.

    specialize (H Γ2 Γ2' (process_gate_pat g p1 Γ3') pf2 H_p2 w' h Γ0 Γ3 Γ3'' H_h pf3).
    fold p2 in H.

  (*  rewrite H. *)
    
    admit (* sort of close *).

  * admit.
Admitted.


(*********************************************************)
(* Equivalence of circuits according to their denotation *)
(*********************************************************)

Definition HOAS_Equiv {W1 W2} (b1 b2 : Box W1 W2) :=
  forall ρ, Mixed_State ρ -> ⟦b1⟧ ρ = ⟦b2⟧ ρ.

Infix "≡" := HOAS_Equiv.

Hint Unfold HOAS_Equiv : den_db.
    

(************************)
(* Hints for automation *)
(************************)

Hint Unfold apply_new0 apply_new1 apply_U apply_meas apply_discard compose_super 
     super Splus swap_list swap_two pad denote_box denote_pat : den_db.

Hint Rewrite hoas_to_db_pat_fresh_empty : proof_db.
Hint Rewrite denote_OCtx_fresh using validate : proof_db.
(* add some arithmetic *)
Hint Rewrite Nat.leb_refl : proof_db.
Hint Rewrite denote_pat_fresh_id : proof_db.
Hint Rewrite swap_fresh_seq : proof_db.
Hint Rewrite apply_U_σ pad_nothing using auto : proof_db.



