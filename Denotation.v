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

Definition denote_gate' n {w1 w2} (g : Gate w1 w2)
           : Superoperator (2^⟦w1⟧ * 2^n) (2^⟦w2⟧ * 2^n) :=
  match g with 
  | U u     => super (⟦u⟧ ⊗ Id (2^n))
  | NOT     => super (σx ⊗ Id (2^n))
  | init0   => super (|0⟩ ⊗ Id (2^n))
  | init1   => super (|1⟩ ⊗ Id (2^n))
  | new0    => super (|0⟩ ⊗ Id (2^n))
  | new1    => super (|1⟩ ⊗ Id (2^n))
  | meas    => fun ρ => super (|0⟩⟨0| ⊗ Id (2^n)) ρ .+ super (|1⟩⟨1| ⊗ Id (2^n)) ρ
  | discard => fun ρ => super (⟨0| ⊗ Id (2^n)) ρ .+ super (⟨1| ⊗ Id (2^n)) ρ
  end.

Definition denote_gate {W1 W2} (g : Gate W1 W2) : 
  Superoperator (2^⟦W1⟧) (2^⟦W2⟧) := denote_gate' 0 g.
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


Lemma WF_denote_gate : forall n W1 W2 (g : Gate W1 W2) ρ,
    WF_Matrix (2^⟦W1⟧ * 2^n) (2^⟦W1⟧ * 2^n) ρ 
 -> WF_Matrix (2^⟦W2⟧ * 2^n) (2^⟦W2⟧ * 2^n) (denote_gate' n g ρ).
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
  + simpl.
    rewrite kron_1_r.
    apply mixed_unitary.
    apply WF_σx.
    apply σx_unitary.
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

Instance Denote_Gate W1 W2 : Denote (Gate W1 W2) (Superoperator (2^⟦W1⟧) (2^⟦W2⟧)):=
    {| denote := denote_gate |}.
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

(* Discard the qubit k in an n-qubit system *)
(* Requires: k < n *)
Definition apply_discard {n} (k : nat) : Superoperator (2^n) (2^(n-1)) :=
  let S := swap_two n 0 k in 
  fun ρ => super ((⟨0| ⊗ Id (2^(n-1))) × S) ρ .+ super ((⟨1| ⊗ Id (2^(n-1))) × S) ρ.
  (* super ((⟨0| ⊗ Id (2^{n-1})) × S) *)

(* Confirm transposes are in the right place *)
Definition apply_meas {n} (k : nat) : Superoperator (2^n) (2^n) :=
  let S := swap_two n 0 k in 
  fun ρ => super (S × (|0⟩⟨0| ⊗ Id (2^(n-1))) × S†) ρ 
        .+ super (S × (|1⟩⟨1| ⊗ Id (2^(n-1))) × S†) ρ.
  (* super S ∘ super (|0⟩⟨0| ⊗ Id (2^(n-1))) *)

Definition super_Zero {m n} : Superoperator m n  :=
  fun _ => Zero _ _.

Definition apply_gate {n w1 w2} (g : Gate w1 w2) (l : list nat) 
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

Fixpoint denote_db_circuit {w} padding input (c : DeBruijn_Circuit w)
                         : Superoperator (2^(padding+input)) (2^(padding+input)) :=
  match c with
  | db_output p    => super (pad (padding+input) (⟦p⟧))
  | db_gate g p c' => let input' := process_gate_state g p input in
                      compose_super (denote_db_circuit padding input' c')
                                    (apply_gate g (pat_to_list p))
  | db_lift p c'   => let S := swap_two input 0 (get_var p) in
                      let input' := remove_pat p input in
                Splus (compose_super (denote_db_circuit padding input' (c' false))
                                     (super (⟨0| ⊗ 'I_(2^input') × S)))
                      (compose_super (denote_db_circuit padding input' (c' true))
                                     (super (⟨1| ⊗ 'I_(2^input') × S)))
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


Definition denote_db_box {w1 w2} (c : DeBruijn_Box w1 w2) := 
  match c with
  | db_box _ c' => denote_db_circuit 0 (⟦w1⟧) c'
  end.

(** Denoting hoas circuits **)


Definition denote_box {W1 W2 : WType} (c : Box W1 W2) := 
    denote_db_box (hoas_to_db_box c).
Instance Denote_Box {W1 W2} : Denote (Box W1 W2) (Superoperator (2^⟦W1⟧) (2^⟦W2⟧)) :=
         {| denote := denote_box |}.

Notation "⟨ Γ0 | Γ ⊩ c ⟩" := 
    (denote_db_circuit (⟦Γ0⟧) (⟦Γ⟧) (hoas_to_db Γ c)) (at level 20).

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


Lemma process_gate_nat : forall {w1 w2} (g : Gate w1 w2) (p1 p2 : Pat w1) (n : nat),
      process_gate_state g p1 n = process_gate_state g p2 n.
Admitted.
Lemma process_gate_denote : forall {w1 w2} (g : Gate w1 w2) (p : Pat w1) Γ,
      process_gate_state g p (⟦Γ⟧)
    = ⟦process_gate_state g p Γ⟧.
Admitted.


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


Lemma denote_Ctx_app : forall Γ1 Γ2, 
      denote_Ctx (Γ1 ++ Γ2) = (denote_Ctx Γ1 + denote_Ctx Γ2)%nat.
Proof.
  induction Γ1 as [ | [w | ] Γ1]; intros; auto.
  * simpl. rewrite IHΓ1. auto.
  * simpl. rewrite IHΓ1. auto.
Qed.



  
Lemma singleton_size : forall x w Γ, SingletonCtx x w Γ -> ⟦Γ⟧ = 1%nat.
Proof.
  induction 1; auto.
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


Lemma denote_singleton_update : forall Γ x w w',
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

Lemma remove_at_singleton : forall x w Γ,
      SingletonCtx x w Γ ->
      empty_Ctx (remove_at x Γ).
Proof.
  induction 1; simpl.
  * constructor.
  * constructor. auto.
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


Lemma denote_gate_circuit : forall {w1 w2 w'} 
      (g : Gate w1 w2) p1 (f : Pat w2 -> Circuit w') Γ0 Γ (*Γ1 Γ1' Γ Γ0,*),

      ⟨ Γ0 | Γ ⊩ gate g p1 f⟩ 
    = compose_super (⟨ Γ0 | process_gate_state g p1 Γ
                          ⊩ f (process_gate_pat g p1 Γ) ⟩)
                    (apply_gate g (pat_to_list (hoas_to_db_pat Γ p1))).
Proof.
  intros.
  simpl; fold_denote.
  set (p1' := hoas_to_db_pat Γ p1).
  set (p2 := process_gate_pat g p1 Γ).
  rewrite (process_gate_nat _ p1' p1).
  rewrite process_gate_denote. 
  reflexivity.
Qed.
  

Lemma denote_compose : forall {w} (c : Circuit w) Γ, Γ ⊢ c :Circ ->
     forall {w'} (f : Pat w -> Circuit w') (Γ0 Γ1 Γ1' : OCtx),
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
    rewrite H.
    
    admit (* sort of close *).

  * admit.
Admitted.

(*
  Types_Circuit Γ1 c ->
  forall Γ Γ1' w' (f : Pat w -> Circuit w') σ σ' p pad n,
    Γ1' == Γ1 ∙ Γ ->
    (forall (p : Pat w) Γ2 Γ2', Γ2' == Γ2 ∙ Γ -> Types_Pat Γ2 p 
                                              -> Types_Circuit Γ2' (f p)) ->
    n = (⟦Γ1⟧+ ⟦Γ⟧)%nat ->
    (p,σ') = get_fresh_pat w (remove_OCtx Γ1 σ) ->
(*    
    denote_db_circuit pad n (hoas_to_db (compose c f) σ)
(*= denote_db_circuit pad n (db_compose (⟦Γ⟧) (hoas_to_db c σ) (hoas_to_db (f p) σ')) *)
  = compose_super (denote_db_circuit pad (⟦w⟧+⟦Γ⟧) (hoas_to_db (f p) σ'))
                  (denote_db_circuit (pad + ⟦Γ⟧) (⟦Γ1⟧) (hoas_to_db c σ)).
*)
    ⟨ pad | n | compose c f | σ ⟩ 
  = compose_super (⟨pad | ⟦w⟧+⟦Γ⟧ | f p | σ'⟩)
                  (⟨pad + ⟦Γ⟧ | ⟦Γ1⟧ | c | σ⟩).
*)




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

Hint Unfold apply_new0 apply_new1 apply_U apply_meas apply_discard compose_super super swap_list swap_two pad denote_box denote_pat : den_db.


