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

(* Redefining to simply be the WType size *)
Definition pat_size {W} (p : Pat W) : nat := size_WType W.

Lemma pat_size_hash_pat : forall w (p : Pat w) ls, 
      pat_size (subst_pat ls p) = pat_size p.
Proof. 
  induction p; intros; auto.
Qed.


Definition get_var (p : Pat Bit) := match p with
                                    | bit x => x
                                    end.


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

Definition denote_db_box {w1 w2} (c : DeBruijn_Box w1 w2) := 
  match c with
  | db_box _ c' => denote_db_circuit 0 (⟦w1⟧) c'  
  end.

(** Denoting hoas circuits **)


Definition denote_box {W1 W2 : WType} (c : Box W1 W2) := 
    denote_db_box (hoas_to_db_box c).
Instance Denote_Box {W1 W2} : Denote (Box W1 W2) (Superoperator (2^⟦W1⟧) (2^⟦W2⟧)) :=
         {| denote := denote_box |}.

Notation "⟨ pad | n | c | σ ⟩" := (denote_db_circuit pad n (hoas_to_db c σ)).

(*
Lemma denote_db_subst : forall pad n σ w (c : DeBruijn_Circuit w),
      denote_db_circuit pad n (subst_db σ c)
    = compose_super (denote_db_circuit pad n c)
                    (super (swap_list (length (get_σ σ)) (get_σ σ))).
Admitted.
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

(* probably a more general form of this *)
Lemma denote_db_unbox : forall {w1 w2} (b : Box w1 w2),
    ⟦b⟧ = ⟨ 0 | ⟦w1⟧ | unbox b (fresh_pat w1 (st_{0})) | st_{⟦w1⟧} ⟩.
Proof.
  destruct b.
  simpl. unfold denote_box.
  simpl.
  rewrite fresh_pat_eq'. simpl.
  reflexivity.
Qed.


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

    


Lemma denote_compose : forall {w} (c : Circuit w) Γ1,
  Types_Circuit Γ1 c ->
  forall Γ Γ1' w' (f : Pat w -> Circuit w') σ σ' p pad n,
    Γ1' == Γ1 ∙ Γ ->
    (forall (p : Pat w) Γ2 Γ2', Γ2' == Γ2 ∙ Γ -> Types_Pat Γ2 p 
                                              -> Types_Circuit Γ2' (f p)) ->
    n = (⟦Γ1⟧+ ⟦Γ⟧)%nat ->
    (p,σ') = get_fresh_pat w (remove_OCtx Γ1 σ) ->

    denote_db_circuit pad n (hoas_to_db (compose c f) σ)
(*= denote_db_circuit pad n (db_compose (⟦Γ⟧) (hoas_to_db c σ) (hoas_to_db (f p) σ')) *)
  = compose_super (denote_db_circuit pad (⟦w⟧+⟦Γ⟧) (hoas_to_db (f p) σ'))
                  (denote_db_circuit (pad + ⟦Γ⟧) (⟦Γ1⟧) (hoas_to_db c σ)).
(*
    ⟨ pad | n | compose c f | σ ⟩ 
  = compose_super (⟨pad | ⟦w⟧+⟦Γ⟧ | f p | σ'⟩)
                  (⟨pad + ⟦Γ⟧ | ⟦Γ1⟧ | c | σ⟩).
*)
Proof.
  intros.
  Print Types_Compose.
  (* ctx_c := Γ1 *) (* ctx_out := Γ1' *) (* ctx_in := Γ *)
(*  set (pf := Build_Types_Compose _ _ c f Γ1 Γ1' Γ H0 H H1). *)
  destruct H0. 
(*
  destruct Γ1 as [ | Γ1]; [simpl in pf_merge; subst; dependent destruction  pf_valid | ].
  destruct Γ as [ | Γ]; [simpl in pf_merge; subst; dependent destruction  pf_valid | ].*)
(*
  erewrite hoas_to_db_compose_correct with (types := pf); 
    [| reflexivity | rewrite surjective_pairing; eauto].
  erewrite denote_db_compose with (Γ := Γ) (Γ1 := Γ1);
    [ | admit | admit (* lemmas about typing judgments *)
    | auto
    | simpl; reflexivity ].
  simpl. 

  inversion H3. simpl.
  reflexivity.
*)

  dependent induction c.
  * dependent destruction H.
    simpl.
    admit.
  * dependent destruction H0.
    destruct Γ as [ | Γ]; [invalid_contradiction | ].
    remember (process_gate_state g p (Γ1 ⋓ Γ)) as Γ1_0.

    assert (Γ1_0_valid : is_valid Γ1_0) by admit.
    assert (Γ1_0_Γ0_valid : is_valid (Γ1_0 ⋓ Γ0)) by admit.
    assert (Γ1_size : ⟦w1⟧ = ⟦Γ1⟧) by (apply types_pat_size with (p := p); auto).
    assert (Γ1_0_size : (⟦Γ1_0⟧ = ⟦Γ1 ⋓ Γ⟧ + ⟦w2⟧ - ⟦w1⟧)%nat).
    { subst. apply process_gate_Ctx_size.
      rewrite Γ1_size.
      rewrite merge_size; auto.
      omega.
    }
    assert (Γ1_0_size' : ⟦Γ1_0⟧ = (⟦Γ⟧ + ⟦w2⟧)%nat).
    { rewrite Γ1_0_size.
      rewrite merge_size; auto.
      transitivity (⟦Γ⟧ + ⟦w2⟧ + ⟦Γ1⟧ - ⟦w1⟧)%nat;
        [ f_equal; rewrite <- plus_assoc; rewrite plus_comm; auto | ].
      transitivity (⟦Γ⟧ + ⟦w2⟧ + (⟦Γ1⟧ - ⟦w1⟧))%nat; [omega | ].
      rewrite Γ1_size.
      rewrite Nat.sub_diag.
      omega.
    }

    assert (n_size : (n + ⟦w2⟧ - ⟦w1⟧ = ⟦Γ1_0⟧ + ⟦Γ0⟧)%nat).
    { 
      rewrite Γ1_0_size.
      subst.
      rewrite merge_size; auto. 
      omega.
    }


    rewrite merge_size; auto.
    simpl.
    erewrite H with (Γ := Γ0) (p0 := p0) (σ' := σ')
                    (Γ1 := Γ1_0)
                    (*such that ⟦new Γ1⟧ = ⟦Γ1⟧ + ⟦w2⟧ - ⟦w1⟧*);
      [ | | | reflexivity | auto | auto | ];
      [ | | auto | ].
    Focus 2. 
      apply t0 with (Γ2 := process_gate_state g p Γ1); auto.
      subst. 
      apply process_gate_state_merge; auto.
      admit (* ?? *).
   Focus 2. subst. admit (*??*).

    --
    rewrite Γ1_0_size.
    rewrite merge_size; auto.

    Arguments apply_gate : clear implicits.
    idtac.
    replace (n + pad0)%nat with (⟦Γ1⟧ + ⟦Γ⟧ + (pad0 + ⟦Γ0⟧))%nat; auto.
    subst. rewrite merge_size; auto.
    rewrite (plus_comm pad0 (⟦Γ0⟧)). 
    rewrite plus_assoc. auto.

  * subst. simpl. 
    dependent destruction H0.

    erewrite H.
    -- admit.
    -- apply t0. (* Γ1 := Γ2 *)
    -- admit.
    -- admit.
    -- apply H1. (* Γ := Γ *)
    -- dependent destruction p.
       dependent destruction t.
       admit.
    -- rewrite H3. (* p := p0 *) (* σ' := σ' *)
       admit.

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

Hint Unfold apply_new0 apply_new1 apply_U apply_meas apply_discard compose_super super swap_list swap_two pad denote_box  : den_db.


