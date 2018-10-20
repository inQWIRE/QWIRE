Require Import Program. 
Require Import Arith.
Require Import Omega.

Require Import Monad.
Require Export Contexts.
Require Export HOASCircuits.
Require Export HOASLib.
Require Export DBCircuits.
Require Export Quantum.

Require Import List.
Import ListNotations.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

Local Opaque WF_Matrix.

Class Denote source target := {denote : source -> target}.

Notation "⟦ s ⟧" := (denote s) (at level 10).

Class Denote_Correct {source target} `(Denote source target) :=
{
    correctness : target -> Prop;
    denote_correct : forall (x : source), correctness (denote x)
}.

(** Unitary Denotation **)

Instance Denote_WType : Denote WType nat := {| denote := size_wtype |}.

Instance Denote_Ctx : Denote Ctx nat := {| denote := size_ctx |}.
Instance Denote_OCtx : Denote OCtx nat := {| denote := size_octx |}.

Fixpoint denote_unitary {W} (U : Unitary W) : Square (2^⟦W⟧) :=
  match U with  
  | _H          => hadamard 
  | _X          => σx
  | _Y          => σy
  | _Z          => σz
  | _R_ ϕ       => phase_shift ϕ
  | ctrl g     => control (denote_unitary g)
  | bit_ctrl g => control (denote_unitary g)  
  end.

Instance Denote_Unitary W : Denote (Unitary W) (Square (2^⟦W⟧)) := 
    {| denote := denote_unitary |}.

Lemma WF_Matrix_U : forall {W} (U : Unitary W), 
      WF_Matrix (2^⟦W⟧) (2^⟦W⟧) (⟦U⟧).
Proof.
  induction U; simpl; auto with wf_db.
Qed.
Hint Resolve WF_Matrix_U : wf_db.
Lemma unitary_gate_unitary : forall {W} (U : Unitary W), WF_Unitary (⟦U⟧).
Proof.
  induction U.
  + apply H_unitary.
  + apply σx_unitary.
  + apply σy_unitary.
  + apply σz_unitary.
  + apply phase_unitary.
  + simpl. apply control_unitary; assumption. 
  + simpl. apply control_unitary; assumption.
Qed.

Lemma denote_unitary_transpose : forall {W} (U : Unitary W), ⟦trans U⟧ = ⟦U⟧†.
Proof.
  induction U; simpl; Msimpl; trivial. 
  - simpl_rewrite IHU. setoid_rewrite control_adjoint. easy.
  - simpl_rewrite IHU. setoid_rewrite control_adjoint. easy.
Qed.


(* Hint Resolve unitary_gate_unitary. Do we need this? Where? *)
Instance Denote_Unitary_Correct W : Denote_Correct (Denote_Unitary W) :=
{|
    correctness := fun A => WF_Unitary A;
    denote_correct := fun U => unitary_gate_unitary U
|}.


(** Gate Denotation **)

Definition denote_gate' (safe : bool) n {w1 w2} (g : Gate w1 w2)
           : Superoperator (2^⟦w1⟧ * 2^n) (2^⟦w2⟧ * 2^n) :=
  match g with 
  | U u     => super (⟦u⟧ ⊗ Id (2^n))
  | BNOT     => super (σx ⊗ Id (2^n))
  | init0   => super (|0⟩ ⊗ Id (2^n))
  | init1   => super (|1⟩ ⊗ Id (2^n))
  | new0    => super (|0⟩ ⊗ Id (2^n))
  | new1    => super (|1⟩ ⊗ Id (2^n))
  | meas    => Splus (super (|0⟩⟨0| ⊗ Id (2^n))) (super (|1⟩⟨1| ⊗ Id (2^n)))
  | measQ   => Splus (super (|0⟩⟨0| ⊗ Id (2^n))) (super (|1⟩⟨1| ⊗ Id (2^n)))
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
  specialize (WF_Matrix_U u). intros wf_u. auto with wf_db.
  specialize (WF_Matrix_U u). intros wf_u. auto with wf_db.
Qed.
Hint Resolve WF_denote_gate : wf_db.

Close Scope circ_scope.
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
    apply unitary_gate_unitary.
    assumption.
  + simpl.
    rewrite kron_1_r.
    apply mixed_unitary.
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
    unfold Splus.
    replace (|0⟩⟨0| × ρ × |0⟩⟨0|) with (ρ 0%nat 0%nat .* |0⟩⟨0|) by solve_matrix.
    replace (|1⟩⟨1| × ρ × |1⟩⟨1|) with (ρ 1%nat 1%nat .* |1⟩⟨1|) by solve_matrix.
    specialize (mixed_state_trace_1 _ H) as TR1. unfold trace in TR1. simpl in TR1.
    replace (ρ 1%nat 1%nat) with (1 - ρ O O) by (rewrite <- TR1; clra).
    replace (ρ O O) with ((fst (ρ O O)), snd (ρ O O)) by clra. 
    rewrite mixed_state_diag_real by assumption.
    set (a := (ρ 0 0)%nat). replace (ρ 0 0)%nat with a in TR1 by reflexivity.
    set (b := (ρ 1 1)%nat). replace (ρ 1 1)%nat with b in TR1 by reflexivity.
    replace (1 - (fst a, 0)) with (RtoC (1 - fst a)) by clra.
    replace (fst a, 0) with (RtoC (fst a)) by reflexivity.
    destruct (Ceq_dec a C0) as [Z | NZ]; [|destruct (Ceq_dec a C1) as [O | NO]].
    * rewrite Z in *.
      rewrite Mscale_0.
      rewrite Mplus_0_l.
      simpl. autorewrite with R_db.
      rewrite Mscale_1.
      apply Pure_S.
      apply pure1.
    * rewrite O in *.
      rewrite Mscale_1.
      simpl. unfold Rminus. rewrite Rplus_opp_r.
      rewrite Mscale_0.
      rewrite Mplus_0_r.
      apply Pure_S.
      apply pure0.
    * apply Mix_S; [| apply Pure_S, pure0| apply Pure_S, pure1].     
      unfold a in *.
      specialize (mixed_state_diag_in01 ρ 0%nat H) as IN01.
      destruct IN01 as [G L].
      destruct G. 
        Focus 2. 
        contradict NZ; apply c_proj_eq. 
        rewrite <- H0; reflexivity.
        apply mixed_state_diag_real; easy.
      destruct L. 
        Focus 2. 
        contradict NO; apply c_proj_eq. 
        rewrite <- H1; reflexivity.
        apply mixed_state_diag_real; easy.
      lra.
  + simpl in *.
    rewrite kron_1_r.
    unfold super.
    Msimpl.
    specialize (WF_Mixed _ H) as WF.
    unfold Splus.
    replace (|0⟩⟨0| × ρ × |0⟩⟨0|) with (ρ 0%nat 0%nat .* |0⟩⟨0|) by solve_matrix.
    replace (|1⟩⟨1| × ρ × |1⟩⟨1|) with (ρ 1%nat 1%nat .* |1⟩⟨1|) by solve_matrix.
    specialize (mixed_state_trace_1 _ H) as TR1. unfold trace in TR1. simpl in TR1.
    replace (ρ 1%nat 1%nat) with (1 - ρ O O) by (rewrite <- TR1; clra).
    replace (ρ O O) with ((fst (ρ O O)), snd (ρ O O)) by clra. 
    rewrite mixed_state_diag_real by assumption.
    replace (1 - (fst (ρ O O), 0)) with (RtoC (1 - fst (ρ O O))) by clra.
    replace (fst (ρ O O), 0) with (RtoC (fst (ρ O O))) by reflexivity.
    specialize (mixed_state_diag_in01 _ O H) as in01.
    destruct in01 as [[L|E0] [R|E1]]. 
    * apply Mix_S. easy. apply Pure_S. apply pure0. apply Pure_S. apply pure1.
    * rewrite E1. unfold Rminus. rewrite Rplus_opp_r. 
      rewrite Mscale_0, Mscale_1. rewrite Mplus_0_r. apply Pure_S. apply pure0. 
    * rewrite <- E0. rewrite Rminus_0_r. 
      rewrite Mscale_0, Mscale_1. rewrite Mplus_0_l. apply Pure_S. apply pure1. 
    * lra.      
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
Qed.

Instance Denote_Gate W1 W2 : Denote (Gate W1 W2) (Superoperator (2^⟦W1⟧) (2^⟦W2⟧)):=
    {| denote := denote_gate true |}.
Instance Denote_Gate_Correct W1 W2 : Denote_Correct (Denote_Gate W1 W2) :=
{|
    correctness := WF_Superoperator;
    denote_correct := denote_gate_correct
|}.


(* for (i,j) ∈ l, 
    swaps the position of qubits i and x in the n-qubit system 
*)
(* Requires: (i,j) ∈ l implies i < n and j < n *)
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

(* These propositions about swap_list may prove useful
Proposition swap_list_spec_1 : forall n i j (A1 : Square (2^i)%nat) (A2 : Square (2^j)%nat)
  (U : Square (2^1)%nat) (ρ : Square (2^1)%nat), (i + j + 1 = n)%nat ->
  super (swap_list n [i] × pad n U × (swap_list n [i])†) (A1 ⊗ ρ ⊗ A2) = 
  A1 ⊗ (super U ρ) ⊗ A2.

Proposition swap_list_spec_2 : forall n i j k 
  (A1 : Square (2^i)%nat) (A2 : Square (2^j)%nat) (A3 : Square (2^k)%nat)   
  (U : Square (2^2)%nat) (ρ1 ρ2 ρ1' ρ2': Square (2^1)%nat), (i + j + k + 2 = n)%nat ->
  (super U (ρ1 ⊗ ρ2)) = ρ1' ⊗ ρ2' -> 
  super (swap_list n [i; (i+j+1)%nat] × pad n U × (swap_list n [i; (i+j+1)%nat])†) 
    (A1 ⊗ ρ1 ⊗ A2 ⊗ ρ2 ⊗ A3) = A1 ⊗ ρ1' ⊗ A2 ⊗ ρ2' ⊗ A3.

Proposition swap_list_shift : forall n (ρ : Square (2^1)%nat) (A : Square (2^n)),
  super (swap_list (S n) (seq 1 n ++ [O])) (ρ ⊗ A) = A ⊗ ρ.

Proposition swap_list_shift' : forall (n : nat) (ρ : Square 2) (A : Square (2^n)%nat),
  super (swap_list (S n) (n :: seq 0 n)) (A ⊗ ρ) = ρ ⊗ A.
*)

(***********************************)
(* Swap structures are well-formed *)
(***********************************)

(* Note that these are based on the proofs of unitarity below.
   In fact, we can use the proofs of unitary in their place 
   (or use the WF proofs in those) *)

Lemma WF_swap_to_0_aux : forall n i, 
  (i + 1 < n)%nat ->
  WF_Matrix (2^n) (2^n) (swap_to_0_aux n i).
Proof.
  intros n i H.
  gen n.
  induction i; intros n H; simpl.
  - auto with wf_db.
  - replace (2^n)%nat with ((2 ^ i + (2 ^ i + 0)) * 4 * 2 ^ (n - S i - 2))%nat by
        unify_pows_two.
    apply WF_mult; auto with wf_db.
    apply WF_mult; auto with wf_db.
    unify_pows_two.
    replace (i + 1 + 2 + (n - S i - 2))%nat with n by omega.
    apply IHi; omega.
Qed.

Lemma WF_swap_to_0 : forall i n, (i < n)%nat -> WF_Matrix (2^n) (2^n) (swap_to_0 n i).
Proof.
  intros i n L.
  unfold swap_to_0.
  destruct i; auto with wf_db.
  apply WF_swap_to_0_aux.
  omega.
Qed.  

Lemma WF_swap_two_aux : forall n i j, (i < j < n)%nat -> 
                                 WF_Matrix (2^n) (2^n)  (swap_two_aux n i j).
Proof.
  intros n i.
  gen n.
  induction i.
  - intros; simpl.
    apply WF_swap_to_0.
    omega.
  - intros n j [Lij Ljn].
    simpl.
    destruct n; try omega.
    rewrite <- (Nat.add_1_l n).
    rewrite minus_plus.
    apply WF_kron; unify_pows_two; auto with wf_db.
    apply IHi.
    omega.
Qed.
    
Lemma WF_swap_two : forall n i j, (i < n)%nat -> (j < n)%nat ->
                             WF_Matrix (2^n) (2^n) (swap_two n i j).
Proof.
  intros n i j Lin Ljn.
  unfold swap_two.
  bdestruct (i =? j). apply id_unitary.
  bdestruct (i <? j).
  apply WF_swap_two_aux. omega.
  apply WF_swap_two_aux. omega.
Qed.  

Lemma WF_swap_list_aux : forall m n l, 
   (forall i j, In (i,j) l -> (i < n)%nat /\ (j < n)%nat) ->
   (m <= n)%nat -> 
   WF_Matrix (2^n) (2^n) (swap_list_aux m n l).
Proof.
  intros m n l Lall Lmn.
  gen l.
  induction m; intros l Lall.
  - simpl. auto with wf_db.
  - simpl.
    destruct l.
    apply id_unitary; auto with wf_db.
    destruct p.
    apply WF_mult.     
    destruct (Lall n0 n1); simpl; auto.
    apply WF_swap_two; easy.
    apply IHm.
    omega.
    intros x y IN.
    split. (* This shouldn't be hard... *)
    + induction l.
      easy.
      destruct IN.
      destruct a.
      simpl in *.
      destruct (n0 =? n3).
      inversion H; subst. clear H.
      edestruct Lall.
      right. left. reflexivity.
      easy.
      inversion H; subst. clear H.
      edestruct Lall.
      right. left. reflexivity.
      easy.
      apply IHl.
      intros. 
      apply Lall.
      destruct H0.
      left. easy.
      right. right. easy.
      apply H.
    + induction l.
      easy.
      destruct IN.
      destruct a.
      simpl in *.
      destruct (n0 =? n3).
      inversion H; subst. clear H.
      edestruct Lall.
      left. reflexivity.
      easy.
      inversion H; subst. clear H.
      edestruct Lall.
      right. left. reflexivity.
      easy.
      apply IHl.
      intros. 
      apply Lall.
      destruct H0.
      left. easy.
      right. right. easy.
      apply H.
Qed.

Lemma WF_swap_list : forall n l, (length l <= n)%nat -> 
                            (forall x, In x l -> x < n)%nat ->
                            WF_Matrix (2^n) (2^n) (swap_list n l).
Proof.
  intros n l len Lall.
  unfold swap_list.
  apply WF_swap_list_aux; try omega.
  intros i j IN.
  split.
  - unfold zip_to in *.
    apply in_combine_l in IN.
    apply in_seq in IN.
    omega.
  - unfold zip_to in *.
    apply in_combine_r in IN.
    apply Lall.
    apply IN.
Qed.

(*******************************)
(* Swap structures are unitary *)
(*******************************)

Lemma swap_to_0_aux_unitary : forall n i, 
  (i + 1 < n)%nat ->
  WF_Unitary (swap_to_0_aux n i).
Proof.
  intros n i H.
  induction i; simpl.
  - specialize (kron_unitary swap ('I_(2^(n-2))))%nat.
    unify_pows_two. rewrite <- le_plus_minus.
    intros KU.
    apply KU.
    apply swap_unitary.
    apply id_unitary.
    omega.
  - unify_pows_two.
    replace (2^n)%nat with (2^(i + 1 + 2 + (n - S i - 2)))%nat by
      (apply f_equal2; trivial; try omega).
    Set Printing Implicit.
    apply Mmult_unitary.
    apply Mmult_unitary.
    rewrite Nat.pow_add_r.
    apply kron_unitary.
    rewrite Nat.pow_add_r.
    apply kron_unitary.
    apply id_unitary.
    apply swap_unitary.
    apply id_unitary.
    replace (2^(i + 1 + 2 + (n - S i - 2)))%nat with (2^n)%nat by
      (apply f_equal2; trivial; try omega).
    apply IHi.
    omega.
    rewrite Nat.pow_add_r.
    apply kron_unitary.
    rewrite Nat.pow_add_r.
    apply kron_unitary.
    apply id_unitary.
    apply swap_unitary.
    apply id_unitary.
    Unset Printing Implicit.
Qed.

Lemma swap_to_0_unitary : forall i n, (i < n)%nat -> WF_Unitary (swap_to_0 n i).
Proof.
  intros i n L.
  unfold swap_to_0.
  destruct i. 
  apply id_unitary.
  apply swap_to_0_aux_unitary.
  omega.
Qed.  

Lemma swap_two_aux_unitary : forall n i j, (i < j < n)%nat -> 
                                      WF_Unitary (swap_two_aux n i j).
Proof.
  intros n i.
  gen n.
  induction i.
  - intros; simpl.
    apply swap_to_0_unitary.
    omega.
  - intros n j [Lij Ljn].
    simpl.
    destruct n; try omega.
    rewrite <- (Nat.add_1_l n).
    rewrite minus_plus.
    apply kron_unitary.
    apply id_unitary.
    apply IHi.
    omega.
Qed.
    
Lemma swap_two_unitary : forall n i j, (i < n)%nat -> (j < n)%nat ->
                                  WF_Unitary (swap_two n i j).
Proof.
  intros n i j Lin Ljn.
  unfold swap_two.
  bdestruct (i =? j). apply id_unitary.
  bdestruct (i <? j).
  apply swap_two_aux_unitary. omega.
  apply swap_two_aux_unitary. omega.
Qed.  

Lemma swap_list_aux_unitary : forall m n l, 
   (forall i j, In (i,j) l -> (i < n)%nat /\ (j < n)%nat) ->
   (m <= n)%nat -> 
  WF_Unitary (swap_list_aux m n l).
Proof.
  intros m n l Lall Lmn.
  gen l.
  induction m; intros l Lall.
  - simpl.
    apply id_unitary.
  - simpl.
    destruct l.
    apply id_unitary.
    destruct p.
    apply Mmult_unitary.
    destruct (Lall n0 n1); simpl; auto.
    apply swap_two_unitary; easy.
    apply IHm.
    omega.
    intros x y IN.
    split. (* This shouldn't be hard... *)
    + induction l.
      easy.
      destruct IN.
      destruct a.
      simpl in *.
      destruct (n0 =? n3).
      inversion H; subst. clear H.
      edestruct Lall.
      right. left. reflexivity.
      easy.
      inversion H; subst. clear H.
      edestruct Lall.
      right. left. reflexivity.
      easy.
      apply IHl.
      intros. 
      apply Lall.
      destruct H0.
      left. easy.
      right. right. easy.
      apply H.
    + induction l.
      easy.
      destruct IN.
      destruct a.
      simpl in *.
      destruct (n0 =? n3).
      inversion H; subst. clear H.
      edestruct Lall.
      left. reflexivity.
      easy.
      inversion H; subst. clear H.
      edestruct Lall.
      right. left. reflexivity.
      easy.
      apply IHl.
      intros. 
      apply Lall.
      destruct H0.
      left. easy.
      right. right. easy.
      apply H.
Qed.


(* for l[i]=x, swaps the position of qubits i and x in the n-qubit system *)
(* Requires: length l <= n *)
(* Requires: x ∈ l implies x < n *)

Lemma swap_list_unitary : forall n l, (length l <= n)%nat -> 
                                 (forall x, In x l -> x < n)%nat ->
                                 WF_Unitary (swap_list n l).
Proof.
  intros n l len Lall.
  unfold swap_list.
  apply swap_list_aux_unitary; try omega.
  intros i j IN.
  split.
  - unfold zip_to in *.
    apply in_combine_l in IN.
    apply in_seq in IN.
    omega.
  - unfold zip_to in *.
    apply in_combine_r in IN.
    apply Lall.
    apply IN.
Qed.

(*** Applying Unitaries to Systems ***)

(* Dummy matrices and superoperators *)
Definition dummy_mat {m n} : Matrix m n. exact (Zero m n). Qed.
Definition dummy_so {m n} : Superoperator m n. exact (fun _ => dummy_mat). Qed.

Definition super_Zero {m n} : Superoperator m n  :=
  fun _ => Zero n n.

Definition apply_to_first {m n} (f : nat -> Superoperator m n) (l : list nat) :
  Superoperator m n :=
  match l with
  | x :: _ => f x 
  | []     => dummy_so
  end.

(* Might be nice to make this use dummy matrices at some point.
   See ctrls_to_list_empty and denote_ctrls_empty, however *)
Fixpoint ctrls_to_list {W} (lb : list bool) (l : list nat) (g : Unitary W) {struct g}: 
  (nat * list bool * Square 2) :=
  match g with
  | ctrl g'     => match l with 
                  | n :: l' => let (res,u) := ctrls_to_list lb l' g' in
                                let (k,lb') := res in
                                  (k,update_at lb' n true, u)  
                  | _       => (O,[],Zero _ _)
                  end
  | bit_ctrl g' => match l with 
                  | n :: l' => let (res,u) := ctrls_to_list lb l' g' in
                                let (k,lb') := res in
                                (k,update_at lb' n true, u)  
                  | _       => (O,[],Zero _ _)
                  end
  | u           => match l with
                  | k :: l' => (k,lb,⟦u⟧)
                  | _       => (O,[],Zero _ _)
                  end
  end.

Fixpoint ctrl_list_to_unitary_r (r : list bool) (u : Square 2) : 
  (Square (2^(length r + 1))) := 
  match r with 
  | false :: r' =>  ctrl_list_to_unitary_r r' u ⊗ Id 2
  | true  :: r' =>  ctrl_list_to_unitary_r r' u ⊗ |1⟩⟨1| .+ Id _ ⊗ |0⟩⟨0|
  | []          => u
  end.

Fixpoint ctrl_list_to_unitary (l r : list bool) (u : Square 2) : 
  (Square (2^(length l + length r + 1))) := 
  match l with 
  | false :: l' => Id 2 ⊗ ctrl_list_to_unitary l' r u
  | true  :: l' => |1⟩⟨1| ⊗ ctrl_list_to_unitary l' r u .+ |0⟩⟨0| ⊗ Id _
  | []          => ctrl_list_to_unitary_r r u
  end.

Definition denote_ctrls {W} (n : nat) (g : Unitary W) (l : list nat) : Matrix (2^n) (2^n) := 
  let (res, u) := ctrls_to_list (repeat false n) l g in
  let (k, lb) := res in
  let ll := firstn k lb in
  let lr := rev (skipn (S k) lb) in 
  ctrl_list_to_unitary ll lr u. 

(* Apply U to qubit k in an n-qubit system *)
(* Requires: k < n *)
Definition apply_qubit_unitary {n} (U : Matrix 2 2) (k : nat) 
  : Superoperator (2^n) (2^n) := (super (Id (2^k) ⊗ U ⊗ Id (2^(n-k-1)))).

(* New in-place version of apply_U *)
Definition apply_U {W} (n : nat) (U : Unitary W) (l : list nat) 
           : Superoperator (2^n) (2^n) :=
  match W with
  | Qubit => apply_to_first (apply_qubit_unitary (⟦U⟧)) l
  | _     => super (denote_ctrls n U l)
  end.

(* In case we add other multi-qubit unitaries 
Fixpoint apply_U {W} (n : nat) (U : Unitary W) (l : list nat) 
           : Superoperator (2^n) (2^n) :=
  match U with
  | _H          => apply_to_first (apply_qubit_unitary hadamard) l
  | _X          => apply_to_first (apply_qubit_unitary σx) l
  | _Y          => apply_to_first (apply_qubit_unitary σy) l
  | _Z          => apply_to_first (apply_qubit_unitary σz) l
  | _R_ ϕ       => apply_to_first (apply_qubit_unitary (phase_shift ϕ)) l
  | ctrl g     => super (denote_ctrls n U l)  
  | bit_ctrl g => 
  end.
*)

(***********************************)
(* Lemmas about applying unitaries *)
(***********************************)

Lemma ctrl_list_to_unitary_r_false : forall n (u : Matrix 2 2),
  ctrl_list_to_unitary_r (repeat false n) u = u ⊗ 'I_ (2^n).
Proof.
  induction n; intros.
  - simpl. Msimpl. reflexivity.
  - intros.
    simpl.
    rewrite IHn.
    setoid_rewrite kron_assoc.
    rewrite id_kron.
    unify_pows_two.
    reflexivity.
Qed.

Lemma ctrl_list_to_unitary_false : forall m n (u : Matrix 2 2),
  WF_Matrix 2 2 u ->
  ctrl_list_to_unitary (repeat false m) (repeat false n) u = 'I_ (2^m) ⊗ u ⊗ 'I_ (2^n).
Proof.
  induction m; intros.
  - simpl. Msimpl. apply ctrl_list_to_unitary_r_false. 
  - simpl.
    rewrite IHm by easy.
    Msimpl.
    repeat rewrite repeat_length.
    match goal with
    | |- context [ @kron ?a1 ?a2 ?bc1 ?bc2 ?A (@kron ?b1 ?b2 ?c1 ?c2 ?B ?C)] => idtac B; 
      replace bc1 with (b1 * c1)%nat by (unify_pows_two); 
      replace bc2 with (b2 * c2)%nat by (unify_pows_two);
      rewrite <- (kron_assoc a1 a2 b1 b2 c1 c2 A B C)
    end.
    match goal with
    | |- context [ @kron ?a1 ?a2 ?bc1 ?bc2 ?A (@kron ?b1 ?b2 ?c1 ?c2 ?B ?C)] => idtac B; 
      replace bc1 with (b1 * c1)%nat by (unify_pows_two); 
      replace bc2 with (b2 * c2)%nat by (unify_pows_two);
      rewrite <- (kron_assoc a1 a2 b1 b2 c1 c2 A B C)
    end.
    rewrite id_kron.
    unify_pows_two.
    repeat rewrite Nat.add_1_r.
    reflexivity.
Qed.
         
Lemma ctrls_to_list_empty  : forall W lb u, @ctrls_to_list W lb [] u = (O, [], Zero 2 2).
Proof. destruct u; easy. Qed.  

Lemma denote_ctrls_empty : forall W (n : nat) (u : Unitary W),
  denote_ctrls n u [] = Zero (2^n) (2^n).
Proof. destruct u; cbv; easy. Qed.

(*
Lemma denote_ctrls_ctrl_u : forall (u : Unitary Qubit), denote_ctrls 2 (ctrl u) [0%nat;1%nat] = (control (denote u)). 
Proof.
  intros.
  dependent destruction u.
  - unfold denote_ctrls; simpl; solve_matrix.
  - unfold denote_ctrls; simpl; solve_matrix.
  - unfold denote_ctrls; simpl; solve_matrix.
  - unfold denote_ctrls; simpl; solve_matrix.
  - unfold denote_ctrls; simpl; solve_matrix.
Qed.

Lemma denote_ctrls_ctrl_u' : forall (u : Unitary Qubit), denote_ctrls 2 (ctrl u) [1%nat;0%nat] = swap × (control (denote u)) × swap. 
Proof.
  intros.
  dependent destruction u.
  - unfold denote_ctrls; simpl; solve_matrix.
  - unfold denote_ctrls; simpl; solve_matrix.
  - unfold denote_ctrls; simpl; solve_matrix.
  - unfold denote_ctrls; simpl; solve_matrix.
  - unfold denote_ctrls; simpl; solve_matrix.
Qed.
*)

Lemma denote_ctrls_qubit : forall n (u : Unitary Qubit) k,
  (k < n)%nat ->
  denote_ctrls n u [k] = 'I_ (2^k) ⊗ ⟦u⟧ ⊗ 'I_ (2^(n-k-1)).
Proof.
  intros n u k L.
  remember Qubit as W.
  induction u.
  Opaque rev skipn.
  1-5: unfold denote_ctrls; simpl;
       rewrite firstn_repeat_le, skipn_repeat, rev_repeat by omega;
       rewrite ctrl_list_to_unitary_false; auto with wf_db;
       rewrite Nat.sub_succ_r, Nat.sub_1_r;
       reflexivity.
  1-2: inversion HeqW.
Qed.

Lemma ctrl_list_to_unitary_r_unitary : forall r (u : Square 2), WF_Unitary u -> 
                                                           WF_Unitary (ctrl_list_to_unitary_r r u).
Proof.
  intros r u Uu.
  induction r; auto.
  simpl.
  destruct a.
  - simpl.
    assert (H : forall n (U : Square n), WF_Unitary U -> WF_Unitary (U ⊗ |1⟩⟨1| .+ 'I_n ⊗ |0⟩⟨0|)).
    intros n U [WFU UU].
    unfold WF_Unitary.
    split; auto with wf_db.
    Msimpl.
    rewrite Mmult_plus_distr_r, Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_l.
    Msimpl.
    rewrite UU.
    replace (|0⟩⟨0| × |1⟩⟨1|) with (Zero 2 2) by solve_matrix.
    replace (|1⟩⟨1| × |0⟩⟨0|) with (Zero 2 2) by solve_matrix.
    repeat rewrite kron_0_r.
    rewrite Mplus_0_r, Mplus_0_l.
    rewrite <- kron_plus_distr_l.
    replace (|1⟩⟨1| × |1⟩⟨1| .+ |0⟩⟨0| × |0⟩⟨0|) with ('I_2) by solve_matrix.
    rewrite id_kron.
    reflexivity.
    specialize (H _ (ctrl_list_to_unitary_r r u)).
    rewrite Nat.mul_comm in H.
    apply H.
    apply IHr.
  - specialize (kron_unitary _ ('I_ 2) IHr) as H.
    rewrite Nat.mul_comm in H.
    apply H.
    apply id_unitary. 
Qed.

Lemma ctrl_list_to_unitary_unitary : forall l r (u : Square 2), WF_Unitary u ->
                                                           WF_Unitary (ctrl_list_to_unitary l r u).
Proof.
  intros l r u Uu.
  induction l.
  - simpl. apply ctrl_list_to_unitary_r_unitary. easy.
  - simpl.
    destruct a.
    + simpl.
      assert (H : forall n (U : Square n), WF_Unitary U -> WF_Unitary (|1⟩⟨1| ⊗ U .+ |0⟩⟨0| ⊗ ('I_n))).
      intros n U [WFU UU].
      unfold WF_Unitary.
      split; auto with wf_db.
      Msimpl.
      rewrite Mmult_plus_distr_l, Mmult_plus_distr_r.
      rewrite Mmult_plus_distr_r.
      Msimpl.
      setoid_rewrite kron_mixed_product.
      rewrite UU.
      replace (|0⟩⟨0| × |1⟩⟨1|) with (Zero 2 2) by solve_matrix.
      replace (|1⟩⟨1| × |0⟩⟨0|) with (Zero 2 2) by solve_matrix.
      repeat rewrite kron_0_l.
      rewrite Mplus_0_r, Mplus_0_l.
      Msimpl. 
      rewrite <- kron_plus_distr_r.
      replace (|1⟩⟨1| × |1⟩⟨1| .+ |0⟩⟨0| × |0⟩⟨0|) with ('I_2) by solve_matrix.
      rewrite id_kron.
      reflexivity.
      specialize (H _ (ctrl_list_to_unitary l r u)).
      apply H.
      apply IHl.
    + specialize (kron_unitary _ _ (id_unitary 2) IHl) as H.
      apply H.
Qed.

Lemma ctrls_to_list_spec : forall W l (g : Unitary W) k lb lb' u, 
  (length l = ⟦W⟧)%nat ->
  ctrls_to_list lb l g = (k, lb', u) ->
  @WF_Unitary 2 u /\ length lb' = length lb /\ In k l.
Proof.
  intros W l g.
  gen l.
  induction g; simpl in *; intros l k lb lb' u L H.
  - destruct l; inversion L. inversion H; subst. split. rewrite H1. apply H_unitary. 
    split. easy. constructor. easy.
  - destruct l; inversion L. inversion H; subst. split. rewrite H1. apply σx_unitary. 
    split. easy. constructor. easy.
  - destruct l; inversion L. inversion H; subst. split. rewrite H1. apply σy_unitary. 
    split. easy. constructor. easy.
  - destruct l; inversion L. inversion H; subst. split. rewrite H1. apply σz_unitary. 
    split. easy. constructor. easy.
  - destruct l; inversion L. inversion H; subst. split. rewrite H1. 
    apply phase_unitary. split. easy. constructor. easy.
  - destruct l; inversion L.
    destruct (ctrls_to_list lb l g) as [[k' lb''] u'] eqn:E.
    inversion H; subst.
    rewrite update_length.    
    specialize (IHg l k lb lb'' u H1 E) as [U [LE I]].
    split; [|split]; trivial.
    right. easy.
  - destruct l; inversion L.
    destruct (ctrls_to_list lb l g) as [[k' lb''] u'] eqn:E.
    inversion H; subst.
    rewrite update_length.    
    specialize (IHg l k lb lb'' u H1 E) as [U [LE I]].
    split; [|split]; trivial.
    right. easy.
Qed.    

Lemma denote_ctrls_unitary : forall W n (g : Unitary W) l, 
    (forallb (fun x => x <? n) l = true) -> 
    (length l = ⟦W⟧)%nat ->
    WF_Unitary (denote_ctrls n g l).
Proof.
  intros W n g l H H0.
  unfold denote_ctrls. simpl.
  destruct (ctrls_to_list (repeat false n) l g) as [[k lb] u] eqn:E.
  apply ctrls_to_list_spec in E as [Uu [L I]]; trivial.
  apply forallb_forall with (x := k) in H; trivial.
  apply Nat.ltb_lt in H.
  specialize (ctrl_list_to_unitary_unitary (firstn k lb) (rev (skipn (S k) lb)) u Uu) 
    as U.  
  assert (E: (length (firstn k lb) + length (rev (skipn (S k) lb)) + 1 = n)%nat).
  rewrite firstn_length_le.
  rewrite rev_length.
  rewrite skipn_length.
  rewrite L, repeat_length. omega.
  rewrite L, repeat_length. omega.
  rewrite E in U.
  apply U.
Qed.

Lemma denote_ctrls_transpose_qubit : forall (n : nat) (u : Unitary Qubit) (li : list nat),
  denote_ctrls n (trans u) li = (denote_ctrls n u li)†.
Proof.
  intros.
  destruct li as [| k li].
  rewrite 2 denote_ctrls_empty. rewrite zero_adjoint_eq. easy.
  dependent destruction u.
  - simpl.
    unfold denote_ctrls. subst; clear.
    unfold ctrls_to_list.
    rewrite skipn_repeat, rev_repeat, firstn_repeat.
    simpl. rewrite ctrl_list_to_unitary_false by (auto with wf_db).    
    repeat setoid_rewrite kron_adjoint.
    Msimpl.
    reflexivity.
  - simpl.
    unfold denote_ctrls. subst; clear.
    unfold ctrls_to_list.
    rewrite skipn_repeat, rev_repeat, firstn_repeat.
    simpl. rewrite ctrl_list_to_unitary_false by (auto with wf_db).    
    repeat setoid_rewrite kron_adjoint.
    Msimpl.
    reflexivity.
  - simpl.
    unfold denote_ctrls. subst; clear.
    unfold ctrls_to_list.
    rewrite skipn_repeat, rev_repeat, firstn_repeat.
    simpl. rewrite ctrl_list_to_unitary_false by (auto with wf_db).    
    repeat setoid_rewrite kron_adjoint.
    Msimpl.
    reflexivity.
  - simpl.
    unfold denote_ctrls. subst; clear.
    unfold ctrls_to_list.
    rewrite skipn_repeat, rev_repeat, firstn_repeat.
    simpl. rewrite ctrl_list_to_unitary_false by (auto with wf_db).    
    repeat setoid_rewrite kron_adjoint.
    Msimpl.
    reflexivity.
  - simpl.
    unfold denote_ctrls. subst; clear.
    unfold ctrls_to_list.
    rewrite skipn_repeat, rev_repeat, firstn_repeat.
    simpl. rewrite 2 ctrl_list_to_unitary_false by (auto with wf_db).    
    repeat setoid_rewrite kron_adjoint.
    Msimpl.
    reflexivity.
Qed.

Lemma ctrls_to_list_transpose : forall W lb li (u : Unitary W) n lb' u', 
  ctrls_to_list lb li u = (n, lb', u') ->
  ctrls_to_list lb li (trans u) = (n, lb', u'†).
Proof.                            
  induction W; intros lb li u n lb' u' H; try solve [inversion u].
  - destruct li as [| k li].
    rewrite ctrls_to_list_empty in *.
    inversion H; subst. rewrite zero_adjoint_eq. easy.
    dependent destruction u.
    + simpl in *.
      inversion H; subst.
      Msimpl. easy.
    + simpl in *.
      inversion H; subst.
      Msimpl. easy.
    + simpl in *.
      inversion H; subst.
      Msimpl. easy.
    + simpl in *.
      inversion H; subst.
      Msimpl. easy.
    + simpl in *.
      inversion H; subst.
      Msimpl. easy.
  - clear IHW1.
    destruct li as [| k li].
    rewrite ctrls_to_list_empty in *.
    inversion H; subst. rewrite zero_adjoint_eq. easy.
    dependent destruction u.
    + simpl in *.
      destruct (ctrls_to_list lb li u) as [[j l] v] eqn:E.
      apply IHW2 in E. rewrite E.
      inversion H; subst.
      easy.
    + simpl in *.
      destruct (ctrls_to_list lb li u) as [[j l] v] eqn:E.
      apply IHW2 in E. rewrite E.
      inversion H; subst.
      easy.
Qed.

Lemma ctrl_list_to_unitary_transpose : forall l r u, 
  ctrl_list_to_unitary l r (u†) = (ctrl_list_to_unitary l r u)†.
Proof.                            
  intros l r u.
  induction l.
  simpl.
  - induction r; trivial.
    simpl.
    destruct a.
    + rewrite IHr.
      match goal with
      | [|- _ = (?A .+ ?B)† ] => setoid_rewrite (Mplus_adjoint _ _ A B)
      end.
      Msimpl.
      reflexivity.
    + rewrite IHr.
      setoid_rewrite kron_adjoint.
      Msimpl.
      reflexivity.
  - simpl.
    destruct a.
    + Msimpl. rewrite IHl. easy.
    + Msimpl. rewrite IHl. easy.
Qed.

Lemma denote_ctrls_transpose: forall W (n : nat) (u : Unitary W) li, 
  denote_ctrls n (trans u) li = (denote_ctrls n u li) †.
Proof.
  intros.
  unfold denote_ctrls.
  destruct (ctrls_to_list (repeat false n) li u) as [[j l] v] eqn:E.
  apply ctrls_to_list_transpose in E.
  rewrite E.
  rewrite ctrl_list_to_unitary_transpose.
  easy.
Qed.


(* Old swapping apply_U 
Definition apply_U {m n} (U : Square (2^m)) (l : list nat) 
           : Superoperator (2^n) (2^n) :=
  let S := swap_list n l in 
  let SU := S × (pad n U) × S† in  
  super SU.
*)

Lemma apply_to_first_correct : forall k n (u : Square 2), 
  WF_Unitary u ->
  (k < n)%nat ->                             
  WF_Superoperator (apply_to_first (@apply_qubit_unitary n u) [k]).                  
Proof.
  intros k n u U L ρ Mρ.
  unfold apply_to_first.
  unfold apply_qubit_unitary.
  unify_pows_two.
  replace (k + 1 + (n - k - 1))%nat with n by omega.    
  apply mixed_unitary; trivial.
  specialize @kron_unitary as KU.
  specialize (KU _ _ ('I_(2^k) ⊗ u) ('I_(2^(n-k-1)))). 
  replace (2^(k+1))%nat with (2^k * 2)%nat by unify_pows_two. 
  replace ((2^k * 2) * (2 ^ (n - k - 1)))%nat with (2^n)%nat in KU by unify_pows_two.
  apply KU.
  apply kron_unitary.
  apply id_unitary.
  apply U.
  apply id_unitary.
Qed.
  
Lemma apply_U_correct : forall W n (U : Unitary W) l,
                            length l = ⟦W⟧ ->
                            (forallb (fun x => x <? n) l = true) -> 
                            WF_Superoperator (apply_U n U l). 
Proof.
  intros W n U l L Lt ρ Mρ.
  destruct U; simpl.
  - destruct l; inversion L. destruct l; inversion L. clear L H0.
    apply apply_to_first_correct; trivial.
    apply H_unitary.
    simpl in Lt. rewrite andb_true_r in Lt. apply Nat.ltb_lt in Lt. easy.
  - destruct l; inversion L. destruct l; inversion L. clear L H0.
    apply apply_to_first_correct; trivial.
    apply σx_unitary.
    simpl in Lt. rewrite andb_true_r in Lt. apply Nat.ltb_lt in Lt. easy.
  - destruct l; inversion L. destruct l; inversion L. clear L H0.
    apply apply_to_first_correct; trivial.
    apply σy_unitary.
    simpl in Lt. rewrite andb_true_r in Lt. apply Nat.ltb_lt in Lt. easy.
  - destruct l; inversion L. destruct l; inversion L. clear L H0.
    apply apply_to_first_correct; trivial.
    apply σz_unitary.
    simpl in Lt. rewrite andb_true_r in Lt. apply Nat.ltb_lt in Lt. easy.
  - destruct l; inversion L. destruct l; inversion L. clear L H0.
    apply apply_to_first_correct; trivial.
    apply phase_unitary.
    simpl in Lt. rewrite andb_true_r in Lt. apply Nat.ltb_lt in Lt. easy.
  - simpl in *.
    apply mixed_unitary; trivial.
    apply denote_ctrls_unitary; trivial.
  - simpl in *.
    apply mixed_unitary; trivial.
    apply denote_ctrls_unitary; trivial.
Qed.


(*** Other Gates Applications ***)

(* Initializing qubits in the 0 position
Definition apply_new0 {n} : Superoperator (2^n) (2^(n+1)) :=
  super (|0⟩ ⊗ Id (2^n)).

Definition apply_new1 {n} : Superoperator (2^n) (2^(n+1)) :=
  super (|1⟩ ⊗ Id (2^n)).
*)

(* Initializing qubits in the n position *)
Definition apply_new0 {n} : Superoperator (2^n) (2^(n+1)) :=
  super (Id (2^n) ⊗ |0⟩).

Definition apply_new1 {n} : Superoperator (2^n) (2^(n+1)) :=
  super (Id (2^n) ⊗ |1⟩).


(* Moving new qubits to the end
Definition apply_new0 {n} : Superoperator (2^n) (2^(n+1)) :=
  super (Id (2^n) ⊗ |0⟩).

Definition apply_new1 {n} : Superoperator (2^n) (2^(n+1)) :=
  super (Id (2^n) ⊗ |1⟩).
*)

(* In-place measurement and discarding *)

(* Discard the qubit k (in place) in an n-qubit system *)
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

Definition apply_measQ {n} (k : nat) : Superoperator (2^n) (2^n) :=
  Splus (super (Id (2^k) ⊗ |0⟩⟨0| ⊗ Id (2^(n-k-1)))) 
        (super (Id (2^k) ⊗ |1⟩⟨1| ⊗ Id (2^(n-k-1)))).

Definition apply_gate {n w1 w2} (safe : bool) (g : Gate w1 w2) (l : list nat) 
           : Superoperator (2^n) (2^(n+⟦w2⟧-⟦w1⟧)) :=
  match g with 
  | U u          => if ⟦w1⟧ <=? n then apply_U n u l else super_Zero
  | BNOT         => if 1 <=? n then apply_U n _X l else super_Zero
  | init0 | new0 => apply_new0 
  | init1 | new1 => apply_new1 
  | meas         => apply_to_first apply_meas l       
  | measQ        => apply_to_first apply_meas l       
  | discard      => apply_to_first apply_discard l
  | assert0      => apply_to_first (if safe then apply_discard else apply_assert0) l
  | assert1      => apply_to_first (if safe then apply_discard else apply_assert1) l
  end.

(*** Correctness of Gate Application **)

Lemma apply_new0_correct : forall n, 
  WF_Superoperator (@apply_new0 n).
Proof.
  intros n ρ Mρ.
  unfold apply_new0.
  unfold super.
  Msimpl.
  rewrite <- (kron_1_r _ _ ρ).
  Msimpl.
  replace (2 ^ (n+1))%nat with (2^n * 2)%nat by unify_pows_two. 
  apply (mixed_state_kron _ _ ρ (|0⟩⟨0|)).
  easy.
  constructor.
  apply pure0.
Qed.

Lemma apply_new1_correct : forall n, 
  WF_Superoperator (@apply_new1 n).
Proof.
  intros n ρ Mρ.
  unfold apply_new1.
  unfold super.
  Msimpl.
  rewrite <- (kron_1_r _ _ ρ).
  Msimpl.
  replace (2 ^ (n+1))%nat with (2^n * 2)%nat by unify_pows_two. 
  apply (mixed_state_kron _ _ ρ (|1⟩⟨1|)).
  easy.
  constructor.
  apply pure1.
Qed.

Fact apply_meas_correct : forall n k, (k < n)%nat ->
    WF_Superoperator (@apply_meas n k). 
Proof.
  intros n k L ρ Mρ.
  unfold apply_meas.
  unfold Splus, super.
  Msimpl.
Admitted.
  
Fact apply_discard_correct : forall n k, (k < n)%nat ->
    WF_Superoperator (@apply_discard n k). 
Proof.
  intros n k L ρ Mρ.
  unfold apply_discard.
  unfold Splus, super.
  Msimpl.
Admitted.

Lemma apply_gate_correct : forall W1 W2 n (g : Gate W1 W2) l,
                           length l = ⟦W1⟧ ->
                           (length l <= n)%nat ->
                           (forallb (fun x => x <? n) l = true) -> (* leaning towards forall *)
                           WF_Superoperator (@apply_gate n W1 W2 true g l). 
Proof.
  intros W1 W2 n g l L1 L2 Lt.
  destruct g.
  - simpl in *.
    rewrite <- L1.
    bdestructΩ  (length l <=? n).
    replace (n + length l - length l)%nat with n by omega.
    apply apply_U_correct; easy.
  - Opaque apply_U.
    simpl in *.
    destruct n; [omega|].
    replace (S n + 1 - 1)%nat with (S n) by omega.
    apply apply_U_correct; easy.
    Transparent apply_U.
  - simpl. rewrite Nat.sub_0_r.
    apply apply_new0_correct.
  - simpl. rewrite Nat.sub_0_r.
    apply apply_new1_correct.
  - simpl. rewrite Nat.sub_0_r.
    apply apply_new0_correct.
  - simpl. rewrite Nat.sub_0_r.
    apply apply_new1_correct.
  - simpl in *. 
    destruct l; simpl.
    inversion L1.
    rewrite Nat.add_sub.
    apply apply_meas_correct.
    simpl in Lt.
    bdestruct (n0 <? n); trivial.
    inversion Lt.
  - simpl in *. 
    destruct l; simpl.
    inversion L1.
    rewrite Nat.add_sub.
    apply apply_meas_correct.
    simpl in Lt.
    bdestruct (n0 <? n); trivial.
    inversion Lt.
  - simpl in *. 
    destruct l; simpl.
    inversion L1.
    rewrite Nat.add_0_r.
    apply apply_discard_correct.
    simpl in Lt.
    bdestruct (n0 <? n); trivial.
    inversion Lt.
  - simpl in *. 
    destruct l; simpl.
    inversion L1.
    rewrite Nat.add_0_r.
    apply apply_discard_correct.
    simpl in Lt.
    bdestruct (n0 <? n); trivial.
    inversion Lt.
  - simpl in *. 
    destruct l; simpl.
    inversion L1.
    rewrite Nat.add_0_r.
    apply apply_discard_correct.
    simpl in Lt.
    bdestruct (n0 <? n); trivial.
    inversion Lt.
Qed.
    
(* These probably don't belong here, if they belong anywhere *)
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

(* No longer needed swap lemmas
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

Lemma apply_U_spec_1 : forall n i j (A1 : Square (2^i)%nat) (A2 : Square (2^j)%nat)
  (U : Square (2^1)%nat) (ρ : Square (2^1)%nat), (i + j + 1 = n)%nat ->
  @apply_U 1%nat n U [i] (A1 ⊗ ρ ⊗ A2) = A1 ⊗ (super U ρ) ⊗ A2.
Proof.
  intros.
  unfold apply_U.
  apply swap_list_spec_1.
  assumption.
Qed.

Lemma apply_U_spec_2 : forall n i j k 
  (A1 : Square (2^i)%nat) (A2 : Square (2^j)%nat) (A3 : Square (2^k)%nat)   
  (U : Square (2^2)%nat) (ρ1 ρ2 ρ1' ρ2': Square (2^1)%nat), (i + j + k + 2 = n)%nat ->
  (super U (ρ1 ⊗ ρ2)) = ρ1' ⊗ ρ2' -> 
  @apply_U 2%nat n U [i; (i+j+1)%nat] (A1 ⊗ ρ1 ⊗ A2 ⊗ ρ2 ⊗ A3) = A1 ⊗ ρ1' ⊗ A2 ⊗ ρ2' ⊗ A3.
Proof.
  intros.
  unfold apply_U.
  apply swap_list_spec_2.
  assumption.
  assumption.
Qed.
*)

(** Denoting Min Circuits **)

Definition get_var (p : Pat Bit) := match p with
                                    | bit x => x
                                    end.

Definition denote_pat {w} (p : Pat w) : Matrix (2^⟦w⟧) (2^⟦w⟧) :=
  swap_list (⟦w⟧) (pat_to_list p).
Instance Denote_Pat {w} : Denote (Pat w) (Matrix (2^⟦w⟧) (2^⟦w⟧)) :=
  { denote := denote_pat }.

(* I'm not convinced that "padding" needs to exist here. It would be wonderful
   if we could remove it *)
Fixpoint denote_db_circuit {w} safe padding input (c : DeBruijn_Circuit w)
                         : Superoperator (2^(padding+input)) (2^(padding+⟦w⟧)) :=
  match c with
  | db_output p             => super (pad (padding+input) (⟦p⟧))
  | @db_gate _ w1 w2 g p c' => let input' := (input + ⟦w2⟧ - ⟦w1⟧)%nat in
                              compose_super (denote_db_circuit safe padding input' c')
                                            (apply_gate safe g (pat_to_list p))
  | db_lift p c'            => let k := get_var p in Splus  
                              (compose_super 
                                 (denote_db_circuit safe padding (input-1) (c' false))
                                 (super ('I_(2^k) ⊗ ⟨0| ⊗ 'I_(2^(input+padding-k-1)))))
                              (compose_super 
                                 (denote_db_circuit safe padding (input-1) (c' true))
                                 (super ('I_(2^k) ⊗ ⟨1| ⊗ 'I_(2^(input+padding-k-1)))))
  end.

(* Just removed. Lift case needs to mention padding
Fixpoint denote_db_circuit {w} safe padding input (c : DeBruijn_Circuit w)
                         : Superoperator (2^(padding+input)) (2^(padding+⟦w⟧)) :=
  match c with
  | db_output p             => super (pad (padding+input) (⟦p⟧))
  | @db_gate _ w1 w2 g p c' => let input' := (input + ⟦w2⟧ - ⟦w1⟧)%nat in
                              compose_super (denote_db_circuit safe padding input' c')
                                            (apply_gate safe g (pat_to_list p))
  | db_lift p c'            => let k := get_var p in Splus  
                              (compose_super 
                                 (denote_db_circuit safe padding (input-1) (c' false))
                                 (super ('I_(2^k) ⊗ ⟨0| ⊗ 'I_(2^(input-k-1)))))
                              (compose_super 
                                 (denote_db_circuit safe padding (input-1) (c' true))
                                 (super ('I_(2^k) ⊗ ⟨1| ⊗ 'I_(2^(input-k-1)))))
  end.
*)


(*
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

*)
                    
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


Definition denote_box (safe : bool) {W1 W2 : WType} (c : Box W1 W2) : 
  Superoperator (2 ^ (⟦ W1 ⟧)) (2 ^ (⟦ W2 ⟧)) := 
    denote_db_box safe (hoas_to_db_box c).
Instance Denote_Box {W1 W2} : Denote (Box W1 W2) (Superoperator (2^⟦W1⟧) (2^⟦W2⟧)) :=
         {| denote := denote_box true |}.

Definition denote_circuit (safe : bool) {W : WType} (c : Circuit W) (Γ0 Γ : Ctx) : 
  Superoperator (2 ^ (⟦ Γ0 ⟧ + ⟦ Γ ⟧)) (2 ^ (⟦ Γ0 ⟧ + ⟦ W ⟧)) := 
  denote_db_circuit safe (⟦Γ0⟧) (⟦Γ⟧) (hoas_to_db Γ c).

(* safe variant *)
Notation "⟨ Γ0 | Γ ⊩ c ⟩" := (denote_circuit true c Γ0 Γ) (at level 20).

(* unsafe variant *)
Notation "⟨! Γ0 | Γ ⊩ c !⟩" := (denote_circuit false c Γ0 Γ) (at level 20).

(*
Proposition denote_db_subst : forall pad n σ w (c : DeBruijn_Circuit w),
      denote_db_circuit pad n (subst_db σ c)
    = compose_super (denote_db_circuit pad n c)
                    (super (swap_list (length (get_σ σ)) (get_σ σ))).
*)

Lemma denote_output : forall Γ0 Γ {w} (p : Pat w),
    ⟨ Γ0 | Γ ⊩ output p ⟩ 
  = super (pad (⟦Γ0⟧ + ⟦Γ⟧) (denote_pat (subst_pat Γ p))).
Proof.
  intros.
  simpl.
  unfold subst_pat.
  reflexivity.
Qed.

Ltac fold_denotation :=
  repeat match goal with
  | [ |- context[ size_octx ?Γ ] ] => replace (size_octx Γ) with (⟦Γ⟧); auto
  end.

(* n is the number of inputs to c'. the number of inputs to c might be less than
that. *)
(* TODO: might need to add a hypothesis relating n1 and n2 to the actual inputs
of c1 and c2 *)
(*
Proposition denote_db_compose : forall pad w1 w2 Γ1 Γ n m
                          (c1 : DeBruijn_Circuit w1) (c2 : DeBruijn_Circuit w2),
    Types_DB Γ1 c1 ->
    Types_DB (Valid (WType_to_Ctx w1 ++ Γ)) c2 ->
    
    n = (⟦Γ1⟧+ ⟦Γ⟧)%nat ->
    m = (⟦Γ⟧) ->
    
    denote_db_circuit pad n (db_compose m c1 c2)
  = compose_super (denote_db_circuit pad (⟦w1⟧+ ⟦Γ⟧) c2)
                  (denote_db_circuit (pad +⟦Γ⟧) (⟦Γ1⟧) c1).
*)

Lemma length_fresh_state : forall w Γ Γ',
  Γ' = add_fresh_state w Γ ->
  length Γ' = (length Γ + size_wtype w)%nat.
Proof.
  induction w; intros Γ Γ' H.
  - unfold add_fresh_state, add_fresh in H.
    simpl in H. rewrite H.
    rewrite app_length. 
    easy.
  - unfold add_fresh_state, add_fresh in H.
    simpl in H. rewrite H.
    rewrite app_length. 
    easy.
  - unfold add_fresh_state, add_fresh in H.
    simpl in H. rewrite H.
    easy.
  - rewrite H. clear H.
    unfold add_fresh_state in *. simpl. 
    destruct (add_fresh w1 Γ) as [p1 Γ1] eqn:E1.    
    destruct (add_fresh w2 Γ1) as [p2 Γ2] eqn:E2.
    simpl.
    specialize (IHw1 Γ _ eq_refl). 
    rewrite E1 in IHw1. simpl in IHw1.
    specialize (IHw2 Γ1 _ eq_refl). 
    rewrite E2 in IHw2. simpl in IHw2.
    rewrite IHw2, IHw1.
    omega.
Qed.

Lemma swap_fresh_seq : forall w (Γ : Ctx),
    pat_to_list (add_fresh_pat w Γ) = seq (length Γ) (size_wtype w).
Proof.
  induction w; intros; simpl; auto.
  unfold add_fresh_pat. simpl.
  destruct (add_fresh w1 Γ) as [p1 Γ1] eqn:E1.
  destruct (add_fresh w2 Γ1) as [p2 Γ2] eqn:E2.
  simpl.
  rewrite (surjective_pairing (add_fresh w1 Γ)) in E1. inversion E1.
  rewrite (surjective_pairing (add_fresh w2 Γ1)) in E2. inversion E2.
  unfold add_fresh_pat in *.
  rewrite IHw1, IHw2.
  symmetry in  H1. apply length_fresh_state in H1. rewrite H1.  
  rewrite <- seq_app.
  easy.
Qed.

Lemma denote_pat_fresh_id : forall w,
      denote_pat (add_fresh_pat w []) = Id (2^⟦w⟧).
Proof.
  intros.
  unfold denote_pat.
  simpl.
  rewrite swap_fresh_seq by validate.
  rewrite swap_list_n_id.
  reflexivity.
Qed.

Lemma maps_to_app : forall Γ w, maps_to (length Γ) (Γ ++ [Some w]) = Some (size_ctx Γ).
Proof.
  intros Γ w.
  induction Γ; simpl; eauto.
  destruct a; simpl.
  rewrite IHΓ. easy.
  rewrite IHΓ. easy.
Qed.

Inductive no_gaps : Ctx -> Prop :=
| no_gaps_empty : no_gaps []
| no_gaps_cons : forall W Γ, no_gaps Γ -> no_gaps (Some W :: Γ).

Lemma no_gaps_app : forall Γ Γ',
  no_gaps Γ ->
  no_gaps Γ' ->
  no_gaps (Γ ++ Γ').
Proof.
  intros Γ Γ' NG NG'.
  induction Γ; trivial.
  simpl.
  inversion NG; subst.
  constructor.
  auto. 
Qed.

Lemma add_fresh_state_no_gaps : forall W Γ,
  no_gaps Γ ->
  no_gaps (add_fresh_state W Γ). 
Proof.
  induction W; intros Γ NG.
  - unfold add_fresh_state; simpl.
    apply no_gaps_app; trivial.
    repeat constructor.
  - unfold add_fresh_state; simpl.
    apply no_gaps_app; trivial.
    repeat constructor.
  - unfold add_fresh_state; simpl.
    easy.
  - unfold add_fresh_state; simpl.
    repeat rewrite add_fresh_split. simpl.
    auto.
Qed.

Lemma subst_var_no_gaps : forall Γ w, 
  no_gaps Γ ->
  subst_var (Γ ++ [Some w]) (length Γ) = length Γ.
Proof.
  intros Γ w NG.
  induction Γ; trivial.
  inversion NG; subst.
  unfold subst_var in *. simpl.
  rewrite maps_to_app in *. simpl in *.
  rewrite IHΓ; easy.
Qed. 

Lemma subst_units : forall w (p : Pat w) Γ, ∅ ⊢ p:Pat -> subst_pat Γ p = p.
Proof.  
  intros w p Γ H.
  gen Γ.
  dependent induction H.
  - intros. reflexivity.
  - inversion s.
  - inversion s.
  - intros Γ.    
    symmetry in e.
    apply merge_nil_inversion in e as [E1 E2].
    simpl.
    rewrite IHTypes_Pat1, IHTypes_Pat2; easy.
Qed.

Proposition subst_pat_no_gaps : forall w (Γ : Ctx) (p : Pat w), 
  Γ ⊢ p:Pat ->
  no_gaps Γ ->
  subst_pat Γ p = p.
Proof.
  intros w Γ p TP.
  dependent induction TP; trivial.
  - intros NG.
    inversion s; subst.
    reflexivity.
    inversion NG.
  - intros NG.
    inversion s; subst.
    reflexivity.
    inversion NG.
  - intros NG.
    destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.
    destruct Γ1 as [|o1 Γ1], Γ2 as [|o2 Γ2].
    + simpl. rewrite IHTP1, IHTP2; easy.
    + rewrite merge_nil_l in e.
      inversion e; subst.
      simpl. rewrite IHTP2; trivial. 
      f_equal.
      apply subst_units; easy.
    + rewrite merge_nil_r in e.
      inversion e; subst.
      simpl. rewrite IHTP1; trivial. 
      f_equal.
      apply subst_units; easy.
    + destruct o1, o2.
      unlock_merge. inversion e.
      (* inductive hypotheses fail us *)
Abort.

Fact subst_pat_fresh : forall w Γ w',
      Γ = add_fresh_state w' [] ->
      subst_pat (add_fresh_state w Γ) (add_fresh_pat w Γ) 
    = add_fresh_pat w Γ.
Proof.
  induction w; intros; auto.
  - unfold add_fresh_state. simpl.
    rewrite subst_var_no_gaps.
    reflexivity.
    rewrite H.
    apply add_fresh_state_no_gaps.
    constructor.
  - unfold add_fresh_state. simpl.
    rewrite subst_var_no_gaps.
    reflexivity.
    rewrite H.
    apply add_fresh_state_no_gaps.
    constructor.
  - unfold add_fresh_state. simpl.
    destruct (add_fresh w1 Γ) as [p1 Γ1] eqn:E1.
    destruct (add_fresh w2 Γ1) as [p2 Γ2] eqn:E2.
    simpl.
Admitted.

Lemma subst_pat_fresh_empty : forall w,
      subst_pat (add_fresh_state w []) (add_fresh_pat w [])
    = add_fresh_pat w [].
Proof.
  intros.
  apply subst_pat_fresh with (w' := One).
  auto.
Qed.

Lemma size_fresh_ctx : forall (w : WType) (Γ : Ctx),
      size_ctx (add_fresh_state w Γ) = (size_ctx Γ + size_wtype w)%nat.
Proof.
  unfold add_fresh_state; simpl.
  induction w; intros Γ. 
  - simpl. rewrite size_ctx_app; easy. 
  - simpl. rewrite size_ctx_app; easy. 
  - simpl; omega.
  - simpl.
    destruct (add_fresh w1 Γ) as [p1 Γ1] eqn:E1.
    destruct (add_fresh w2 Γ1) as [p2 Γ2] eqn:E2.
    simpl in *.
    rewrite (surjective_pairing (add_fresh _ _)) in E2. inversion E2.
    rewrite IHw2.
    rewrite (surjective_pairing (add_fresh _ _)) in E1. inversion E1.
    rewrite IHw1.
    omega.
Qed.

(* probably a more general form of this *)
Lemma denote_db_unbox : forall {w1 w2} (b : Box w1 w2),
    ⟦b⟧ = ⟨ [] | add_fresh_state w1 [] ⊩ unbox b (add_fresh_pat w1 []) ⟩.
Proof.
  destruct b.
  simpl. unfold denote_box.
  unfold denote_circuit.
  simpl. 
  rewrite size_fresh_ctx. 
  simpl.
  unfold add_fresh_state, add_fresh_pat.
  destruct (add_fresh w1 []) as [p1 Γ1] eqn:E1.
  simpl.
  easy.
Qed.
  
Lemma denote_index_update_some : forall (Γ : Ctx) x w w',
      index (Valid Γ) x = Some w ->
      ⟦update_at Γ x (Some w')⟧ = ⟦Γ⟧.
Proof.
  induction Γ as [ | o Γ]; intros; auto.
  destruct x; auto.
  * simpl in *. subst. auto.
  * simpl in *. rewrite (IHΓ _ w); auto.
Qed.

Lemma denote_index_update_none : forall (Γ : Ctx) x w,
      index (Valid Γ) x = Some w ->
      ⟦update_at Γ x None⟧ = (⟦Γ⟧ - 1)%nat.
Proof.
  induction Γ as [ | o Γ]; intros; auto.
  destruct x; auto.
  * simpl in *. subst. simpl. omega. 
  * simpl in *.
    rewrite (IHΓ _ w); trivial.
    destruct o; trivial.
    assert (size_ctx Γ > 0)%nat.
      clear -H.
      gen x.
      induction Γ. 
      destruct x; simpl; intros H; inversion H.
      intros x H.
      destruct a; simpl.
      omega.
      destruct x. simpl in H; inversion H.
      apply (IHΓ x).
      simpl in H.
      apply H.
    omega.
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

Lemma remove_at_singleton : forall x w Γ,
      SingletonCtx x w Γ ->
      empty_ctx (remove_at x Γ).
Proof.
  induction 1; simpl.
  * constructor.
  * constructor. auto.
Qed.

Lemma update_none_singleton : forall x w Γ,
      SingletonCtx x w Γ ->
      empty_ctx (update_at Γ x None).
Proof.
  induction 1; simpl.
  * repeat constructor.
  * constructor. assumption.
Qed.

Lemma remove_pat_singleton : forall x W (p : Pat W), 
      singleton x W ⊢ p:Pat ->
      remove_pat p (singleton x W) = [].
Proof.
  intros x W p H.
  dependent induction H.
  - rewrite <- x. reflexivity.
  - unfold remove_pat. simpl.
    unfold remove_var. simpl.
    rewrite trim_empty; trivial.
    eapply update_none_singleton. apply s.
  - unfold remove_pat. simpl.
    unfold remove_var. simpl.
    rewrite trim_empty; trivial.
    eapply update_none_singleton. apply s.
  - unfold remove_pat. simpl.
(* true, but I shouldn't care about compound singletons *)
Abort.    
   
Proposition process_gate_ctx_size : forall w1 w2 (g : Gate w1 w2) p (Γ : Ctx),
      (⟦w1⟧ <= ⟦Γ⟧)%nat ->
      ⟦process_gate_state g p Γ⟧ = (⟦Γ⟧ + ⟦w2⟧ - ⟦w1⟧)%nat.
Proof.
  destruct g; intros p Γ H;
    try (simpl; rewrite Nat.add_sub; auto; fail);
    try (simpl; rewrite ctx_size_app; simpl; omega).
  - simpl. rewrite Nat.sub_0_r. destruct Γ. simpl in *. omega. simpl.
    destruct o; rewrite size_ctx_app; simpl; omega.
  - simpl. rewrite Nat.sub_0_r. destruct Γ. simpl in *. omega. simpl.
    destruct o; rewrite size_ctx_app; simpl; omega.
  - simpl. rewrite Nat.sub_0_r. destruct Γ. simpl in *. omega. simpl.
    destruct o; rewrite size_ctx_app; simpl; omega.
  - simpl. rewrite Nat.sub_0_r. destruct Γ. simpl in *. omega. simpl.
    destruct o; rewrite size_ctx_app; simpl; omega.
  - dependent destruction p. 
    simpl. destruct Γ. simpl. easy.
    simpl. destruct o. simpl. unfold process_gate_state. simpl.
    admit. admit.
  - (* Need that we're discarding a valid wire *)
Abort.
    
Proposition process_gate_state_merge : forall w1 w2 (g : Gate w1 w2) p Γ1 Γ2 Γ,
      Types_Pat Γ1 p ->
      Valid Γ = Γ1 ⋓ Γ2 ->
      Valid (process_gate_state g p Γ) = process_gate_state g p Γ ⋓ Γ2.
Proof.
(*
  induction g; intros p Γ1 Γ2 types_p; auto.
  * dependent destruction p.
    dependent destruction types_p.
    rewrite merge_nil_l.
    unfold process_gate_state at 2.
    unfold process_gate_state. simpl.
    destruct Γ2; simpl. auto.
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
*)
Abort.

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
    inversion m; subst.
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
    apply merge_ind_fun in H.
    destruct H.
    apply pf_merge.
    unlock_merge.
    simpl.
    edestruct IHmerge_ind with (n := n); try reflexivity.
    unlock_merge.
    simpl in pf_merge.
    rewrite <- pf_merge.
    apply merge_o_ind_fun in m.
    rewrite m.
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
      apply merge_ind_fun in H.
      destruct H. unlock_merge. simpl. rewrite <- pf_merge. reflexivity.
    + simpl.
      edestruct IHmerge_ind with (n := n); try reflexivity.
      unlock_merge.
      simpl in *.
      rewrite <- pf_merge.
      apply merge_o_ind_fun in m.
      rewrite m.
      reflexivity.
Qed.

Lemma remove_at_collision : forall n W (Γ Γ1 Γ2 : Ctx),  SingletonCtx n W Γ1 -> 
  Γ == Γ1 ∙ Γ2 -> size_ctx (remove_at n Γ2) = size_ctx Γ2.
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
  Γ == Γ1 ∙ Γ2 -> size_ctx (update_at Γ2 n None) = size_ctx Γ2.
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

(* No longer makes sense without process_gate_state taking nats:
Proposition process_gate_denote : forall {w1 w2} (g : Gate w1 w2) (p : Pat w1) (Γ Γ1 Γ2 : Ctx),
    Valid Γ == Γ1 ∙ Γ2 ->
    Γ1 ⊢ p :Pat -> 
    process_gate_state g p (⟦Γ⟧) = ⟦process_gate_state g p Γ⟧.
Proof.
  intros w1 w2 g p Γ Γ1 Γ2 U TP.
  unfold process_gate_state, add_fresh_state, size_octx.
  destruct g; simpl; trivial.
  + unfold size_octx.
    destruct U.  
    destruct pf_valid. subst. 
    simpl.
    rewrite size_ctx_app. 
    simpl; omega.
  + unfold size_octx.
    destruct U.  
    destruct pf_valid. subst. 
    simpl.
    rewrite size_ctx_app. 
    simpl; omega.
  + unfold size_octx.
    destruct U.  
    destruct pf_valid. subst. 
    simpl.
    rewrite size_ctx_app. 
    simpl; omega.
  + unfold size_octx.
    destruct U.  
    destruct pf_valid. subst. 
    simpl.
    rewrite size_ctx_app. 
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

    destruct U. rewrite pf_merge in *.
    rewrite size_octx_merge with (Γ1 := Γ1) (Γ2 := Γ2) by easy.
    destruct RM.
    (* Need lemma about size_ctx trim x *)
    rewrite size_octx_trim.    
    rewrite pf_merge0 in *.
    rewrite size_octx_merge with (Γ1 := Valid (update_at Γ1 v None)) 
                                 (Γ2 := Valid (update_at Γ2 v None)) by easy.    
    simpl.
    specialize (update_none_singleton _ _ _ H1) as E. simpl in E.
    apply size_empty_ctx in E. simpl in E. rewrite E.
    specialize (Singleton_size _ _ _ H1) as SS. simpl in SS. rewrite SS.
    erewrite update_none_collision.
    omega.
    apply H1.    
    rewrite <- pf_merge in pf_valid.
    constructor; [apply pf_valid| apply pf_merge].
  + dependent destruction p; simpl.
    inversion TP; subst. rename Γ0 into Γ1.
    unfold remove_pat.
    simpl.
    destruct Γ as [|Γ]. destruct U. apply not_valid in pf_valid. contradiction.
    destruct Γ2 as [|Γ2]. destruct U. simpl in pf_merge. rewrite pf_merge in *. 
      apply not_valid in pf_valid. contradiction.
    specialize (update_none_merge _ _ _ v U) as RM.

    destruct U. rewrite pf_merge in *.
    rewrite size_octx_merge with (Γ1 := Γ1) (Γ2 := Γ2) by easy.
    destruct RM. 
    rewrite size_octx_trim.
    rewrite pf_merge0 in *.      
    rewrite size_octx_merge with (Γ1 := Valid (update_at Γ1 v None)) 
                                 (Γ2 := Valid (update_at Γ2 v None)) by easy.    
    simpl.
    specialize (update_none_singleton _ _ _ H1) as E. simpl in E.
    apply size_empty_ctx in E. simpl in E. rewrite E.
    specialize (Singleton_size _ _ _ H1) as SS. simpl in SS. rewrite SS.
    erewrite update_none_collision.
    omega.
    apply H1.    
    rewrite <- pf_merge in pf_valid.
    constructor; [apply pf_valid| apply pf_merge].
  + dependent destruction p; simpl.
    inversion TP; subst. rename Γ0 into Γ1.
    unfold remove_pat.
    simpl.
    destruct Γ as [|Γ]. destruct U. apply not_valid in pf_valid. contradiction.
    destruct Γ2 as [|Γ2]. destruct U. simpl in pf_merge. rewrite pf_merge in *. 
      apply not_valid in pf_valid. contradiction.
    specialize (update_none_merge _ _ _ v U) as RM.

    destruct U. rewrite pf_merge in *.
    rewrite size_octx_merge with (Γ1 := Γ1) (Γ2 := Γ2) by easy.
    replace (Valid (flatten_ctx (update_at Γ v None)))
       with (flatten_octx (Valid (update_at Γ v None))) by easy.
    destruct RM.
    rewrite size_octx_trim.
    rewrite pf_merge0 in *.  
    rewrite size_octx_merge with (Γ1 := Valid (update_at Γ1 v None)) 
                                 (Γ2 := Valid (update_at Γ2 v None)) by easy.    
    simpl.
    specialize (update_none_singleton _ _ _ H1) as E. simpl in E.
    apply size_empty_ctx in E. simpl in E. rewrite E.
    specialize (Singleton_size _ _ _ H1) as SS. simpl in SS. rewrite SS.
    erewrite update_none_collision.
    omega.
    apply H1.    
    rewrite <- pf_merge in pf_valid.
    constructor; [apply pf_valid| apply pf_merge].
Abort.
*)

(*
Proposition denote_gate_circuit : forall Γ0 (Γ : OCtx) Γ1 Γ1' {w1 w2 w'} 
                           (g : Gate w1 w2) p1 (f : Pat w2 -> Circuit w'),
      Γ1 ⊢ p1 :Pat ->
      Γ ⊢ f :Fun ->
      Γ1' == Γ1 ∙ Γ ->

    ⟨ Γ0 | Γ ⊩ gate g p1 f⟩ 
    = compose_super (⟨ Γ0 | process_gate_state g p1 Γ
                          ⊩f (process_gate_pat g p1 Γ) ⟩)
                    (apply_gate g (pat_to_list (subst_pat Γ p1))).
Proof.
  intros.
  simpl. fold_denotation.
  set (p1' := subst_pat Γ p1).
  set (p2 := process_gate_pat g p1 Γ).
  rewrite (process_gate_nat _ p1' p1).
  rewrite process_gate_denote. 
  reflexivity.
Abort.
*)

Fact process_gate_ctx_size : forall w1 w2 (Γ Γ1 Γ2 : Ctx) (g : Gate w1 w2) (p1 : Pat w1),
  Γ == Γ1 ∙ Γ2 -> (* these are only needed for measure and maybe discard *)
  Γ1 ⊢ p1 :Pat ->
  (size_ctx (process_gate_state g p1 Γ)) = (size_ctx Γ + ⟦w2⟧ - ⟦w1⟧)%nat.
Proof.
  intros w1 w2 Γ Γ1 Γ2 g p1 M TP.
  unfold process_gate_state.
  destruct g; simpl.
  - rewrite Nat.add_sub. easy.
  - rewrite Nat.add_sub. easy.
  - rewrite Nat.sub_0_r. rewrite size_ctx_app. easy.
  - rewrite Nat.sub_0_r. rewrite size_ctx_app. easy.
  - rewrite Nat.sub_0_r. rewrite size_ctx_app. easy.
  - rewrite Nat.sub_0_r. rewrite size_ctx_app. easy.
  - dependent destruction p1. 
    simpl.
    rewrite Nat.add_sub.
    unfold change_type.
    rewrite denote_index_update_some with (w:=Qubit).
    easy.
    eapply index_merge_l.
    apply M.
    apply singleton_index.
    dependent destruction TP.
    easy.
  - rewrite Nat.add_sub. easy.
  - dependent destruction p1.
    unfold remove_pat. simpl.
    unfold remove_var.
    rewrite size_ctx_trim.
    rewrite Nat.add_0_r.
    rewrite denote_index_update_none with (w:=Bit).
    easy.
    eapply index_merge_l.
    apply M.
    apply singleton_index.
    dependent destruction TP.
    easy.
  - dependent destruction p1.
    unfold remove_pat. simpl.
    unfold remove_var.
    rewrite size_ctx_trim.
    rewrite Nat.add_0_r.
    rewrite denote_index_update_none with (w:=Qubit).
    easy.
    eapply index_merge_l.
    apply M.
    apply singleton_index.
    dependent destruction TP.
    easy.
  - dependent destruction p1.
    unfold remove_pat. simpl.
    unfold remove_var.
    rewrite size_ctx_trim.
    rewrite Nat.add_0_r.
    rewrite denote_index_update_none with (w:=Qubit).
    easy.
    eapply index_merge_l.
    apply M.
    apply singleton_index.
    dependent destruction TP.
    easy.
Qed.

Lemma denote_gate_circuit : forall {w1 w2 w'} (safe:bool)
      (g : Gate w1 w2) p1 (f : Pat w2 -> Circuit w') (Γ0 Γ Γ1 Γ2 : Ctx) (* Γ Γ0,*),     
       Γ == Γ1 ∙ Γ2 -> Γ1 ⊢ p1 :Pat  ->   
(*   ⟨! Γ0 | Γ ⊩ gate g p1 f !⟩ 
    = compose_super 
        (⟨ Γ0 | process_gate_state g p1 Γ ⊩ f (process_gate_pat g p1 Γ) ⟩)
        (apply_gate false g (pat_to_list (subst_pat Γ p1))). *)
      denote_circuit safe (gate g p1 f) Γ0 Γ
    = compose_super 
        (denote_circuit safe (f (process_gate_pat g p1 Γ)) Γ0 (process_gate_state g p1 Γ))
                    (apply_gate safe g (pat_to_list (subst_pat Γ p1))).
Proof.
  intros.
  unfold denote_circuit.
  simpl; fold_denotation.
  replace (process_gate g p1 Γ) with 
      (process_gate_pat g p1 Γ, process_gate_state g p1 Γ) by 
      (symmetry; apply surjective_pairing).
  simpl; fold_denotation.
  rewrite process_gate_ctx_size with (Γ1:=Γ1) (Γ2:=Γ2); easy.
Qed.  

(* True for any bijection f in place of S, actually *)
Lemma lookup_maybe_S : forall x l,  lookup_maybe (S x) (map S l) = lookup_maybe x l.
Proof. 
  intros x l.
  induction l; auto.
  simpl.
  destruct (x =? a). easy.
  rewrite IHl. easy.
Qed.  

(*
Proposition lookup_maybe_ctx_dom : forall v Γ Γv Γo W,
          Γ == Γv ∙ Γo ->
          SingletonOCtx v W Γv ->
          lookup_maybe v (octx_dom Γ) <> None. 
Proof.
  induction v; intros Γ Γv Γo W H H0.    
  - inversion H0; subst. clear H0.
    apply singleton_equiv in H1; subst. 
    destruct H.
    rewrite pf_merge.
    destruct Γo as [|Γo]. invalid_contradiction.
    destruct Γo.
    simpl. easy.
    destruct o. unlock_merge. simpl in pf_merge. invalid_contradiction.
    simpl. easy.
  - apply merge_fun_ind in H.
    inversion H; subst.
    + inversion H0. inversion H2.
    + inversion H0; subst.
      apply singleton_equiv in H2. subst.
      simpl.
      rewrite lookup_maybe_S.
      eapply (IHv (singleton v W)).
      split. validate. rewrite merge_nil_r. easy.
      constructor. apply singleton_singleton.
    + inversion H0; subst.
      inversion H1; subst.
      * inversion H4; subst.
        simpl.
        rewrite lookup_maybe_S.
        eapply (IHv Γ0).
        apply merge_ind_fun. apply H2.
        constructor; apply H7.
      * inversion H4.
      * inversion H4; subst.
        simpl.
        rewrite lookup_maybe_S.
        intros F.
        eapply (IHv Γ0).
        apply merge_ind_fun. apply H2.
        constructor; apply H7.
        simpl.
        destruct (lookup_maybe v (ctx_dom Γ0)).
        inversion F.
        easy.
Abort.
*)

Lemma subst_qubit_bounded : forall v (Γ Γv Γo : Ctx),
                            Γv ⊢ (qubit v) :Pat ->
                            Γ == Γv ∙ Γo ->
                            (subst_var Γ v < size_octx Γ)%nat.
Proof.
  induction v; intros Γ Γv Γo TP M.
  - inversion TP; subst.
    apply singleton_equiv in H1.
    rewrite H1 in M.
    apply merge_fun_ind in M.
    inversion M; subst.
    simpl.
    unfold subst_var. simpl.
    omega.
    unfold subst_var. simpl.
    destruct o; simpl.
    omega.
    inversion H4.
  - inversion TP; subst.
    apply singleton_equiv in H1.
    rewrite H1 in M.
    apply merge_fun_ind in M.
    inversion M; subst.
    + unfold subst_var.
      simpl.
      rewrite maps_to_singleton.
      rewrite singleton_size.
      omega.
    + assert (TP': singleton v Qubit ⊢ qubit v :Pat).
        constructor. apply singleton_singleton.
      apply merge_ind_fun in H5.
      specialize (IHv _ _ _ TP' H5).
      destruct o; simpl in *.      
      * unfold subst_var in *.
        simpl.
        destruct (maps_to v Γ0); simpl; auto.
        omega.
      * unfold subst_var in *.
        simpl.
        destruct (maps_to v Γ0); simpl; auto.
Qed.

Lemma subst_bit_bounded : forall v (Γ Γv Γo : Ctx),
                            Γv ⊢ (bit v) :Pat ->
                            Γ == Γv ∙ Γo ->
                            (subst_var Γ v < size_octx Γ)%nat.
Proof.
  induction v; intros Γ Γv Γo TP M.
  - inversion TP; subst.
    apply singleton_equiv in H1.
    rewrite H1 in M.
    apply merge_fun_ind in M.
    inversion M; subst.
    simpl.
    unfold subst_var. simpl.
    omega.
    unfold subst_var. simpl.
    destruct o; simpl.
    omega.
    inversion H4.
  - inversion TP; subst.
    apply singleton_equiv in H1.
    rewrite H1 in M.
    apply merge_fun_ind in M.
    inversion M; subst.
    + unfold subst_var.
      simpl.
      rewrite maps_to_singleton.
      rewrite singleton_size.
      omega.
    + assert (TP': singleton v Bit ⊢ bit v :Pat).
        constructor. apply singleton_singleton.
      apply merge_ind_fun in H5.
      specialize (IHv _ _ _ TP' H5).
      destruct o; simpl in *.      
      * unfold subst_var in *.
        simpl.
        destruct (maps_to v Γ0); simpl; auto.
        omega.
      * unfold subst_var in *.
        simpl.
        destruct (maps_to v Γ0); simpl; auto.
Qed.

Lemma pat_to_list_bounded : forall W (Γ Γp Γo : Ctx) (p : Pat W) x, 
                            Γ == Γp ∙ Γo ->
                            Γp ⊢ p:Pat ->
                            In x (pat_to_list (subst_pat Γ p)) ->
                            (x < size_ctx Γ)%nat.
Proof.
  intros W Γ Γp Γo p.
  gen Γ Γp Γo.
  induction p; intros Γ Γp Γo x M TP IN.
  - simpl in *. easy.
  - simpl in *.     
    destruct IN; try easy. 
    rewrite <- H.
    eapply subst_qubit_bounded.
    apply TP.
    apply M.
  - simpl in *.     
    destruct IN; try easy. 
    rewrite <- H.
    eapply subst_bit_bounded.
    apply TP.
    apply M.
  - simpl in IN.    
    apply in_app_or in IN.
    destruct IN as [IN1 | IN2].
    + dependent destruction TP.
      destruct M.
      rewrite e in pf_merge.
      rewrite <- merge_assoc in pf_merge.
      destruct Γ1 as [|Γ1], (Γ2 ⋓ Γo) as [|Γ']; try invalid_contradiction.
      eapply IHp1; trivial.
      split; trivial. apply pf_merge. easy.
    + dependent destruction TP.
      destruct M.
      rewrite e in pf_merge.
      rewrite (merge_comm Γ1) in pf_merge.
      rewrite <- merge_assoc in pf_merge.
      destruct Γ2 as [|Γ2], (Γ1 ⋓ Γo) as [|Γ']; try invalid_contradiction.
      eapply IHp2; trivial.
      split; trivial. apply pf_merge. easy.
Qed.      

Lemma update_at_singleton : forall v W W' Γ Γ',
                            SingletonCtx v W Γ ->
                            SingletonCtx v W' Γ' ->
                            update_at Γ v (Some W') = Γ'.
Proof.
  intros v W W' Γ Γ' H H'.
  apply singleton_equiv in H.
  apply singleton_equiv in H'.
  subst.
  induction v; auto.
  simpl.
  rewrite IHv.
  easy.
Qed.

Lemma update_at_merge : forall v W W' Γ Γ1 Γ1' Γ2, 
                        SingletonCtx v W Γ1 ->
                        SingletonCtx v W' Γ1' ->
                        Valid Γ == Γ1 ∙ Γ2 ->
                        Valid (update_at Γ v (Some W')) == Γ1' ∙ Γ2.
Proof.
  induction v; intros W W' Γ Γ1 Γ1' Γ2 H H0 H1.
  - apply singleton_equiv in H. subst.
    apply singleton_equiv in H0. subst.
    simpl in *.
    destruct H1.
    split. validate.
    destruct Γ2 as [|Γ2]. invalid_contradiction.
    destruct Γ. Search merge ∅.
    symmetry in pf_merge.
    apply merge_nil_inversion in pf_merge as [L R].
    inversion L.
    simpl.
    destruct Γ2.
    destruct Γ.
    easy.
    rewrite merge_nil_r in pf_merge.
    inversion pf_merge.
    destruct o0.
    inversion pf_merge.
    unlock_merge.
    simpl in *.
    inversion pf_merge; subst.
    easy.
  - apply merge_fun_ind in H1.
    inversion H1; subst.
    inversion H.
    split. validate.
    rewrite merge_nil_r.
    f_equal.
    eapply update_at_singleton; trivial.
    apply H.
    inversion H; subst.
    inversion H0; subst.
    simpl.
    apply merge_ind_fun in H6.
    specialize (IHv _ _ _ _ _ _ H7 H3 H6).
    destruct IHv.
    split. validate.
    simpl.
    unlock_merge.
    simpl in *.
    rewrite <- pf_merge.
    inversion H4; subst; easy.
Qed.

Lemma types_pat_no_trail : forall Γ W (p : Pat W), (Valid Γ) ⊢ p:Pat -> trim Γ = Γ.
Proof.
  intros Γ W. gen Γ.
  induction W; intros Γ p H; dependent destruction p; dependent destruction H.
  - apply singleton_equiv in s; subst.
    induction v; trivial.
    simpl. rewrite IHv.
    destruct v; easy.
  - apply singleton_equiv in s; subst.
    induction v; trivial.
    simpl. rewrite IHv.
    destruct v; easy.
  - easy.
  - destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.
    assert(otrim (Valid Γ) = Valid Γ).
    rewrite e at 2.
    rewrite <- (IHW1 Γ1 p1); trivial.
    rewrite <- (IHW2 Γ2 p2); trivial.
    destruct (trim_merge Γ Γ1 Γ2). solve_merge. assumption.
    apply pf_merge.
    simpl in H1. 
    rewrite ctx_octx in H1.
    easy.
Qed.

Lemma remove_bit_merge' : forall (Γ Γ' : Ctx) v, Γ' == singleton v Bit ∙ Γ ->
                                            remove_pat (bit v) Γ' = trim Γ.
Proof.      
  intros Γ Γ' v H.
  apply merge_fun_ind in H.
  dependent induction H.
  - destruct v; inversion x.
  - induction v.
    + simpl. unfold remove_pat. simpl. easy.
    + simpl. 
      unfold remove_pat in *.
      unfold remove_var in *.
      simpl in *.
      rewrite IHv.      
      easy.
 - destruct v.
   + inversion x; subst.
     inversion m; subst.
     unfold remove_pat.
     simpl in *.
     inversion H; subst; easy.
   + inversion x; subst.
     inversion m; subst.
     unfold remove_pat, remove_var in *.     
     simpl in *.
     erewrite IHmerge_ind; easy.
     replace (remove_pat (bit (S v)) (Some w :: Γ0)) with
        (Some w :: remove_pat (bit v) (Γ0)) by easy.
     simpl.
     erewrite IHmerge_ind; easy.
Qed.     

Lemma remove_bit_merge : forall (Γ Γ' : Ctx) W (p : Pat W) v, 
  Γ ⊢ p:Pat ->
  Γ' == singleton v Bit ∙ Γ ->
  remove_pat (bit v)  Γ' = Γ.
Proof.
  intros Γ Γ' W p v H H0.
  erewrite <- (types_pat_no_trail Γ) by apply H.
  simpl.
  assert (remove_pat (bit v) Γ' = trim Γ).
  apply remove_bit_merge'; easy.
  inversion H1.  
  easy.
Qed.

Lemma remove_qubit_merge' : forall (Γ Γ' : Ctx) v, Γ' == singleton v Qubit ∙ Γ ->
                                            remove_pat (qubit v)  Γ' = trim Γ.
Proof.      
  intros Γ Γ' v H.
  apply merge_fun_ind in H.
  dependent induction H.
  - destruct v; inversion x.
  - induction v.
    + simpl. unfold remove_pat. simpl. easy.
    + simpl. 
      unfold remove_pat, remove_var in *.
      simpl in *.
      inversion IHv.
      rewrite H0.
      easy.
 - destruct v.
   + inversion x; subst.
     inversion m; subst.
     unfold remove_pat.
     simpl in *.
     inversion H; subst; easy.
   + inversion x; subst.
     inversion m; subst.
     unfold remove_pat, remove_var in *.
     simpl in *.
     erewrite IHmerge_ind; easy.
     replace (remove_pat (qubit (S v)) (Some w :: Γ0)) with
        (Some w :: remove_pat (qubit v) (Γ0)) by easy.
     simpl.
     erewrite IHmerge_ind; easy.
Qed.     

Lemma remove_qubit_merge : forall (Γ Γ' : Ctx) W (p : Pat W) v, 
  Γ ⊢ p:Pat ->
  Γ' == singleton v Qubit ∙ Γ ->
  remove_pat (qubit v)  Γ' = Γ.
Proof.
  intros Γ Γ' W p v H H0.
  erewrite <- (types_pat_no_trail Γ) by apply H.
  simpl.
  assert (remove_pat (bit v) Γ' = trim Γ).
  apply remove_qubit_merge'; easy.
  inversion H1.  
  easy.
Qed.

Lemma remove_bit_pred : forall (Γ Γ' : Ctx) v, 
    Γ' == (singleton v Bit) ∙ Γ ->
    size_ctx (remove_pat (bit v) Γ') = (size_ctx Γ' - 1)%nat.
Proof.
  intros Γ Γ' v H.
  rewrite (remove_bit_merge' Γ Γ'); trivial.
  destruct H.
  replace (size_ctx Γ') with (size_octx Γ') by easy.
  rewrite pf_merge in *.   
  rewrite size_octx_merge by easy. 
  simpl. rewrite singleton_size. 
  rewrite size_ctx_trim.
  omega.
Qed.

Lemma remove_qubit_pred : forall (Γ Γ' : Ctx) v, 
    Γ' == (singleton v Qubit) ∙ Γ ->
    size_ctx (remove_pat (qubit v) Γ') = (size_ctx Γ' - 1)%nat.
Proof.
  intros Γ Γ' v H.
  rewrite (remove_qubit_merge' Γ Γ'); trivial.
  destruct H.
  replace (size_ctx Γ') with (size_octx Γ') by easy.
  rewrite pf_merge in *.   
  rewrite size_octx_merge by easy. 
  simpl. rewrite singleton_size. 
  rewrite size_ctx_trim.
  omega.
Qed.

(* Move these to somewhere relevant *)
Lemma maps_to_trim : forall Γ v, maps_to v (trim Γ) = maps_to v Γ.
Proof.
  intros Γ v. gen Γ.
  induction v; intros Γ.
  - destruct Γ; trivial. 
    destruct o; trivial.
    simpl. destruct (trim Γ); easy.
  - destruct Γ; trivial.
    simpl. 
    destruct o.
    rewrite IHv; easy.
    rewrite <- IHv.
    destruct (trim Γ) eqn:E; trivial.
    destruct v; easy.
Qed.

Lemma subst_pat_trim : forall W Γ (p : Pat W), subst_pat (trim Γ) p = subst_pat Γ p.
Proof.
  intros W Γ p.
  induction p.
  - simpl. easy.
  - simpl. unfold subst_var. rewrite maps_to_trim. easy.
  - simpl. unfold subst_var. rewrite maps_to_trim. easy. 
  - simpl. rewrite IHp1, IHp2. easy.
Qed.    

Proposition hoas_to_db_trim : forall W Γ (c : Circuit W), hoas_to_db (trim Γ) c = hoas_to_db Γ c.
Proof.
  intros W Γ c.
  induction c.
  - simpl. rewrite subst_pat_trim. easy.
  - simpl. rewrite subst_pat_trim. 
    destruct g eqn:E.
    + simpl. rewrite H. easy. 
    + simpl. rewrite H. easy. 
    + simpl. (*nope! and not even close to true for flatten_ctx *) 
Abort.

Lemma trim_types_circ : forall W (c : Circuit W) (Γ : Ctx), Γ ⊢ c :Circ -> trim Γ ⊢ c :Circ.
Proof.
  intros W c.
  induction c.
  - intros Γ WT. 
    dependent destruction WT.
    erewrite types_pat_no_trail by apply t. 
    econstructor; easy.
  - intros Γ WT.
    dependent destruction WT.
    destruct Γ0 as [|Γ0], Γ1 as [|Γ1]; try invalid_contradiction.
    specialize (types_pat_no_trail _ _ _ t) as NT1.
    econstructor.
    rewrite <- NT1 in t.
    apply t.
    2: apply (trim_merge Γ Γ1 Γ0 pf1).
    simpl. intros Γ1' Γ' p2 M' t'.
    destruct Γ1' as [|Γ1']; try invalid_contradiction.
    assert (M'' : (Γ1' ⋓ Γ0) == Γ1' ∙ Γ0).
      split; trivial. 
      apply trim_valid.
      destruct M'. 
      apply types_pat_no_trail in t'.
      rewrite <- t' in pf_merge.
      rewrite <- trim_merge_dist.
      simpl.
      rewrite <- pf_merge.
      easy.
    specialize (t0 Γ1' (Γ1' ⋓ Γ0) p2 M'' t').
    destruct M'.
    rewrite pf_merge.
    apply types_pat_no_trail in t'.
    rewrite <- t'.
    simpl_rewrite (trim_merge_dist Γ1' Γ0).
    destruct (Γ1' ⋓ Γ0) as [|Γ'']; try invalid_contradiction.
    simpl.
    apply H.
    apply t0.
  - intros Γ H0.
    dependent destruction H0.
    destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.
    econstructor.
    apply t.
    intros b.
    apply H.
    apply t0.
    apply types_pat_no_trail in t.
    rewrite <- t.
    apply (trim_merge Γ Γ1 Γ2).
    easy.
Qed.

Proposition WF_denote_circuit : forall safe W (c : Circuit W) (Γ0 Γ : Ctx) ρ,
  Γ ⊢ c:Circ -> 
  WF_Matrix (2^(⟦Γ0⟧ + ⟦Γ⟧)) (2^(⟦Γ0⟧ + ⟦Γ⟧)) ρ -> 
  WF_Matrix (2^(⟦Γ0⟧ + ⟦W⟧)) (2^(⟦Γ0⟧ + ⟦W⟧)) (denote_circuit safe c Γ0 Γ ρ).
Proof.
  intros safe W c.
  induction c.
  - intros Γ0 Γ ρ WT WF.
    dependent destruction WT.
    unfold denote_circuit. simpl.
    unfold denote_pat.
    unfold pad.
    subst.
    rewrite (ctx_wtype_size w p Γ t).
    rewrite Nat.add_sub.
    apply WF_super; trivial.
    apply WF_kron; unify_pows_two; auto with wf_db.
    erewrite ctx_wtype_size by apply t.
    apply WF_swap_list.
    rewrite size_wtype_length.
    erewrite ctx_wtype_size by apply t. omega.
    intros x.
    apply (pat_to_list_bounded _ Γ Γ []).
    solve_merge.
    easy.
  - intros Γ0 Γ ρ WT WF.
    dependent destruction WT.
    unfold compose_super.
    rename H into IH. 
    unfold denote_circuit; simpl.
    destruct g.
    + simpl.
      destruct pf1.
      replace (size_ctx Γ) with (size_octx Γ) by easy.
      rewrite pf_merge in *.
      rewrite size_octx_merge by easy.
      simpl_rewrite (octx_wtype_size W p Γ2 t).
      rewrite leb_correct by omega.
      unfold compose_super.
      unfold denote_circuit in IH.
      unfold process_gate_state. simpl.
      rewrite Nat.add_sub.
      rewrite <- size_octx_merge by easy.
      rewrite <- pf_merge in *. simpl.
      simpl in IH.
      eapply (IH p); trivial. 
      eapply t0; [|apply t].
      split; easy.
      unfold apply_U.
      destruct W.
      * simpl.
        unfold apply_to_first, apply_qubit_unitary, super.
        specialize (size_wtype_length (subst_pat Γ p)) as L. simpl in L.
        destruct (pat_to_list (subst_pat Γ p)) eqn:E; simpl in L; try omega. 
        Msimpl.
        assert (M : Γ == Γ2 ∙ Γ1) by (split; auto).
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.
        assert (IN : In v (pat_to_list (subst_pat Γ p))) by (rewrite E; simpl; auto).
        specialize (pat_to_list_bounded Qubit _ _ _ p v M t IN) as LT.
        replace (2^(size_ctx Γ0 + size_ctx Γ))%nat with 
            (2 ^ v * 2 * 2 ^ (size_ctx Γ0 + size_ctx Γ - v - 1))%nat by unify_pows_two.
        apply WF_mult.
        apply WF_mult.
        apply WF_kron; trivial.
        apply WF_kron; trivial; auto with wf_db.
        apply (@unitary_gate_unitary Qubit).        
        auto with wf_db.
        unify_pows_two.
        apply_with_obligations WF. simpl; unify_pows_two.
        apply WF_kron; trivial.
        apply WF_kron; trivial; auto with wf_db.
        apply WF_adjoint.
        apply (@unitary_gate_unitary Qubit).        
        auto with wf_db.
      * unfold super.
        apply WF_mult.
        apply WF_mult.
        apply denote_ctrls_unitary.
        apply forallb_forall. intros x IN.
        apply Nat.ltb_lt.
        apply Nat.lt_lt_add_l.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.        
        eapply pat_to_list_bounded.
        split; [apply pf_valid|apply pf_merge].
        apply t.
        easy.
        rewrite size_wtype_length. easy.
        apply WF.
        apply WF_adjoint.
        apply denote_ctrls_unitary.
        apply forallb_forall. intros x IN.
        apply Nat.ltb_lt.
        apply Nat.lt_lt_add_l.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.        
        eapply pat_to_list_bounded.
        split; [apply pf_valid|apply pf_merge].
        apply t.
        easy.
        rewrite size_wtype_length. easy.
      * unfold super.
        apply WF_mult.
        apply WF_mult.
        apply denote_ctrls_unitary.
        apply forallb_forall. intros x IN.
        apply Nat.ltb_lt.
        apply Nat.lt_lt_add_l.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.        
        eapply pat_to_list_bounded.
        split; [apply pf_valid|apply pf_merge].
        apply t.
        easy.
        rewrite size_wtype_length. easy.
        apply WF.
        apply WF_adjoint.
        apply denote_ctrls_unitary.
        apply forallb_forall. intros x IN.
        apply Nat.ltb_lt.
        apply Nat.lt_lt_add_l.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.        
        eapply pat_to_list_bounded.
        split; [apply pf_valid|apply pf_merge].
        apply t.
        easy.
        rewrite size_wtype_length. easy.
      * unfold super.
        apply WF_mult.
        apply WF_mult.
        apply denote_ctrls_unitary.
        apply forallb_forall. intros x IN.
        apply Nat.ltb_lt.
        apply Nat.lt_lt_add_l.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.        
        eapply pat_to_list_bounded.
        split; [apply pf_valid|apply pf_merge].
        apply t.
        easy.
        rewrite size_wtype_length. easy.
        apply WF.
        apply WF_adjoint.
        apply denote_ctrls_unitary.
        apply forallb_forall. intros x IN.
        apply Nat.ltb_lt.
        apply Nat.lt_lt_add_l.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.        
        eapply pat_to_list_bounded.
        split; [apply pf_valid|apply pf_merge].
        apply t.
        easy.
        rewrite size_wtype_length. easy.
    + simpl.
      rewrite Nat.add_sub.
      replace (size_ctx Γ0 + size_ctx Γ)%nat with (S (⟦Γ0⟧ + ⟦Γ1⟧))%nat.
      Focus 2.
        destruct pf1.
        replace (size_ctx Γ) with (size_octx Γ) by easy.
        rewrite pf_merge in *.
        rewrite size_octx_merge by easy.
        rewrite <- (octx_wtype_size Bit p Γ2 t).
        simpl. omega.
      unfold compose_super.
      unfold denote_circuit in IH.
      eapply IH.
      eapply t0. apply pf1. easy.
      unfold apply_to_first, apply_qubit_unitary, super.
      specialize (size_wtype_length (subst_pat Γ p)) as L. simpl in L.
      destruct (pat_to_list (subst_pat Γ p)) eqn:E; simpl in L; try omega. 
      Msimpl.
      destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.
      assert (IN : In v (pat_to_list (subst_pat Γ p))) by (rewrite E; simpl; auto).
      specialize (pat_to_list_bounded Bit _ _ _ p v pf1 t IN) as LT.
      destruct pf1. 
      replace (⟦Γ⟧) with (⟦Valid Γ⟧) by easy.
      replace (size_ctx Γ) with (size_octx Γ) in LT by easy.
      rewrite pf_merge in *.
      rewrite size_octx_merge in * by easy.
      rewrite <- (octx_wtype_size Bit p Γ2 t) in *.        
      replace (2 ^ (⟦ Γ0 ⟧ + (size_wtype Bit + size_octx Γ1)))%nat with 
          (2 ^ v * 2 * 2 ^ (S (⟦ Γ0 ⟧ + ⟦ Γ1 ⟧) - v - 1))%nat.
      Focus 2.
        unify_pows_two. simpl in *. destruct v; omega. 
      apply WF_mult.
      apply WF_mult.
      apply WF_kron; trivial.
      apply WF_kron; trivial; auto with wf_db.
      auto with wf_db.
      unify_pows_two.
      auto with wf_db.
      simpl (denote Γ0). simpl (denote (Valid Γ1)).
      replace (v + 1 + (S (size_ctx Γ0 + size_ctx Γ1) - v - 1))%nat with
          (size_ctx Γ0 + size_ctx Γ)%nat. 
      easy. 
      simpl in *.  
      replace (size_ctx Γ) with (size_octx Γ) by easy.
      rewrite pf_merge.
      rewrite size_octx_merge by easy.
      rewrite <- (octx_wtype_size Bit p Γ2 t).
      simpl.
      destruct v; omega.
      auto with wf_db.
    + simpl.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      rewrite Nat.sub_0_r.
      apply WF_compose_super; intros.
      * apply WF.
      * unfold apply_new0.
        replace (2 ^ (size_ctx Γ0 + (size_ctx Γ + 1)))%nat with
            (2 ^ (size_ctx Γ0 + size_ctx Γ) * 2)%nat by unify_pows_two.
        apply WF_super.
        auto with wf_db.
        rewrite Nat.mul_1_r.
        easy.
      * replace (size_ctx Γ + 1)%nat with (size_octx (Valid (Γ ++ [Some Qubit]))). 
          2: simpl; rewrite size_ctx_app; simpl; omega. 
        eapply IH.
        eapply t0. 
        split. validate.
        rewrite merge_comm. 
        rewrite merge_singleton_append.
        reflexivity.
        constructor; apply singleton_singleton.
        rewrite size_ctx_app; easy.
    + simpl.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      rewrite Nat.sub_0_r.
      apply WF_compose_super; intros.
      * apply WF.
      * unfold apply_new1.
        replace (2 ^ (size_ctx Γ0 + (size_ctx Γ + 1)))%nat with
            (2 ^ (size_ctx Γ0 + size_ctx Γ) * 2)%nat by unify_pows_two.
        apply WF_super.
        auto with wf_db.
        rewrite Nat.mul_1_r.
        easy.
      * replace (size_ctx Γ + 1)%nat with (size_octx (Valid (Γ ++ [Some Qubit]))). 
          2: simpl; rewrite size_ctx_app; simpl; omega. 
        eapply IH.
        eapply t0. 
        split. validate.
        rewrite merge_comm. 
        rewrite merge_singleton_append.
        reflexivity.
        constructor; apply singleton_singleton.
        rewrite size_ctx_app; easy.
    + simpl.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      rewrite Nat.sub_0_r.
      apply WF_compose_super; intros.
      * apply WF.
      * unfold apply_new0.
        replace (2 ^ (size_ctx Γ0 + (size_ctx Γ + 1)))%nat with
            (2 ^ (size_ctx Γ0 + size_ctx Γ) * 2)%nat by unify_pows_two.
        apply WF_super.
        auto with wf_db.
        rewrite Nat.mul_1_r.
        easy.
      * replace (size_ctx Γ + 1)%nat with (size_octx (Valid (Γ ++ [Some Bit]))). 
          2: simpl; rewrite size_ctx_app; simpl; omega. 
        eapply IH.
        eapply t0. 
        split. validate.
        rewrite merge_comm. 
        rewrite merge_singleton_append.
        reflexivity.
        constructor; apply singleton_singleton.
        rewrite size_ctx_app; easy.
    + simpl.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      rewrite Nat.sub_0_r.
      apply WF_compose_super; intros.
      * apply WF.
      * unfold apply_new1.
        replace (2 ^ (size_ctx Γ0 + (size_ctx Γ + 1)))%nat with
            (2 ^ (size_ctx Γ0 + size_ctx Γ) * 2)%nat by unify_pows_two.
        apply WF_super.
        auto with wf_db.
        rewrite Nat.mul_1_r.
        easy.
      * replace (size_ctx Γ + 1)%nat with (size_octx (Valid (Γ ++ [Some Bit]))). 
          2: simpl; rewrite size_ctx_app; simpl; omega. 
        eapply IH.
        eapply t0. 
        split. validate.
        rewrite merge_comm. 
        rewrite merge_singleton_append.
        reflexivity.
        constructor; apply singleton_singleton.
        rewrite size_ctx_app; easy.
    + simpl.
      dependent destruction t.
      simpl.
      rewrite Nat.add_sub.
      apply WF_compose_super; intros.
      * apply WF.
      * unfold apply_meas.       
        unfold Splus.
        destruct Γ1 as [|Γ1]; try invalid_contradiction.
        specialize (subst_qubit_bounded _ _ _ _ (types_qubit _ _ s) pf1) as LT. 
        simpl in LT.
        replace (2 ^ (size_ctx Γ0 + size_ctx Γ))%nat with
          (2 ^ subst_var Γ x * 2 * 2 ^ (size_ctx Γ0 + size_ctx Γ - 
          subst_var Γ x - 1))%nat in * by unify_pows_two. 
        auto with wf_db.
      * unfold denote_circuit in IH.
        replace (size_ctx Γ) with (size_ctx (change_type x Bit Γ)).
        Focus 2.
          unfold change_type.
          eapply denote_index_update_some.
          eapply index_merge_l.
          apply pf1.
          apply singleton_index.
          apply s.
        eapply IH. 
        unfold change_type.
        eapply t0.
        eapply update_at_merge.
        apply s.
        apply singleton_singleton.
        easy.
        constructor.
        apply singleton_singleton.
        unfold change_type.
        erewrite denote_index_update_some.
        apply H.
        eapply index_merge_l.
        apply pf1.
        apply singleton_index.
        apply s.
    + (* Why isn't this case identical to apply_meas? *)
      simpl.
      rewrite Nat.add_sub.
      unfold apply_to_first.
      specialize (size_wtype_length (subst_pat Γ p)) as L. simpl in L.
      destruct (pat_to_list (subst_pat Γ p)) eqn:E; simpl in L; try omega. 
      apply WF_compose_super; intros.
      * easy.
      * unfold apply_meas.
        unfold Splus.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.   
        assert (IN: In v (pat_to_list (subst_pat Γ p))).
          rewrite E. simpl. auto.
        specialize (pat_to_list_bounded _ _ _ _ _ _ pf1 t IN) as LT.
        replace (2 ^ (size_ctx Γ0 + size_ctx Γ))%nat with
          (2 ^ v * 2 * 2 ^ (size_ctx Γ0 + size_ctx Γ - v - 1))%nat in * 
          by unify_pows_two. 
        auto with wf_db.
      * eapply (IH p). eapply t0. apply pf1. easy. easy.
    + simpl in *.
      apply WF_compose_super.
      * easy.
      * intros A WFA.
        rewrite Nat.add_0_r.
        replace (size_ctx Γ - 1)%nat with (size_octx Γ1) in *.
        Focus 2.
          simpl.
          replace (size_ctx Γ) with (size_octx Γ) by easy.
          destruct pf1.
          rewrite pf_merge in *.
          rewrite size_octx_merge by easy. 
          dependent destruction t.
          apply singleton_equiv in s. subst.
          simpl. rewrite singleton_size.
          omega.
        simpl.
        unfold apply_to_first.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.   
        dependent destruction t. simpl.
        unfold apply_discard.
        unfold Splus.
        specialize (subst_bit_bounded _ _ _ _ (types_bit _ _ s) pf1) as LT. 
        simpl in LT.
        replace (size_ctx Γ) with (size_octx Γ) in * by easy.
        destruct pf1. rewrite pf_merge in *.
        rewrite size_octx_merge in * by easy.
        apply singleton_equiv in s. subst.
        simpl in *. rewrite singleton_size in *.
        replace (2 ^ (size_ctx Γ0 + size_ctx Γ1))%nat with
            (2 ^ subst_var Γ x * 1 * 2 ^ (size_ctx Γ0 + (1 + size_ctx Γ1) 
             - subst_var Γ x - 1))%nat in * by unify_pows_two.
        replace (2 ^ (size_ctx Γ0 + (1 + size_ctx Γ1)))%nat with (2 ^ subst_var Γ x * 2
          * 2 ^ (size_ctx Γ0 + (1 + size_ctx Γ1) - subst_var Γ x - 1))%nat in WFA by
          unify_pows_two.
        apply WF_plus; auto with wf_db.
      * rewrite Nat.add_0_r.
        intros A.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.
        replace (size_ctx Γ - 1)%nat with (size_octx Γ1) in *.
        Focus 2.
          simpl.
          replace (size_ctx Γ) with (size_octx Γ) by easy.
          destruct pf1.
          rewrite pf_merge in *.
          rewrite size_octx_merge by easy. 
          dependent destruction t.
          apply singleton_equiv in s. subst.
          simpl. rewrite singleton_size.
          omega.
        intros WFA.
        dependent destruction t.
        apply singleton_equiv in s; subst.
        assert (M: Γ1 == ∅ ∙ Γ1) by solve_merge.
        specialize (t0 ∅ Γ1 unit M types_unit).
        erewrite remove_bit_merge' by apply pf1.
        specialize (IH unit Γ0 (trim Γ1) A). 
        unfold denote_circuit in IH.
        simpl in IH.
        rewrite size_ctx_trim in IH.
        apply IH. 
        apply trim_types_circ. easy.
        easy.
    + simpl in *.
      apply WF_compose_super.
      * easy.
      * intros A WFA.
        rewrite Nat.add_0_r.
        replace (size_ctx Γ - 1)%nat with (size_octx Γ1) in *.
        Focus 2.
          simpl.
          replace (size_ctx Γ) with (size_octx Γ) by easy.
          destruct pf1.
          rewrite pf_merge in *.
          rewrite size_octx_merge by easy. 
          dependent destruction t.
          apply singleton_equiv in s. subst.
          simpl. rewrite singleton_size.
          omega.
        simpl.
        unfold apply_to_first.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.   
        dependent destruction t. simpl.
        unfold apply_assert0.
        unfold Splus.
        specialize (subst_qubit_bounded _ _ _ _ (types_qubit _ _ s) pf1) as LT. 
        simpl in LT.
        replace (size_ctx Γ) with (size_octx Γ) in * by easy.
        destruct pf1. rewrite pf_merge in *.
        rewrite size_octx_merge in * by easy.
        apply singleton_equiv in s. subst.
        simpl in *. rewrite singleton_size in *.
        replace (2 ^ (size_ctx Γ0 + size_ctx Γ1))%nat with
            (2 ^ subst_var Γ x * 1 * 2 ^ (size_ctx Γ0 + (1 + size_ctx Γ1) 
             - subst_var Γ x - 1))%nat in * by unify_pows_two.
        replace (2 ^ (size_ctx Γ0 + (1 + size_ctx Γ1)))%nat with (2 ^ subst_var Γ x * 2
          * 2 ^ (size_ctx Γ0 + (1 + size_ctx Γ1) - subst_var Γ x - 1))%nat in WFA by
          unify_pows_two.
        destruct safe.
        apply WF_plus; auto with wf_db.
        auto with wf_db.
      * rewrite Nat.add_0_r.
        intros A.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.
        replace (size_ctx Γ - 1)%nat with (size_octx Γ1) in *.
        Focus 2.
          simpl.
          replace (size_ctx Γ) with (size_octx Γ) by easy.
          destruct pf1.
          rewrite pf_merge in *.
          rewrite size_octx_merge by easy. 
          dependent destruction t.
          apply singleton_equiv in s. subst.
          simpl. rewrite singleton_size.
          omega.
        intros WFA.
        dependent destruction t.
        apply singleton_equiv in s; subst.
        assert (M: Γ1 == ∅ ∙ Γ1) by solve_merge.
        specialize (t0 ∅ Γ1 unit M types_unit).
        erewrite remove_qubit_merge' by apply pf1.
        specialize (IH unit Γ0 (trim Γ1) A). 
        unfold denote_circuit in IH.
        simpl in IH.
        rewrite size_ctx_trim in IH.
        apply IH. 
        apply trim_types_circ. easy.
        easy.
    + simpl in *.
      apply WF_compose_super.
      * easy.
      * intros A WFA.
        rewrite Nat.add_0_r.
        replace (size_ctx Γ - 1)%nat with (size_octx Γ1) in *.
        Focus 2.
          simpl.
          replace (size_ctx Γ) with (size_octx Γ) by easy.
          destruct pf1.
          rewrite pf_merge in *.
          rewrite size_octx_merge by easy. 
          dependent destruction t.
          apply singleton_equiv in s. subst.
          simpl. rewrite singleton_size.
          omega.
        simpl.
        unfold apply_to_first.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.   
        dependent destruction t. simpl.
        unfold apply_assert1.
        unfold Splus.
        specialize (subst_qubit_bounded _ _ _ _ (types_qubit _ _ s) pf1) as LT. 
        simpl in LT.
        replace (size_ctx Γ) with (size_octx Γ) in * by easy.
        destruct pf1. rewrite pf_merge in *.
        rewrite size_octx_merge in * by easy.
        apply singleton_equiv in s. subst.
        simpl in *. rewrite singleton_size in *.
        replace (2 ^ (size_ctx Γ0 + size_ctx Γ1))%nat with
            (2 ^ subst_var Γ x * 1 * 2 ^ (size_ctx Γ0 + (1 + size_ctx Γ1) 
             - subst_var Γ x - 1))%nat in * by unify_pows_two.
        replace (2 ^ (size_ctx Γ0 + (1 + size_ctx Γ1)))%nat with (2 ^ subst_var Γ x * 2
          * 2 ^ (size_ctx Γ0 + (1 + size_ctx Γ1) - subst_var Γ x - 1))%nat in WFA by
          unify_pows_two.
        destruct safe.
        apply WF_plus; auto with wf_db.
        auto with wf_db.
      * rewrite Nat.add_0_r.
        intros A.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.
        replace (size_ctx Γ - 1)%nat with (size_octx Γ1) in *.
        Focus 2.
          simpl.
          replace (size_ctx Γ) with (size_octx Γ) by easy.
          destruct pf1.
          rewrite pf_merge in *.
          rewrite size_octx_merge by easy. 
          dependent destruction t.
          apply singleton_equiv in s. subst.
          simpl. rewrite singleton_size.
          omega.
        intros WFA.
        dependent destruction t.
        apply singleton_equiv in s; subst.
        assert (M: Γ1 == ∅ ∙ Γ1) by solve_merge.
        specialize (t0 ∅ Γ1 unit M types_unit).
        erewrite remove_qubit_merge' by apply pf1.
        specialize (IH unit Γ0 (trim Γ1) A). 
        unfold denote_circuit in IH.
        simpl in IH.
        rewrite size_ctx_trim in IH.
        apply IH. 
        apply trim_types_circ. easy.
        easy.
  - intros Γ0 Γ ρ WT WF.
    dependent destruction WT.
    unfold denote_circuit in *.
    dependent destruction t.
    destruct Γ2 as [|Γ2]; try invalid_contradiction.
    specialize (subst_bit_bounded _ _ _ _ (types_bit _ _ s) pf) as LT. 
    simpl in *.
    unfold Splus.
    apply WF_plus.
    + apply WF_compose_super.
      * apply_with_obligations WF.
        unify_pows_two.
      * intros A WFA.
        replace (2 ^ (size_ctx Γ0 + (size_ctx Γ - 1)))%nat with 
            (2 ^ subst_var Γ x * 1 * 2 ^ (size_ctx Γ + size_ctx Γ0 - subst_var Γ x - 1))%nat
        by unify_pows_two.
        apply WF_super.
        auto with wf_db.
        apply_with_obligations WFA.
      * intros A WFA.
        replace (size_ctx Γ - 1)%nat with (size_octx Γ2) in *.
        Focus 2.
          simpl.
          replace (size_ctx Γ) with (size_octx Γ) by easy.
          destruct pf.
          rewrite pf_merge in *.
          rewrite size_octx_merge by easy. 
          apply singleton_equiv in s. subst.
          simpl. rewrite singleton_size.
          omega.
        apply singleton_equiv in s; subst.
        specialize (t0 false).
        erewrite remove_bit_merge'; [|apply pf].
        specialize (H false Γ0 (trim Γ2)).
        rewrite size_ctx_trim in H.
        eapply H.
        apply trim_types_circ. easy.
        easy.
    + apply WF_compose_super.
      * apply_with_obligations WF.
        unify_pows_two.
      * intros A WFA.
        replace (2 ^ (size_ctx Γ0 + (size_ctx Γ - 1)))%nat with 
            (2 ^ subst_var Γ x * 1 * 2 ^ (size_ctx Γ + size_ctx Γ0 - subst_var Γ x - 1))%nat
        by unify_pows_two.
        apply WF_super.
        auto with wf_db.
        apply_with_obligations WFA.
      * intros A WFA.
        replace (size_ctx Γ - 1)%nat with (size_octx Γ2) in *.
        Focus 2.
          simpl.
          replace (size_ctx Γ) with (size_octx Γ) by easy.
          destruct pf.
          rewrite pf_merge in *.
          rewrite size_octx_merge by easy. 
          apply singleton_equiv in s. subst.
          simpl. rewrite singleton_size.
          omega.
        apply singleton_equiv in s; subst.
        specialize (t0 true).
        erewrite remove_bit_merge'; [|apply pf].
        specialize (H true Γ0 (trim Γ2)).
        rewrite size_ctx_trim in H.
        eapply H.
        apply trim_types_circ. easy.
        easy.
Qed.

Proposition WF_denote_box : forall safe W1 W2 (c : Box W1 W2) ρ,
  Typed_Box c ->
  WF_Matrix (2^(⟦W1⟧)) (2^(⟦W1⟧)) ρ -> 
  WF_Matrix (2^(⟦W2⟧)) (2^(⟦W2⟧)) (denote_box safe c ρ).
Proof.
  intros safe W1 W2 c ρ T WF.
  destruct c.
  unfold denote_box. simpl.
  unfold denote_db_box.
  simpl.
  destruct (add_fresh W1 []) as [p Γ] eqn:E.
  unfold Typed_Box in T.
  symmetry in E. apply add_fresh_typed with (p0 := unit) in E; try constructor.
  dependent destruction E.
  specialize (T Γ2 p E2). simpl in T.
  dependent destruction E1. rewrite merge_nil_l in e; subst.
  specialize (WF_denote_circuit safe W2 (c p) [] Γ ρ T) as WFC.
  unfold denote_circuit in WFC.
  simpl in *.
  rewrite (ctx_wtype_size _ _ _ E2) in *.
  apply WFC.
  easy.
Qed.

Inductive Static_Circuit {W} : Circuit W -> Prop := 
| S_output : forall p, Static_Circuit (output p)
| S_gate :   forall w1 w2 (g : Gate w1 w2) (p : Pat w1) (c' : Pat w2 -> Circuit W),
               (forall p2, Static_Circuit (c' p2)) ->
               Static_Circuit (gate g p c').

Inductive Static_Box {W1 W2} : Box W1 W2 -> Prop := 
| S_box : forall c, (forall p, Static_Circuit (c p)) -> Static_Box (box c).

Theorem denote_static_circuit_correct : forall W (Γ0 Γ : Ctx) (c : Circuit W),
  Static_Circuit c ->
  Γ ⊢ c:Circ -> 
  WF_Superoperator (⟨ Γ0 | Γ ⊩ c⟩).
Proof.
  intros W Γ0 Γ c.
  gen Γ0 Γ.
  induction c; intros Γ0 Γ STAT WT.
  - dependent destruction WT.
    unfold denote_circuit. simpl.
    unfold denote_pat.
    unfold pad.
    subst.
    rewrite (ctx_wtype_size w p Γ t).
    apply super_unitary_correct.
    rewrite Nat.add_sub.
    match goal with
    | [|- WF_Unitary (?A ⊗ ?B)] => specialize (kron_unitary A B) as KU
    end.
    unify_pows_two.
    simpl in *. rewrite (ctx_wtype_size w p Γ t) in *.    
    replace (2 ^ (size_ctx Γ0 + size_ctx Γ))%nat 
      with (2 ^ size_ctx Γ * 2 ^ size_ctx Γ0)%nat by (simpl; unify_pows_two). 
    apply KU.
    apply swap_list_unitary.
    rewrite size_wtype_length.
    rewrite (ctx_wtype_size w p Γ t). omega.
    intros x.
    eapply pat_to_list_bounded.
    split. validate.
    rewrite merge_nil_r. easy.
    easy.
    apply id_unitary.
  - dependent destruction WT.
    rename p into p1. rename Γ1 into Γ3. rename Γ2 into Γ1. rename Γ3 into Γ2.
    dependent destruction STAT. 
    rename H0 into STAT. rename H into IH. 
    unfold denote_circuit; simpl.
    destruct g.
    + simpl.
      destruct pf1.
      replace (size_ctx Γ) with (size_octx Γ) by easy.
      rewrite pf_merge in *.
      rewrite size_octx_merge by easy.
      simpl_rewrite (octx_wtype_size W p1 Γ1 t).
      rewrite leb_correct by omega.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        rewrite Nat.add_sub.
        rewrite <- size_octx_merge by easy.
        rewrite <- pf_merge in *. simpl.
        eapply (IH p1); trivial. 
        eapply t0.
        split. easy. apply pf_merge. easy.
      * rewrite Nat.add_sub.
        apply apply_U_correct.
        rewrite size_wtype_length.
        reflexivity.
        unfold subst_pat.
        replace (size_wtype W) with (⟦W⟧) by easy.
        rewrite <- size_octx_merge by easy.
        apply forallb_forall.
        intros x IN.
        specialize Nat.ltb_lt as [L R]. rewrite R. easy. clear L R.
        apply Nat.lt_lt_add_l.
        rewrite <- pf_merge in *.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.
        eapply pat_to_list_bounded.        
        split. assumption. apply pf_merge. apply t. 
        apply IN.
    + simpl.
      destruct pf1.
      rewrite pf_merge in *.
      rewrite Nat.add_sub.
      apply compose_super_correct.
      * eapply IH. 
        apply STAT.
        eapply t0.
        split.
        rewrite pf_merge.
        apply pf_valid.
        apply pf_merge.
        easy.
      * replace (size_ctx Γ) with (size_octx Γ) by easy.
        rewrite pf_merge.
        rewrite size_octx_merge by easy.
        dependent destruction p1.
        dependent destruction t.
        apply singleton_equiv in s; subst.
        simpl. rewrite singleton_size.
        simpl.
        rewrite Nat.add_succ_r.
        specialize (apply_U_correct Qubit) as AUC.
        simpl in AUC.
        unfold process_gate_state. simpl.
        unify_pows_two.
        rewrite Nat.add_1_r.
        apply (AUC _ _X [subst_var Γ v]).
        easy.
        apply forallb_forall.
        intros x IN.
        specialize Nat.ltb_lt as [L R]. rewrite R. easy. clear L R.
        assert (L : (x < size_octx Γ)%nat).        
        destruct Γ2 as [|Γ2]; try invalid_contradiction.
        eapply pat_to_list_bounded.
        split. validate. apply pf_merge.
        apply types_bit. apply singleton_singleton.
        easy.
        rewrite pf_merge in L.
        rewrite size_octx_merge in L; trivial.
        simpl in L. rewrite singleton_size in L.
        omega.
    + simpl.
      dependent destruction p1.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      unfold subst_pat. simpl.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        rewrite Nat.sub_0_r.
        replace (size_ctx Γ + 1)%nat with (size_octx (Valid (Γ ++ [Some Qubit]))). 
          2: simpl; rewrite size_ctx_app; simpl; omega. 
        eapply IH.
        apply STAT.
        eapply t0.
        split. validate.
        rewrite merge_comm. 
        rewrite merge_singleton_append.
        easy.
        constructor; apply singleton_singleton.
      * rewrite Nat.sub_0_r.
        rewrite Nat.add_assoc.
        apply apply_new0_correct.
    + simpl.
      dependent destruction p1.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      unfold subst_pat. simpl.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        rewrite Nat.sub_0_r.
        replace (size_ctx Γ + 1)%nat with (size_octx (Valid (Γ ++ [Some Qubit]))). 
          2: simpl; rewrite size_ctx_app; simpl; omega. 
        eapply IH.
        apply STAT. 
        eapply t0. 
        split. validate.
        rewrite merge_comm. 
        rewrite merge_singleton_append.
        easy.
        constructor; apply singleton_singleton.
      * rewrite Nat.sub_0_r.
        rewrite Nat.add_assoc.
        apply apply_new1_correct.
    + simpl.
      dependent destruction p1.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      unfold subst_pat. simpl.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        rewrite Nat.sub_0_r.
        replace (size_ctx Γ + 1)%nat with (size_octx (Valid (Γ ++ [Some Bit]))). 
          2: simpl; rewrite size_ctx_app; simpl; omega. 
        eapply IH.
        apply STAT. 
        eapply t0. 
        split. validate.
        rewrite merge_comm. 
        rewrite merge_singleton_append.
        easy.
        constructor; apply singleton_singleton.
      * rewrite Nat.sub_0_r.
        rewrite Nat.add_assoc.
        apply apply_new0_correct.
    + simpl.
      dependent destruction p1.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      unfold subst_pat. simpl.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        rewrite Nat.sub_0_r.
        replace (size_ctx Γ + 1)%nat with (size_octx (Valid (Γ ++ [Some Bit]))). 
          2: simpl; rewrite size_ctx_app; simpl; omega. 
        eapply IH.
        apply STAT. 
        eapply t0. 
        split. validate.
        rewrite merge_comm. 
        rewrite merge_singleton_append.
        easy.
        constructor; apply singleton_singleton.
      * rewrite Nat.sub_0_r.
        rewrite Nat.add_assoc.
        apply apply_new1_correct.
    + simpl.
      dependent destruction p1.
      simpl.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        rewrite Nat.add_sub.
        replace (size_ctx Γ) with (size_octx (Valid (update_at Γ v (Some Bit)))).
        Focus 2.
          simpl. 
          rewrite denote_index_update_some with (w := Qubit).
          reflexivity.
          eapply index_merge_l.
          apply pf1.
          destruct Γ1. invalid_contradiction. 
          apply singleton_index.
          inversion t. easy.
        eapply IH.
        apply STAT. 
        eapply t0. 
        split. validate.
        inversion t; subst.
        eapply update_at_merge; [apply H1| apply singleton_singleton| easy].
        constructor; apply singleton_singleton.
      * rewrite Nat.add_sub. 
        apply apply_meas_correct.
        apply Nat.lt_lt_add_l.
        destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; try invalid_contradiction.
        eapply subst_qubit_bounded; [apply t | apply pf1].
    + simpl.
      apply compose_super_correct.
      * rewrite Nat.add_sub.
        unfold denote_circuit in IH.
        eapply IH.
        apply STAT.
        eapply t0. apply pf1. apply t.
      * dependent destruction t. simpl.
        rewrite Nat.add_sub.
        apply apply_meas_correct.
        apply Nat.lt_lt_add_l.
        apply singleton_equiv in s; subst.
        destruct Γ2 as [|Γ2]; try invalid_contradiction.
        eapply subst_qubit_bounded; 
          [constructor; apply singleton_singleton| apply pf1].
    + simpl.        
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        rewrite Nat.add_0_r.
        dependent destruction t.
        apply singleton_equiv in s; subst.
        assert (M: Γ2 == ∅ ∙ Γ2).
          solve_merge. rewrite pf_merge in *. validate.
        specialize (t0 ∅ Γ2 unit M types_unit).
        destruct Γ2 as [|Γ2]; try invalid_contradiction.
        replace (size_ctx Γ - 1)%nat with (size_ctx (remove_pat (bit x) Γ)).
          2: erewrite remove_bit_pred; [easy|apply pf1].
        eapply IH.
        apply STAT.
        erewrite remove_bit_merge'; trivial.
        apply trim_types_circ. apply t0. 
        apply pf1.
      * unfold apply_to_first.
        dependent destruction p1.
        dependent destruction t.
        apply singleton_equiv in s; subst.
        unfold pat_to_list.
        simpl.
        unfold process_gate_state. simpl.
        unfold remove_pat. simpl.
        simpl.
        rewrite Nat.add_0_r.
        rewrite Nat.add_sub_assoc.
        apply apply_discard_correct.
        apply Nat.lt_lt_add_l.            
        destruct Γ2 as [|Γ2]; try invalid_contradiction.
        eapply subst_bit_bounded; [constructor; apply singleton_singleton|apply pf1].
        replace (size_ctx Γ) with (size_octx Γ) by easy.
        destruct pf1; rewrite pf_merge in *.        
        rewrite size_octx_merge by easy.
        simpl; rewrite singleton_size.
        omega.
    + simpl.        
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        rewrite Nat.add_0_r.
        dependent destruction t.
        apply singleton_equiv in s; subst.
        assert (M: Γ2 == ∅ ∙ Γ2). 
          solve_merge. rewrite pf_merge in *. validate.
        specialize (t0 ∅ Γ2 unit M types_unit).
        destruct Γ2 as [|Γ2]; try invalid_contradiction.
        replace (size_ctx Γ - 1)%nat with (size_ctx (remove_pat (qubit x) Γ)).
          2: erewrite remove_qubit_pred; [easy|apply pf1].
        eapply IH.
        apply STAT.
        erewrite remove_qubit_merge'; trivial.
        apply trim_types_circ. apply t0. 
        apply pf1.
      * unfold apply_to_first.
        dependent destruction p1.
        dependent destruction t.
        apply singleton_equiv in s; subst.
        unfold pat_to_list.
        simpl.
        unfold process_gate_state. simpl.
        unfold remove_pat. simpl.
        simpl.
        rewrite Nat.add_0_r.
        rewrite Nat.add_sub_assoc.
        apply apply_discard_correct.
        apply Nat.lt_lt_add_l.            
        destruct Γ2 as [|Γ2]; try invalid_contradiction.
        eapply subst_qubit_bounded; 
          [constructor; apply singleton_singleton|apply pf1].
        replace (size_ctx Γ) with (size_octx Γ) by easy.
        destruct pf1; rewrite pf_merge in *.        
        rewrite size_octx_merge by easy.
        simpl; rewrite singleton_size.
        omega.
    + simpl.        
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        rewrite Nat.add_0_r.
        dependent destruction t.
        apply singleton_equiv in s; subst.
        assert (M: Γ2 == ∅ ∙ Γ2). 
          solve_merge. rewrite pf_merge in *. validate.
        specialize (t0 ∅ Γ2 unit M types_unit).
        destruct Γ2 as [|Γ2]; try invalid_contradiction.
        replace (size_ctx Γ - 1)%nat with (size_ctx (remove_pat (qubit x) Γ)).
          2: erewrite remove_qubit_pred; [easy|apply pf1].
        eapply IH.
        apply STAT.
        erewrite remove_qubit_merge'; trivial.
        apply trim_types_circ. apply t0. 
        apply pf1.
      * unfold apply_to_first.
        dependent destruction p1.
        dependent destruction t.
        apply singleton_equiv in s; subst.
        unfold pat_to_list.
        simpl.
        unfold process_gate_state. simpl.
        unfold remove_pat. simpl.
        simpl.
        rewrite Nat.add_0_r.
        rewrite Nat.add_sub_assoc.
        apply apply_discard_correct.
        apply Nat.lt_lt_add_l.            
        destruct Γ2 as [|Γ2]; try invalid_contradiction.
        eapply subst_qubit_bounded; 
          [constructor; apply singleton_singleton|apply pf1].
        replace (size_ctx Γ) with (size_octx Γ) by easy.
        destruct pf1; rewrite pf_merge in *.        
        rewrite size_octx_merge by easy.
        simpl; rewrite singleton_size.
        omega.
  - (* Lifting is an interesting case since we are combining two subterms which are 
       not themselves mixed_states. To be precise, denote_db_circuit is being 
       apply to /partial mixed states/ and a predicate saying that circuits preserve
       partial-mixed-states and their traces. We leave this for future work. *)
    inversion STAT.
Qed.

Theorem denote_static_box_correct : forall W1 W2 (c : Box W1 W2),
  Static_Box c ->
  Typed_Box c ->
  WF_Superoperator (⟦c⟧).
Proof.
  intros W1 W2 c STAT WT.
  simpl.
  unfold denote_box.
  unfold denote_db_box.
  destruct c as [c'].
  inversion STAT; subst. clear STAT. rename H0 into STAT.
  unfold Typed_Box in WT. 
  simpl.
  destruct (add_fresh W1 []) as [p Γ] eqn:E.
  specialize (STAT p).
  specialize (WT Γ p).
  specialize (denote_static_circuit_correct W2 [] Γ (c' p) STAT) as WFC.
  unfold denote_circuit in WFC.
  simpl in WFC.
  rewrite (ctx_wtype_size W1 p Γ).
  apply WFC. 
  apply WT.  
  apply add_fresh_typed_empty. easy. 
  apply add_fresh_typed_empty. easy. 
Qed.
  
Fact denote_circuit_correct : forall W (Γ0 Γ : Ctx) (c : Circuit W),
  Γ ⊢ c:Circ -> 
  WF_Superoperator (⟨ Γ0 | Γ ⊩ c⟩).
Admitted.

Fact denote_box_correct : forall W1 W2 (c : Box W1 W2), 
  Typed_Box c -> WF_Superoperator (⟦c⟧).
Proof.
  intros W1 W2 c WT.
  simpl.
  unfold denote_box.
  unfold denote_db_box.
  destruct c as [c'].
  unfold Typed_Box in WT. 
  simpl.
  destruct (add_fresh W1 []) as [p Γ] eqn:E.
  specialize (WT Γ p).
  specialize (denote_circuit_correct W2 [] Γ (c' p)) as WFC.
  unfold denote_circuit in WFC.
  simpl in WFC.
  rewrite (ctx_wtype_size W1 p Γ).
  apply WFC. 
  apply WT.  
  apply add_fresh_typed_empty. easy. 
  apply add_fresh_typed_empty. easy. 
Qed.

(********************************************)
(* Lemmas regarding denotation with padding *)
(********************************************)

(* This needs updating, may not be needed: 
(* needs defining *)
Parameter decr_circuit_once : forall {W}, Circuit W -> Circuit W.

Fixpoint decr_circuit {W} (n : nat) (c : Circuit W) : Circuit W :=
  match n with 
  | 0 => c
  | S n' => decr_circuit n' (decr_circuit_once c)
  end. 

Fixpoint decr_pat_once {W} (p : Pat W) :=
  match p with 
  | unit => unit 
  | qubit v => qubit (v-1)%nat 
  | bit v => bit (v-1)%nat
  | pair p1 p2 => pair (decr_pat_once p1) (decr_pat_once p2)
  end.

Proposition decr_pat_once_qubit : forall n Γ, 
    decr_pat_once (add_fresh_pat (NTensor n Qubit) (Some Qubit :: Γ))
    = add_fresh_pat (NTensor n Qubit) Γ.
Proof.
  induction n; intros; trivial.
  simpl. unfold add_fresh_pat, add_fresh_state. simpl. rewrite IHn. rewrite Nat.sub_0_r. easy.
Abort.

Proposition decr_circuit_pat : forall W1 W2 (c : Box W1 W2) (p : Pat W1), 
    decr_circuit_once (unbox c p) = unbox c (decr_pat_once p).
Abort.

Proposition denote_db_pad_left : forall (Γ0 Γ : Ctx) pad n W (c : Circuit W) 
  (ρ1 : Square (2^pad)) (ρ2 : Square (2^n)), 
  ⟦Γ0⟧ = pad ->
  ⟦Γ⟧ = n ->  
  ⟨Γ0 | Valid (repeat None pad ++ Γ) ⊩ c ⟩ (ρ1 ⊗ ρ2) = 
  ρ1 ⊗ (⟨ ∅ | Γ ⊩ decr_circuit pad c ⟩ ρ2).
Abort.

Proposition denote_db_pad_right : forall (Γ0 Γ : OCtx) pad n w (c : Circuit w) (ρ1 : Square (2^n)) (ρ2 : Square (2^pad)),
  ⟦Γ0⟧ = pad ->
  ⟦Γ⟧ = n ->
  ⟨ Γ0 | Γ ⊩ c ⟩ (ρ1 ⊗ ρ2) = ⟨ ∅ | Γ ⊩ c ⟩ ρ1 ⊗ ρ2.
Abort.
*)

(*********************************************************)
(* Equivalence of circuits according to their denotation *)
(*********************************************************)

(* Now for both version of the semantics *)
Definition HOAS_Equiv {W1 W2} (c1 c2 : Box W1 W2) :=
  forall ρ b, Mixed_State ρ -> denote_box b c1 ρ = denote_box b c2 ρ .

Locate "≡".
Notation "a ≡ b" := (HOAS_Equiv a b) (at level 70) : circ_scope.

Hint Unfold HOAS_Equiv : den_db.
    
Open Scope circ_scope.

Lemma inSeq_id_l : forall w1 w2 (c : Box w1 w2),
    id_circ · c = c.
Proof.
  destruct c. unfold inSeq. simpl.
  apply f_equal.
  apply functional_extensionality; intros p.
  remember (c p) as c0. clear c p Heqc0.
  induction c0; auto.
  * simpl. apply f_equal. apply functional_extensionality; intros p'.
    apply H.
  * simpl. apply f_equal. apply functional_extensionality; intros p'.
    apply H.
Qed.


Lemma inSeq_id_r : forall w1 w2 (c : Box w1 w2),
    c · id_circ = c.
Proof.
  destruct c.
  unfold inSeq.
  simpl.
  reflexivity.
Qed.

Lemma HOAS_Equiv_refl : forall w1 w2 (c : Box w1 w2), c ≡ c.
Proof. intros w1 w2 c ρ b. auto.
Qed.
Lemma HOAS_Equiv_sym : forall w1 w2 (c1 c2: Box w1 w2), (c1 ≡ c2) -> c2 ≡ c1.
Proof.
  intros. intros ρ b H'. rewrite H; auto.
Qed.
Lemma HOAS_Equiv_trans : forall w1 w2 (c1 c2 c3 : Box w1 w2), 
  (c1 ≡ c2) -> (c2 ≡ c3) -> c1 ≡ c3.
Proof.
  intros. intros ρ b Hρ. rewrite H; auto.
Qed.

Lemma inSeq_assoc : forall {w1 w2 w3 w4} (c1 : Box w1 w2) (c2 : Box w2 w3) (c3 : Box w3 w4), c3 · (c2 · c1) = (c3 · c2) · c1.
Proof.
  intros w1 w2 w3 w4 [c1] [c2] [c3]. unfold inSeq. simpl.
  apply f_equal; apply functional_extensionality; intros p1.
  simpl.
  remember (c1 p1) as c. clear c1 p1 Heqc.
  dependent induction c.
  - reflexivity.
  - simpl. apply f_equal; apply functional_extensionality; intros p2.
    rewrite H.
    reflexivity.
  - simpl. apply f_equal; apply functional_extensionality; intros p2.
    rewrite H.
    reflexivity.
Qed.

Require Import Setoid.
Require Import Relation_Definitions.

Add Parametric Relation W1 W2 : (Box W1 W2) (@HOAS_Equiv W1 W2)
       reflexivity proved by (HOAS_Equiv_refl W1 W2)
       symmetry proved by (HOAS_Equiv_sym W1 W2)
       transitivity proved by (HOAS_Equiv_trans W1 W2)
       as eq_set_rel.



(************************)
(* Hints for automation *)
(************************)

(* add_fresh *)
Hint Unfold get_fresh add_fresh_state add_fresh_pat process_gate process_gate_state : den_db.

Hint Unfold apply_new0 apply_new1 apply_U apply_qubit_unitary denote_ctrls apply_meas apply_discard apply_assert0 apply_assert1 compose_super Splus swap_list swap_two pad denote_box denote_pat super: den_db.

(* add_fresh *)
Hint Unfold get_fresh add_fresh_state add_fresh_pat process_gate process_gate_state : vector_den_db.

Hint Unfold apply_new0 apply_new1 apply_U apply_qubit_unitary denote_ctrls apply_meas apply_discard apply_assert0 apply_assert1 compose_super Splus swap_list swap_two pad denote_box denote_pat : vector_den_db.

Ltac vector_denote :=
  intros; 
  repeat (autounfold with vector_den_db; simpl);
  repeat rewrite <- bool_to_ket_matrix_eq;
  repeat replace (|0⟩⟨0|) with (outer_product |0⟩) by reflexivity;
  repeat replace (|1⟩⟨1|) with (outer_product |1⟩) by reflexivity;
  repeat rewrite outer_product_kron;
  repeat rewrite super_outer_product;
  apply outer_product_eq.

Ltac matrix_denote :=
  intros; repeat (autounfold with den_db; simpl).

Hint Rewrite subst_pat_fresh_empty : proof_db.
Hint Rewrite size_fresh_ctx using validate : proof_db.
(* add some arithmetic *)
Hint Rewrite Nat.leb_refl : proof_db.
Hint Rewrite denote_pat_fresh_id : proof_db.
Hint Rewrite swap_fresh_seq : proof_db.
(* Hint Rewrite apply_U_σ pad_nothing using auto : proof_db. *)


