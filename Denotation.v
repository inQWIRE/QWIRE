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

Lemma swap_list_spec_1 : forall n i j (A1 : Square (2^i)%nat) (A2 : Square (2^j)%nat)
  (U : Square (2^1)%nat) (ρ : Square (2^1)%nat), (i + j + 1 = n)%nat ->
  super (swap_list n [i] × pad n U × (swap_list n [i])†) (A1 ⊗ ρ ⊗ A2) = 
  A1 ⊗ (super U ρ) ⊗ A2.
Admitted.

Lemma swap_list_spec_2 : forall n i j k 
  (A1 : Square (2^i)%nat) (A2 : Square (2^j)%nat) (A3 : Square (2^k)%nat)   
  (U : Square (2^2)%nat) (ρ1 ρ2 ρ1' ρ2': Square (2^1)%nat), (i + j + k + 2 = n)%nat ->
  (super U (ρ1 ⊗ ρ2)) = ρ1' ⊗ ρ2' -> 
  super (swap_list n [i; (i+j+1)%nat] × pad n U × (swap_list n [i; (i+j+1)%nat])†) 
    (A1 ⊗ ρ1 ⊗ A2 ⊗ ρ2 ⊗ A3) = A1 ⊗ ρ1' ⊗ A2 ⊗ ρ2' ⊗ A3.
Admitted.

(*
Lemma swap_list_shift : forall n (ρ : Square (2^1)%nat) (A : Square (2^n)),
  super (swap_list (S n) (seq 1 n ++ [O])) (ρ ⊗ A) = A ⊗ ρ.
Admitted.

Lemma swap_list_shift' : forall (n : nat) (ρ : Square 2) (A : Square (2^n)%nat),
  super (swap_list (S n) (n :: seq 0 n)) (A ⊗ ρ) = ρ ⊗ A.
Admitted.
*)

(*** Applying Unitaries to Sytems ***)

Definition super_Zero {m n} : Superoperator m n  :=
  fun _ => Zero n n.

Definition apply_to_first {m n} (f : nat -> Superoperator m n) (l : list nat) :
  Superoperator m n :=
  match l with
  | x :: _ => f x 
  | []     => super_Zero
  end.

Fixpoint ctrls_to_list {W} (lb : list bool) (l : list nat) (g : Unitary W) {struct g}: 
  (nat * list bool * Square 2) :=
  match g with
  | ctrl g'     => match l with 
                  | n :: l' => let (res,u) := ctrls_to_list lb l' g' in
                              let (k,lb') := res in
                              (k,update_at lb' n true, u)  
                  | _       => (O,[],Zero 2 2)
                  end
  | bit_ctrl g' => match l with 
                  | n :: l' => let (res,u) := ctrls_to_list lb l' g' in
                              let (k,lb') := res in
                              (k,update_at lb' n true, u)  
                  | _       => (O,[],Zero 2 2)
                  end
  | u           => match l with
                  | k :: l' => (k,lb,⟦u⟧)
                  | _       => (O,[],Zero 2 2)
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

Lemma apply_meas_correct : forall n k, (k < n)%nat ->
    WF_Superoperator (@apply_meas n k). 
Proof.
  intros n k L ρ Mρ.
  unfold apply_meas.
  unfold Splus, super.
  Msimpl.
Admitted.
  
Lemma apply_discard_correct : forall n k, (k < n)%nat ->
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

(* here, the state represents the number of qubits in a system. *)
Instance nat_gate_state : Gate_State nat :=
  { get_fresh := fun _ n => (n,S n)
  ; remove_var := fun _ n => (n-1)%nat
  ; change_type := fun _ _ n => n
  ; maps_to := fun _ _ => None
  }.

(* Rewrote lift to remove the bit in-place. Not sure if the corresponding variable
   is being removed from the context, though *)
Fixpoint denote_db_circuit {w} safe padding input (c : DeBruijn_Circuit w)
                         : Superoperator (2^(padding+input)) (2^(padding+⟦w⟧)) :=
  match c with
  | db_output p    => super (pad (padding+input) (⟦p⟧))
  | db_gate g p c' => let input' := process_gate_state g p input in
                      compose_super (denote_db_circuit safe padding input' c')
                                    (apply_gate safe g (pat_to_list p))
  | db_lift p c'   => let k := get_var p in 
                     Splus  (compose_super 
                               (denote_db_circuit safe padding (input-1) (c' false))
                               (super ('I_(2^k) ⊗ ⟨0| ⊗ 'I_(2^(input-k-1)))))
                             (compose_super 
                                (denote_db_circuit safe padding (input-1) (c' true))
                                (super ('I_(2^k) ⊗ ⟨1| ⊗ 'I_(2^(input-k-1)))))
  end.


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
  = super (pad (⟦Γ0⟧ + ⟦Γ⟧) (denote_pat (subst_pat (octx_dom Γ) p))).
Proof.
  intros.
  simpl.
  unfold hoas_to_db_pat.
  reflexivity.
Qed.


Ltac fold_denotation :=
  repeat match goal with
  | [ |- context[ size_octx ?Γ ] ] => replace (size_octx Γ) with (⟦Γ⟧); auto
  end.

Lemma size_wtype_length : forall {w} (p : Pat w),
    length (pat_to_list p) = size_wtype w.
Proof.
  induction p; simpl; auto.
  rewrite app_length.
  rewrite IHp1, IHp2.
  auto.
Qed.

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

Lemma hoas_to_db_pat_fresh : forall w Γ w',
      Γ = fresh_state w' ∅ ->
      hoas_to_db_pat (fresh_state w Γ) (fresh_pat w Γ) 
    = fresh_pat w (octx_dom Γ).
Proof.
  induction w; intros; 
    (assert (is_valid Γ) by (subst; apply is_valid_fresh; validate));
    (destruct Γ as [ | Γ]; [invalid_contradiction | ]);
    unfold hoas_to_db_pat in *; simpl in *; auto.

  * rewrite ctx_dom_app; simpl.
    unfold subst_var.
    rewrite Nat.add_0_r.
    admit (* maps_to (length Γ) (Ctx_dom Γ ++ [length Γ]) = length Γ *).
  * admit (* same as above *).

  * f_equal.
    +admit. (* more general lemma *)
    + rewrite IHw2 with (w' := Tensor w' w1).
      - f_equal. 
        rewrite octx_dom_fresh; auto.
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

Lemma Singleton_size : forall x w Γ, SingletonCtx x w Γ -> ⟦Γ⟧ = 1%nat.
Proof.
  induction 1; auto.
Qed.

Lemma singleton_size : forall x w,
      size_ctx (singleton x w) = 1%nat.
Proof.
  intros. simpl. eapply Singleton_size. apply singleton_singleton.
Qed.

Lemma size_octx_fresh : forall (W : WType) (Γ : OCtx),
      is_valid Γ ->
      ⟦fresh_state W Γ⟧ = (⟦Γ⟧ + ⟦W⟧)%nat.
Proof.
  induction W; intros;
    (destruct Γ as [ | Γ]; [invalid_contradiction | ]).
  * simpl. rewrite size_ctx_app; easy. 
  * simpl. rewrite size_ctx_app; easy. 
  * simpl; omega.
  * simpl.
    rewrite IHW2 by (apply is_valid_fresh; easy).
    rewrite IHW1 by easy.
    simpl; omega. 
Qed.


(* probably a more general form of this *)
Lemma denote_db_unbox : forall {w1 w2} (b : Box w1 w2),
    ⟦b⟧ = ⟨ ∅ | fresh_state w1 ∅ ⊩ unbox b (fresh_pat w1 ∅) ⟩.
Proof.
  destruct b.
  simpl. unfold denote_box.
  unfold denote_circuit.
  simpl. 
  rewrite size_octx_fresh; [ | validate].
  easy.
Qed.
  
Lemma types_pat_size : forall w (p : Pat w) (Γ : OCtx),
      Types_Pat Γ p -> ⟦w⟧ = ⟦Γ⟧.
Proof.
  induction 1; simpl; auto.
  * apply Singleton_size in s. simpl in *. omega.
  * apply Singleton_size in s. simpl in *. omega.
  * subst.
    rewrite size_octx_merge; auto.
Qed.

Lemma denote_index_update : forall (Γ : Ctx) x w w',
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
    rewrite trim_empty; trivial.
    eapply update_none_singleton. apply s.
  - unfold remove_pat. simpl.
    rewrite trim_empty; trivial.
    eapply update_none_singleton. apply s.
  - unfold remove_pat. simpl.
(* true, but I shouldn't care about compound singletons *)
Abort.    
   
Lemma size_empty_ctx : forall Γ,
    empty_ctx Γ ->
    size_ctx Γ = 0%nat.
Proof.
  induction 1; auto.
Qed.

(* This doesn't seem to be true in the case where Γ is invalid and w1 is One. *)
(* Discuss with Jennifer *)
Lemma process_gate_ctx_size : forall w1 w2 (g : Gate w1 w2) p (Γ : OCtx),
      (⟦w1⟧ <= ⟦Γ⟧)%nat ->
      ⟦process_gate_state g p Γ⟧ = (⟦Γ⟧ + ⟦w2⟧ - ⟦w1⟧)%nat.
Proof.
  destruct g; intros p Γ H;
    try (simpl; rewrite Nat.add_sub; auto; fail);
    try (simpl; rewrite ctx_size_app; simpl; omega).
(*
  * simpl. rewrite Nat.sub_0_r. destruct Γ. simpl in *. omega. simpl. auto.

  * simpl. rewrite Nat.add_sub. auto.
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
*)
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

Lemma process_gate_denote : forall {w1 w2} (g : Gate w1 w2) (p : Pat w1) Γ Γ1 Γ2,
    Γ == Γ1 ∙ Γ2 ->
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
  simpl. fold_denotation.
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
  simpl; fold_denotation.
  replace (process_gate g p1 Γ) with 
      (process_gate_pat g p1 Γ, process_gate_state g p1 Γ) by 
      (symmetry; apply surjective_pairing).
  simpl; fold_denotation.
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
  simpl; fold_denotation.
  replace (process_gate g p1 Γ) with 
      (process_gate_pat g p1 Γ, process_gate_state g p1 Γ) by 
      (symmetry; apply surjective_pairing).
  simpl; fold_denotation.
  set (p1' := hoas_to_db_pat Γ p1).
  set (p2 := process_gate_pat g p1 Γ).    
  rewrite (process_gate_nat _ p1' p1).
  rewrite (process_gate_denote _ _ Γ Γ1 Γ2) by assumption.   
  reflexivity.
Qed.

(* True for unsafe denote as well? *)
(*
Lemma denote_compose : forall w (c : Circuit w) Γ, Γ ⊢ c :Circ ->
     forall w' (f : Pat w -> Circuit w') (Γ0 Γ1 Γ1' : OCtx),
  Γ1 ⊢ f :Fun ->
  Γ1' == Γ1 ∙ Γ ->
      ⟨ Γ0 | Γ1' ⊩ compose c f ⟩ 
    = compose_super (⟨Γ0 | fresh_state w Γ1 ⊩ f (fresh_pat w Γ1)⟩)
                    (⟨Γ0 ⋓ Γ1 | Γ ⊩ c⟩). 
*)
Lemma denote_compose : forall safe w (c : Circuit w) Γ, Γ ⊢ c :Circ ->
     forall w' (f : Pat w -> Circuit w') (Γ0 Γ1 Γ1' : OCtx),
  Γ1 ⊢ f :Fun ->
  Γ1' == Γ1 ∙ Γ ->
      denote_circuit safe (compose c f) Γ0 Γ1'
    = compose_super (denote_circuit safe (f (fresh_pat w Γ1)) Γ0 (fresh_state w Γ1)) 
                    (denote_circuit safe c (Γ0 ⋓ Γ1) Γ). 
Proof.
  induction 1; intros w' h Γ0 Γ3 Γ3' wf_f pf_merge.
  * simpl; fold_denotation.
    admit. (* property about f being parametric *)
    (* ⟨ Γ0 | Γ1 ⋓ Γ2 ⊩ f p ⟩
    =  ⟨ Γ0 | fresh_state Γ2 ⊩ f (fresh_pat w Γ2) ⟩ ∘ ⟨ Γ1 ⊩ p ⟩ 
    *)
  * replace (compose (gate g p1 f) h) 
      with (gate g p1 (fun p2 => compose (f p2) h)) 
      by auto.
    repeat rewrite denote_gate_circuit; fold_denotation.


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

Lemma swap_list_unitary : forall n l, WF_Unitary (swap_list n l).
Proof.
  intros n l.
  unfold swap_list.
  induction n.
  - simpl.
    apply id_unitary.
  - 
Admitted.



(* For Contexts.v - also reqs. moving Singleton_size *)
Lemma ctx_wtype_size : forall Γ W (p : Pat W), Γ ⊢ p :Pat -> ⟦Γ⟧ = ⟦W⟧. 
Proof.
  intros Γ W p H.
  induction H; trivial.
  - apply Singleton_size in s.
    simpl in *. apply s.
  - apply Singleton_size in s.
    simpl in *. apply s.
  - simpl in *.
    rewrite e in *.
    rewrite size_octx_merge; auto.
Qed.

Lemma merge_singleton_append : forall W (Γ : Ctx), 
        Γ ⋓ (singleton (length Γ) W) = Valid (Γ ++ [Some W]). 
Proof. 
  induction Γ.
  - simpl. reflexivity. 
  - unlock_merge. simpl in *.
    destruct a; simpl; rewrite IHΓ; reflexivity.
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

Lemma lookup_maybe_ctx_dom : forall v Γ Γv Γo W,
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
Qed.

Lemma subst_qubit_bounded : forall v Γ Γv Γo,
                            Γv ⊢ (qubit v) :Pat ->
                            Γ == Γv ∙ Γo ->
                            (subst_var (octx_dom Γ) v < size_octx Γ)%nat.
Proof.
  induction v; intros Γ Γv Γo TP M.
  - inversion TP; subst.
    apply singleton_equiv in H1.
    rewrite H1 in M.
    apply merge_fun_ind in M.
    inversion M; subst.
    simpl.
    rewrite subst_var_singleton_list. omega.
    simpl.
    inversion H2; subst.
    unfold subst_var. simpl. omega.
  - inversion TP; subst.
    apply singleton_equiv in H1.
    rewrite H1 in M.
    apply merge_fun_ind in M.
    inversion M; subst.
    + simpl.
      erewrite singleton_dom by apply singleton_singleton. 
      simpl.
      rewrite subst_var_singleton_list.
      rewrite singleton_size.
      omega.
    + assert (TP': singleton v Qubit ⊢ qubit v :Pat).
        constructor. apply singleton_singleton.
      apply merge_ind_fun in H5.
      specialize (IHv _ _ _ TP' H5).
      destruct o; simpl in *.      
      * replace (subst_var (O :: list_fmap S (ctx_dom Γ3)) (S v)) with 
            (S (subst_var (ctx_dom Γ3) v)).
        omega.
        unfold subst_var.
        Search maps_to.
        unfold maps_to. simpl.
        rewrite lookup_maybe_S.
        destruct (lookup_maybe v (ctx_dom Γ3)) eqn:E.
        simpl.
        easy.
        simpl.
        contradict E.
        eapply (lookup_maybe_ctx_dom v Γ3).
        apply H5.
        constructor. apply singleton_singleton.
      * unfold subst_var in *.
        unfold maps_to in *. simpl in *.
        rewrite lookup_maybe_S.
        apply IHv.
Qed.

Lemma subst_bit_bounded : forall v Γ Γv Γo,
                            Γv ⊢ (bit v) :Pat ->
                            Γ == Γv ∙ Γo ->
                            (subst_var (octx_dom Γ) v < size_octx Γ)%nat.
Proof.
  induction v; intros Γ Γv Γo TP M.
  - inversion TP; subst.
    apply singleton_equiv in H1.
    rewrite H1 in M.
    apply merge_fun_ind in M.
    inversion M; subst.
    simpl.
    rewrite subst_var_singleton_list. omega.
    simpl.
    inversion H2; subst.
    unfold subst_var. simpl. omega.
  - inversion TP; subst.
    apply singleton_equiv in H1.
    rewrite H1 in M.
    apply merge_fun_ind in M.
    inversion M; subst.
    + simpl.
      erewrite singleton_dom by apply singleton_singleton. 
      simpl.
      rewrite subst_var_singleton_list.
      rewrite singleton_size.
      omega.
    + assert (TP': singleton v Bit ⊢ bit v :Pat).
        constructor. apply singleton_singleton.
      apply merge_ind_fun in H5.
      specialize (IHv _ _ _ TP' H5).
      destruct o; simpl in *.      
      * replace (subst_var (O :: list_fmap S (ctx_dom Γ3)) (S v)) with 
            (S (subst_var (ctx_dom Γ3) v)).
        omega.
        unfold subst_var.
        Search maps_to.
        unfold maps_to. simpl.
        rewrite lookup_maybe_S.
        destruct (lookup_maybe v (ctx_dom Γ3)) eqn:E.
        simpl.
        easy.
        simpl.
        contradict E.
        eapply (lookup_maybe_ctx_dom v Γ3).
        apply H5.
        constructor. apply singleton_singleton.
      * unfold subst_var in *.
        unfold maps_to in *. simpl in *.
        rewrite lookup_maybe_S.
        apply IHv.
Qed.


Lemma pat_to_list_bounded : forall W Γ Γp Γo (p : Pat W) x, 
                            Γ == Γp ∙ Γo ->
                            Γp ⊢ p:Pat ->
                            In x (pat_to_list (subst_pat (octx_dom Γ) p)) ->
                            (x < size_octx Γ)%nat.
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
      rewrite <- merge_assoc in pf_merge.
      eapply IHp1; trivial.
      split; trivial. apply pf_merge. easy.
    + dependent destruction TP.
      destruct M.
      rewrite (merge_comm Γ1) in pf_merge.
      rewrite <- merge_assoc in pf_merge.
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
    rewrite (trim_merge Γ Γ1 Γ2).
    reflexivity.
    split; easy.
    simpl in H1.
    inversion H1.
    repeat rewrite H3.
    easy.
Qed.

Lemma remove_bit_merge' : forall (Γ Γ' : Ctx) v, Γ' == singleton v Bit ∙ Γ ->
                                            remove_pat (bit v)  Γ' = trim Γ.
Proof.      
  intros Γ Γ' v H.
  apply merge_fun_ind in H.
  dependent induction H.
  - destruct v; inversion x.
  - induction v.
    + simpl. unfold remove_pat. simpl. easy.
    + simpl. 
      unfold remove_pat in *.
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
     unfold remove_pat in *.
     simpl in *.
     erewrite IHmerge_ind; easy.
     replace (remove_pat (bit (S v)) (Some w :: Γ0)) with
        (Some w :: remove_pat (bit v) (Γ0)) by easy.
     simpl.
     erewrite IHmerge_ind; easy.
Qed.     

Lemma remove_bit_merge : forall (Γ Γ' : OCtx) W (p : Pat W) v, 
  Γ ⊢ p:Pat ->
  Γ' == singleton v Bit ∙ Γ ->
  remove_pat (bit v)  Γ' = Γ.
Proof.
  intros Γ Γ' W p v H H0.
  destruct Γ' as [|Γ'], Γ as [|Γ]; try invalid_contradiction.
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
      unfold remove_pat in *.
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
     unfold remove_pat in *.
     simpl in *.
     erewrite IHmerge_ind; easy.
     replace (remove_pat (qubit (S v)) (Some w :: Γ0)) with
        (Some w :: remove_pat (qubit v) (Γ0)) by easy.
     simpl.
     erewrite IHmerge_ind; easy.
Qed.     

Lemma remove_qubit_merge : forall (Γ Γ' : OCtx) W (p : Pat W) v, 
  Γ ⊢ p:Pat ->
  Γ' == singleton v Qubit ∙ Γ ->
  remove_pat (qubit v)  Γ' = Γ.
Proof.
  intros Γ Γ' W p v H H0.
  destruct Γ' as [|Γ'], Γ as [|Γ]; try invalid_contradiction.
  erewrite <- (types_pat_no_trail Γ) by apply H.
  simpl.
  assert (remove_pat (bit v) Γ' = trim Γ).
  apply remove_qubit_merge'; easy.
  inversion H1.  
  easy.
Qed.

Lemma remove_bit_pred : forall Γ Γ' v, Γ' == (singleton v Bit) ∙ Γ ->
                        size_octx (remove_pat (bit v) Γ') = (size_octx Γ' - 1)%nat.
Proof.
  intros Γ Γ' v H.
  destruct Γ as [|Γ], Γ' as [|Γ']; try invalid_contradiction.
  replace (size_octx (remove_pat (bit v) (Valid Γ'))) with
    (size_ctx (remove_pat (bit v) Γ')) by easy.
  rewrite (remove_bit_merge' Γ Γ'); trivial.
  destruct H. rewrite pf_merge in *. rewrite size_octx_merge by easy. 
  simpl. rewrite singleton_size. 
  rewrite size_ctx_trim.
  omega.
Qed.

Lemma remove_qubit_pred : forall Γ Γ' v, Γ' == (singleton v Qubit) ∙ Γ ->
                        size_octx (remove_pat (qubit v) Γ') = (size_octx Γ' - 1)%nat.
Proof.
  intros Γ Γ' v H.
  destruct Γ as [|Γ], Γ' as [|Γ']; try invalid_contradiction.
  replace (size_octx (remove_pat (qubit v) (Valid Γ'))) with
    (size_ctx (remove_pat (qubit v) Γ')) by easy.
  rewrite (remove_qubit_merge' Γ Γ'); trivial.
  destruct H. rewrite pf_merge in *. rewrite size_octx_merge by easy. 
  simpl. rewrite singleton_size. 
  rewrite size_ctx_trim.
  omega.
Qed.

Lemma remove_pat_valid : forall W Γ (p : Pat W), is_valid Γ -> is_valid (remove_pat p Γ).
Proof.
  intros W Γ p H.
  change(exists Γ', (remove_pat p Γ) = Valid Γ').  
  destruct Γ as [|Γ].
  apply not_valid in H. contradiction.
  clear H.
  generalize dependent Γ.
  induction p.
  - unfold remove_pat. simpl. eauto.
  - unfold remove_pat. simpl. eauto.
  - unfold remove_pat. simpl. eauto.
  - intros. 
    unfold remove_pat in *.
    simpl.
    rewrite fold_left_app.
    edestruct IHp1 as [Γ1 H1]. rewrite H1.
    apply IHp2.
Qed.

(* From ancilla.v. Broken by change to remove_bit_merge 
Lemma remove_bit_pred : forall Γ Γ' v, Γ' == (singleton v Bit) ∙ Γ ->
                        size_octx (remove_pat (bit v) Γ') = (size_octx Γ' - 1)%nat.
Proof.
  intros Γ Γ' v H.
  remember H as H'. clear HeqH'. apply remove_bit_merge in H'.
  destruct H. rewrite pf_merge in *. rewrite size_octx_merge by easy. 
  erewrite remove_bit_merge.
  2: constructor; trivial.
  unfold size_octx at 2. rewrite singleton_size. omega.
Qed.
*)

Lemma types_circ_no_trail : forall (Γ : Ctx) W (c : Circuit W), 
            Γ ⊢ c:Circ ->
            trim Γ = Γ.
Proof.
  intros Γ W c WT.
  dependent induction WT; subst.
  - eapply types_pat_no_trail. apply t.
  - destruct Γ0 as [|Γ0]. invalid_contradiction.
    destruct (mk_typed_pat Γ0 w2) as [Γ2 p2] eqn:E.
    symmetry in E.
    specialize (typed_pat_merge_valid _ _ _ _ E) as V.
    destruct V as [Γ2' M].
    assert (T2 : trim Γ2' = Γ2'). 
      eapply H; trivial.
      split. validate. rewrite <- M. monoid.
      eapply typed_pat_typed. apply E.
    clear H.
    destruct Γ1 as [|Γ1]. invalid_contradiction.
    apply types_pat_no_trail in t.
    destruct pf1. 
    apply ctx_octx.
    replace (Valid (trim Γ)) with (otrim Γ) by easy.
    rewrite pf_merge.
    rewrite <- t at 2.
    apply typed_pat_typed in E.
    apply types_pat_no_trail in E.
    (* But what if Γ0 has trailing Nones, and Γ1 < Γ0 < Γ2? *)
Abort.

(* Γ should type the input pattern *)
Lemma types_fun_types_pat : forall W W' Γ (f : Pat W' -> Circuit W), 
            Γ ⊢ f:Fun ->
            {W' : WType & {p : Pat W' & Γ ⊢ p:Pat}}.
Abort.

Lemma types_circ_types_pat : forall W Γ (c : Circuit W), 
            Γ ⊢ c:Circ ->
            {W' : WType & {p : Pat W' & Γ ⊢ p:Pat}}.
Proof.
  intros W Γ c WT.
  induction WT; subst.
  - exists w, p. easy.
  - (* Γ2 is the union. How can we break it into components? *)
    destruct Γ as [|Γ]. invalid_contradiction.
    destruct (mk_typed_pat Γ w2) as [Γ2 p2] eqn:E.
    symmetry in E.
    specialize (typed_pat_merge_valid _ _ _ _ E) as V.
    specialize (H Γ2 (Γ2 ⋓ Γ) p2).
    destruct H as [w' [p' TP']].
    split; trivial. validate. 
    eapply typed_pat_typed. apply E.
Admitted.

Inductive Static_Circuit {W} : Circuit W -> Prop := 
| S_output : forall p, Static_Circuit (output p)
| S_gate :   forall w1 w2 (g : Gate w1 w2) (p : Pat w1) (c' : Pat w2 -> Circuit W),
               (forall p2, Static_Circuit (c' p2)) ->
               Static_Circuit (gate g p c').

Theorem denote_static_circuit_correct : forall W Γ0 Γ (c : Circuit W),
  Static_Circuit c ->
  Γ ⊢ c:Circ -> 
  WF_Superoperator (⟨ Γ0 | Γ ⊩ c⟩).
Proof.
  intros W Γ0 Γ c STAT WT.
  induction WT.
  - unfold denote_circuit. simpl.
    unfold denote_pat.
    unfold pad.
    subst.
    simpl_rewrite (ctx_wtype_size Γ' w p t).
    apply super_unitary_correct.
    rewrite Nat.add_sub.
    match goal with
    | [|- WF_Unitary (?A ⊗ ?B)] => specialize (kron_unitary A B) as KU
    end.
    unify_pows_two.
    replace (2 ^ (size_octx Γ0 + size_wtype w))%nat 
      with (2 ^ ⟦ w ⟧ * 2 ^ size_octx Γ0)%nat by (simpl; unify_pows_two). 
    apply KU.
    apply swap_list_unitary.
    apply id_unitary.
  - dependent destruction STAT. 
    rename H into STAT. rename H0 into IH.
    unfold denote_circuit; simpl.
    destruct g.
    + simpl.
      destruct pf1.
      rewrite pf_merge in *.
      rewrite size_octx_merge by easy.
      simpl_rewrite (ctx_wtype_size Γ1 W p1 t).
      rewrite leb_correct by omega.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        replace (size_wtype W) with (⟦W⟧) by easy.
        rewrite <- (ctx_wtype_size Γ1 W p1 t).
        rewrite <- size_octx_merge by easy.
        apply (IH Γ1); trivial. 
        split; easy.
      * apply apply_U_correct.
        rewrite size_wtype_length.
        reflexivity.
        unfold hoas_to_db_pat.
        replace (size_wtype W) with (⟦W⟧) by easy.
        rewrite <- (ctx_wtype_size Γ1 W p1 t).
        rewrite <- size_octx_merge by easy.
        apply forallb_forall.
        intros x IN.
        specialize Nat.ltb_lt as [L R]. rewrite R. easy. clear L R.
        apply Nat.lt_lt_add_l.
        eapply pat_to_list_bounded.
        split; easy.
        apply t. 
        apply IN.
    + simpl.
      destruct pf1.
      rewrite pf_merge in *.
      rewrite size_octx_merge by easy.
      simpl_rewrite (ctx_wtype_size Γ1 Bit p1 t).
      simpl.
      rewrite Nat.add_succ_r.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        replace (S (size_octx Γ)) with (size_octx Γ1').
        Focus 2. rewrite pf_merge. rewrite size_octx_merge by easy.
          dependent destruction t. apply singleton_equiv in s. subst.
          simpl. rewrite singleton_size. easy.
        rewrite pf_merge.
        apply (IH Γ1); trivial.
        split; easy.
      * specialize (apply_U_correct Qubit) as AUC.
        simpl in AUC.
        unfold process_gate_state. simpl.
        unify_pows_two.
        rewrite Nat.add_1_r. rewrite Nat.add_succ_r.
        apply AUC with (U := _X).
        rewrite size_wtype_length.
        reflexivity.
        unfold hoas_to_db_pat.
        apply forallb_forall.
        intros x IN.
        specialize Nat.ltb_lt as [L R]. rewrite R. easy. clear L R.
        assert (L : (x < size_octx (Γ1 ⋓ Γ))%nat).
        eapply pat_to_list_bounded.
        split; trivial. apply t. easy. 
        rewrite size_octx_merge in L; trivial.
        dependent destruction t. 
        apply singleton_equiv in s. subst.
        simpl in L. rewrite singleton_size in L.
        omega.
    + simpl.
      dependent destruction p1.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      destruct Γ as [|Γ]. invalid_contradiction.
      unfold hoas_to_db_pat. simpl.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        replace (S (size_ctx Γ)) with (size_octx (Valid (Γ ++ [Some Qubit]))). 
          2: simpl; rewrite size_ctx_app; simpl; omega. 
        eapply IH; [|constructor; apply singleton_singleton | easy].
        split. validate.
        rewrite merge_comm. 
        rewrite merge_singleton_append.
        easy.
      * unfold process_gate_state.
        simpl.
        rewrite Nat.add_succ_r.
        rewrite <- (Nat.add_1_r (size_octx Γ0 + size_ctx Γ)).
        apply apply_new0_correct.
    + simpl.
      dependent destruction p1.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      destruct Γ as [|Γ]. invalid_contradiction.
      unfold hoas_to_db_pat. simpl.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        replace (S (size_ctx Γ)) with (size_octx (Valid (Γ ++ [Some Qubit]))).
          2: simpl; rewrite size_ctx_app; simpl; omega. 
        eapply IH; [|constructor; apply singleton_singleton | easy].
        split. validate.
        rewrite merge_comm. 
        rewrite merge_singleton_append.
        easy.
      * unfold process_gate_state.
        simpl.
        rewrite Nat.add_succ_r.
        rewrite <- (Nat.add_1_r (size_octx Γ0 + size_ctx Γ)).
        apply apply_new1_correct.
    + simpl.
      dependent destruction p1.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      destruct Γ as [|Γ]. invalid_contradiction.
      unfold hoas_to_db_pat. simpl.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        replace (S (size_ctx Γ)) with (size_octx (Valid (Γ ++ [Some Bit]))).
          2: simpl; rewrite size_ctx_app; simpl; omega. 
        eapply IH; [|constructor; apply singleton_singleton | easy].
        split. validate.
        rewrite merge_comm. 
        rewrite merge_singleton_append.
        easy.
      * unfold process_gate_state.
        simpl.
        rewrite Nat.add_succ_r.
        rewrite <- (Nat.add_1_r (size_octx Γ0 + size_ctx Γ)).
        apply apply_new0_correct.
    + simpl.
      dependent destruction p1.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      destruct Γ as [|Γ]. invalid_contradiction.
      unfold hoas_to_db_pat. simpl.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        replace (S (size_ctx Γ)) with (size_octx (Valid (Γ ++ [Some Bit]))).
          2: simpl; rewrite size_ctx_app; simpl; omega. 
        eapply IH; [|constructor; apply singleton_singleton | easy].
        split. validate.
        rewrite merge_comm. 
        rewrite merge_singleton_append.
        easy.
      * unfold process_gate_state.
        simpl.
        rewrite Nat.add_succ_r.
        rewrite <- (Nat.add_1_r (size_octx Γ0 + size_ctx Γ)).
        apply apply_new1_correct.
    + simpl.
      dependent destruction p1.
      destruct Γ1' as [|Γ1'].
      inversion pf1. invalid_contradiction. 
      simpl.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        replace (size_ctx Γ1') with (size_octx (Valid (update_at Γ1' v (Some Bit)))).
        Focus 2.
          simpl. 
          rewrite denote_index_update with (w := Qubit).
          reflexivity.
          eapply index_merge_l.
          apply pf1.
          destruct Γ1. invalid_contradiction. 
          apply singleton_index.
          inversion t. easy.
        eapply IH; [|constructor; apply singleton_singleton|easy].
        inversion t; subst.
        eapply update_at_merge; [apply H1| apply singleton_singleton| easy].
      * apply apply_meas_correct.
        apply Nat.lt_lt_add_l.
        replace (ctx_dom Γ1') with (octx_dom Γ1') by reflexivity.
        eapply subst_qubit_bounded; [apply t | apply pf1].
    + simpl.
      dependent destruction p1.
      destruct Γ1' as [|Γ1'].
      inversion pf1. invalid_contradiction. 
      simpl.
      apply compose_super_correct.
      * unfold denote_circuit in IH.
        unfold process_gate_state. simpl.
        replace (size_ctx Γ1') with (size_octx Γ1') by easy.
        eapply IH; [apply pf1|easy|easy].
      * apply apply_meas_correct.
        apply Nat.lt_lt_add_l.
        replace (ctx_dom Γ1') with (octx_dom Γ1') by reflexivity.
        eapply subst_qubit_bounded; [apply t | apply pf1].
    + simpl.        
      apply compose_super_correct.
      * unfold denote_circuit in IH. 
        unfold process_gate_state. simpl.
        dependent destruction t.
        apply singleton_equiv in s. subst.
        assert (M: Γ == ∅ ∙ Γ). split. destruct Γ. invalid_contradiction. validate. 
          rewrite merge_nil_l. easy.
        specialize (t0 ∅ Γ unit M types_unit).
        apply types_circ_types_pat in t0 as [w' [p' TP]]. (* admitted *)
        replace (remove_pat (hoas_to_db_pat Γ1' (bit x)) (size_octx Γ1')) with
            (size_octx (remove_pat (bit x) Γ1')).
        eapply IH; [|constructor|easy].
        split. unfold remove_pat. simpl. 
        destruct Γ1'; validate; invalid_contradiction.
        rewrite merge_nil_l.
        eapply remove_bit_merge; [| apply pf1].
        apply TP.        
        erewrite remove_bit_merge; [| apply TP | apply pf1].
        unfold hoas_to_db_pat. simpl.
        unfold remove_pat. simpl.
        destruct pf1; subst.
        rewrite size_octx_merge.
        simpl.
        rewrite singleton_size. 
        omega.
        easy.
      * unfold apply_to_first.
        dependent destruction p1.
        dependent destruction t.
        apply singleton_equiv in s; subst.
        unfold pat_to_list.
        simpl.
        unfold process_gate_state. simpl.
        unfold remove_pat. simpl.
        rewrite Nat.add_sub_assoc.
        apply apply_discard_correct.
        apply Nat.lt_lt_add_l.            
        eapply subst_bit_bounded; [constructor; apply singleton_singleton|apply pf1].
        destruct pf1; subst.
        rewrite size_octx_merge by easy.
        simpl; rewrite singleton_size.
        omega.
    + simpl.        
      apply compose_super_correct.
      * unfold denote_circuit in IH. 
        unfold process_gate_state. simpl.
        dependent destruction t.
        apply singleton_equiv in s. subst.
        assert (M: Γ == ∅ ∙ Γ). split. destruct Γ. invalid_contradiction. validate. 
          rewrite merge_nil_l. easy.
        specialize (t0 ∅ Γ unit M types_unit).
        apply types_circ_types_pat in t0 as [w' [p' TP]]. (* admitted *)
        replace (remove_pat (hoas_to_db_pat Γ1' (qubit x)) (size_octx Γ1')) with
            (size_octx (remove_pat (qubit x) Γ1')).
        eapply IH; [|constructor|easy].
        split. unfold remove_pat. simpl. 
        destruct Γ1'; validate; invalid_contradiction.
        rewrite merge_nil_l.
        eapply remove_qubit_merge; [| apply pf1].
        apply TP.        
        erewrite remove_qubit_merge; [| apply TP | apply pf1].
        unfold hoas_to_db_pat. simpl.
        unfold remove_pat. simpl.
        destruct pf1; subst.
        rewrite size_octx_merge.
        simpl.
        rewrite singleton_size. 
        omega.
        easy.
      * unfold apply_to_first.
        dependent destruction p1.
        dependent destruction t.
        apply singleton_equiv in s; subst.
        unfold pat_to_list.
        simpl.
        unfold process_gate_state. simpl.
        unfold remove_pat. simpl.
        rewrite Nat.add_sub_assoc.
        apply apply_discard_correct.
        apply Nat.lt_lt_add_l.            
        eapply subst_qubit_bounded; 
          [constructor; apply singleton_singleton|apply pf1].
        destruct pf1; subst.
        rewrite size_octx_merge by easy.
        simpl; rewrite singleton_size.
        omega.
    + simpl.        
      apply compose_super_correct.
      * unfold denote_circuit in IH. 
        unfold process_gate_state. simpl.
        dependent destruction t.
        apply singleton_equiv in s. subst.
        assert (M: Γ == ∅ ∙ Γ). split. destruct Γ. invalid_contradiction. validate. 
          rewrite merge_nil_l. easy.
        specialize (t0 ∅ Γ unit M types_unit).
        apply types_circ_types_pat in t0 as [w' [p' TP]]. (* admitted *)
        replace (remove_pat (hoas_to_db_pat Γ1' (qubit x)) (size_octx Γ1')) with
            (size_octx (remove_pat (qubit x) Γ1')).
        eapply IH; [|constructor|easy].
        split. unfold remove_pat. simpl. 
        destruct Γ1'; validate; invalid_contradiction.
        rewrite merge_nil_l.
        eapply remove_qubit_merge; [| apply pf1].
        apply TP.        
        erewrite remove_qubit_merge; [| apply TP | apply pf1].
        unfold hoas_to_db_pat. simpl.
        unfold remove_pat. simpl.
        destruct pf1; subst.
        rewrite size_octx_merge.
        simpl.
        rewrite singleton_size. 
        omega.
        easy.
      * unfold apply_to_first.
        dependent destruction p1.
        dependent destruction t.
        apply singleton_equiv in s; subst.
        unfold pat_to_list.
        simpl.
        unfold process_gate_state. simpl.
        unfold remove_pat. simpl.
        rewrite Nat.add_sub_assoc.
        apply apply_discard_correct.
        apply Nat.lt_lt_add_l.            
        eapply subst_qubit_bounded; 
          [constructor; apply singleton_singleton|apply pf1].
        destruct pf1; subst.
        rewrite size_octx_merge by easy.
        simpl; rewrite singleton_size.
        omega.
  - (* Lifting is an interesting case since we are combining two subterms which are 
       not themselves mixed_states. To be precise, denote_db_circuit is being 
       apply to /partial mixed states/ and a predicate saying that circuits preserve
       partial-mixed-states and their traces. We leave this for future work. *)
    inversion STAT.
Qed.

Inductive Static_Box {W1 W2} : Box W1 W2 -> Prop := 
| S_box : forall c, (forall p, Static_Circuit (c p)) -> Static_Box (box c).


(* This seems like an important unproven lemma *)
(* It might just make sense to define fresh_state and fresh_pat in terms of mk_typed_pat *)
Lemma fresh_state_types_fresh_pat : forall W W' Γ (p : Pat W'), 
    Γ ⊢ p :Pat ->
    fresh_state W Γ ⊢ (pair (fresh_pat W Γ) p) :Pat.
Proof.
  induction W; intros W' Γ p H.
  - simpl. 
    unfold add_fresh_state; simpl.
    unfold get_fresh_var; simpl.
    destruct Γ as [|Γ]. inversion H. invalid_contradiction.
    simpl.
    Search app merge.
    econstructor.
    validate.
    rewrite <- merge_singleton_append.
    rewrite merge_comm. easy.
    constructor. apply singleton_singleton.
    easy.
  - simpl. 
    unfold add_fresh_state; simpl.
    unfold get_fresh_var; simpl.
    destruct Γ as [|Γ]. inversion H. invalid_contradiction.
    simpl.
    Search app merge.
    econstructor.
    validate.
    rewrite <- merge_singleton_append.
    rewrite merge_comm. easy.
    constructor. apply singleton_singleton.
    easy.
  - simpl. 
    econstructor.
    validate.
    rewrite merge_nil_l. easy.
    constructor.
    easy.
  - simpl.
    econstructor.
    repeat apply is_valid_fresh. validate.
Admitted.    
    
Lemma fresh_state_empty_types_fresh_pat : forall W, fresh_state W ∅ ⊢ fresh_pat W ∅ :Pat.
Proof.
  intros W.
  specialize (fresh_state_types_fresh_pat W One ∅ unit types_unit) as FST.
  dependent destruction FST.
  dependent destruction FST2.
  rewrite merge_nil_r in e. rewrite e.
  easy.
Qed.
  
Lemma mk_typed_pat_fresh : forall W Γ p, 
  (Γ, p) = mk_typed_pat [] W ->
  Γ = fresh_state W [] /\ p = fresh_pat W [].
Proof. 
  induction W; intros Γ p E.
  - cbv; inversion E; easy. 
  - cbv; inversion E; easy. 
  - cbv; inversion E; easy. 
  - simpl in E.
    destruct (mk_typed_pat [] W1) as [Γ1 p1] eqn:E1. symmetry in E1.
    destruct (mk_typed_pat Γ1 W2) as [Γ2 p2] eqn:E2. symmetry in E2.
    specialize (typed_pat_merge_valid _ _ _ _ E2) as V. 
    destruct V as [Γ12 M].
    simpl.
    destruct (IHW1 _ _ eq_refl) as [FS1 FP1].
    destruct (IHW1 _ _ eq_refl) as [FS2 FP2].
Abort.


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
  set (Γ := (fresh_state W1 ∅)).
  set (p := (fresh_pat W1 ∅)).
  set (c := (c' p)).
  specialize (STAT p).
  Search fresh_state fresh_pat.
  specialize (WT Γ p).
  specialize (denote_static_circuit_correct W2 ∅ Γ c STAT) as WFC.
  unfold denote_circuit in WFC.
  simpl in WFC.
  simpl_rewrite' (ctx_wtype_size Γ W1 p).
  apply WFC.
  apply WT.
  apply fresh_state_empty_types_fresh_pat. (* admitted *)
  apply fresh_state_empty_types_fresh_pat.
Qed.

(* This will need to wait for a more general version of denote_circuit_correct *)
Theorem denote_box_correct : forall W1 W2 (c : Box W1 W2), 
  Typed_Box c -> WF_Superoperator (⟦c⟧).
Proof.
  intros W1 W2 c T.
  destruct c.
  simpl in *.
  induction c.
Admitted.

(********************************************)
(* Lemmas regarding denotation with padding *)
(********************************************)

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

Lemma decr_pat_once_qubit : forall n Γ, 
    decr_pat_once (fresh_pat (NTensor n Qubit) (Valid (Some Qubit :: Γ)))
    = fresh_pat (NTensor n Qubit) (Valid Γ).
Proof.
  induction n; intros; trivial.
  simpl. unfold add_fresh_state. simpl. rewrite IHn. rewrite Nat.sub_0_r. easy.
Qed.

Lemma decr_circuit_pat : forall W1 W2 (c : Box W1 W2) (p : Pat W1), 
    decr_circuit_once (unbox c p) = unbox c (decr_pat_once p).
Admitted.

Lemma denote_db_pad_left : forall (Γ0 Γ : Ctx) pad n W (c : Circuit W) 
  (ρ1 : Square (2^pad)) (ρ2 : Square (2^n)), 
  ⟦Γ0⟧ = pad ->
  ⟦Γ⟧ = n ->  
  ⟨Γ0 | Valid (repeat None pad ++ Γ) ⊩ c ⟩ (ρ1 ⊗ ρ2) = 
  ρ1 ⊗ (⟨ ∅ | Γ ⊩ decr_circuit pad c ⟩ ρ2).
Admitted.

Lemma denote_db_pad_right : forall (Γ0 Γ : OCtx) pad n w (c : Circuit w) (ρ1 : Square (2^n)) (ρ2 : Square (2^pad)),
  ⟦Γ0⟧ = pad ->
  ⟦Γ⟧ = n ->
  ⟨ Γ0 | Γ ⊩ c ⟩ (ρ1 ⊗ ρ2) = ⟨ ∅ | Γ ⊩ c ⟩ ρ1 ⊗ ρ2.
Admitted.



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

Hint Unfold get_fresh add_fresh_state get_fresh_var process_gate process_gate_state : den_db.

Hint Unfold apply_new0 apply_new1 apply_U apply_qubit_unitary denote_ctrls apply_meas apply_discard apply_assert0 apply_assert1 compose_super Splus swap_list swap_two pad denote_box denote_pat super: den_db.

Hint Unfold get_fresh add_fresh_state get_fresh_var process_gate process_gate_state : ket_den_db.

Hint Unfold apply_new0 apply_new1 apply_U apply_qubit_unitary denote_ctrls apply_meas apply_discard apply_assert0 apply_assert1 compose_super Splus swap_list swap_two pad denote_box denote_pat : ket_den_db.

(* This should probably be vector_denote *)
Ltac ket_denote :=
  intros; 
  repeat (autounfold with ket_den_db; simpl);
  repeat rewrite <- bool_to_ket_matrix_eq;
  repeat replace (|0⟩⟨0|) with (outer_product |0⟩) by reflexivity;
  repeat replace (|1⟩⟨1|) with (outer_product |1⟩) by reflexivity;
  repeat rewrite outer_product_kron;
  repeat rewrite super_outer_product;
  apply outer_product_eq.

Ltac matrix_denote :=
  intros; repeat (autounfold with den_db; simpl).

Hint Rewrite hoas_to_db_pat_fresh_empty : proof_db.
Hint Rewrite size_octx_fresh using validate : proof_db.
(* add some arithmetic *)
Hint Rewrite Nat.leb_refl : proof_db.
Hint Rewrite denote_pat_fresh_id : proof_db.
Hint Rewrite swap_fresh_seq : proof_db.
(* Hint Rewrite apply_U_σ pad_nothing using auto : proof_db. *)



(**********************)
(* Composition lemmas *)
(**********************)

Lemma merge_singleton_end : forall Γ w,
      Valid (Γ ++ [Some w]) = Valid Γ ⋓ singleton (length Γ) w.
Proof.
  unlock_merge.
  induction Γ as [ | [w' | ] Γ]; intros; simpl in *; auto.
  * rewrite <- IHΓ. reflexivity.
  * rewrite <- IHΓ. reflexivity.
Qed.

Lemma fresh_state_pat : forall w,
      fresh_state w ∅ ⊢ fresh_pat w ∅ :Pat.
Proof.
  induction w; repeat constructor.
Admitted.

Lemma fresh_state_decompose : forall w Γ,
      is_valid Γ ->
      fresh_state w Γ == Γ ∙ (pat_to_ctx (fresh_pat w Γ)).
Proof.
  induction w; intros;
    (destruct Γ as [ | Γ]; [invalid_contradiction | ]);
    simpl.
  - solve_merge. unfold add_fresh_state. simpl. validate. 
    simpl. apply merge_singleton_end.
  - solve_merge. unfold add_fresh_state. simpl. validate. 
    simpl. apply merge_singleton_end.
  - solve_merge.
  - solve_merge. 
    * repeat apply is_valid_fresh; auto.
    * destruct (IHw1 Γ); [auto | ].
      rewrite pf_merge.
      rewrite pf_merge in pf_valid.
      destruct (IHw2 (Γ ⋓ pat_to_ctx (fresh_pat w1 (Valid Γ)))); auto.
      rewrite pf_merge0.
      monoid.
Qed.

Theorem inSeq_correct : forall W1 W2 W3 (g : Box W2 W3) (f : Box W1 W2) (safe : bool),
      Typed_Box g -> Typed_Box f ->
      denote_box safe (inSeq f g) = 
      compose_super (denote_box safe g) (denote_box safe f).
Proof.
  intros W1 W2 W3 g f safe types_g types_f.
  autounfold with den_db; simpl. 

  destruct f as [f]. 
  destruct g as [g].
  autounfold with den_db; simpl.

  set (Γ1_0 := fresh_state W1 ∅).
  set (Γ2_0 := fresh_state W2 ∅).
  assert (⟦Γ1_0⟧ = ⟦W1⟧).
  { unfold Γ1_0.
    rewrite size_octx_fresh; auto.
    validate. }
  assert (⟦Γ2_0⟧ = ⟦W2⟧).
  { unfold Γ2_0.
    rewrite size_octx_fresh; auto.
    validate. }

  replace 0%nat with (⟦∅⟧:nat) by auto.
  replace (size_wtype W1) with (⟦Γ1_0⟧).
  replace (size_wtype W2) with (⟦Γ2_0⟧).

  apply denote_compose. 
  * apply types_f. apply fresh_state_pat. 
  * unfold Typed_Box in types_g. intros Γ Γ' p pf wf_p.
    solve_merge.
    apply types_g. monoid. auto.
  * solve_merge.
    apply is_valid_fresh. validate.
Qed.

Theorem inPar_correct : forall W1 W1' W2 W2' (f : Box W1 W1') (g : Box W2 W2') (safe : bool)
     (ρ1 : Square (2^⟦W1⟧)) (ρ2 : Square (2^⟦W2⟧)),
     Typed_Box f -> Typed_Box g ->
     WF_Matrix (2^⟦W1⟧) (2^⟦W1⟧) ρ1 -> 
     WF_Matrix (2^⟦W2⟧) (2^⟦W2⟧) ρ2 ->
     denote_box safe (inPar f g) (ρ1 ⊗ ρ2)%M = 
    (denote_box safe f ρ1 ⊗ denote_box true g ρ2)%M.
Proof.  
  intros W1 W1' W2 W2' f g safe ρ1 ρ2 types_f types_g mixed_ρ1 mixed_ρ2.
  destruct f as [f]. 
  destruct g as [g].
  repeat (autounfold with den_db; simpl).


  set (p_1 := fresh_pat W1 ∅).
  set (Γ_1 := fresh_state W1 ∅).
  set (p_2 := fresh_pat W2 Γ_1).
  set (Γ_2 := fresh_state W2 Γ_1).
  assert (Γ_1 ⊢ p_1 :Pat) by apply fresh_state_pat.
  assert (Γ_2 ⊢ p_2 :Pat) by admit (* need a vaiant of fresh_pat_typed *).

  replace 0%nat with (⟦∅⟧) by auto.
  replace (size_wtype W1 + size_wtype W2)%nat with (⟦Γ_2⟧).
  replace (size_wtype W1) with (⟦Γ_1⟧).
  replace (size_wtype W2) with (⟦fresh_state W2 ∅⟧).

  specialize denote_compose as DC. unfold denote_circuit in DC. 
  rewrite DC with (Γ1' := Γ_2) (Γ1 := Γ_2) (Γ := Γ_1). 
  set (Γ_3 := pat_to_ctx (fresh_pat W1' Γ_2)).
  rewrite DC with (Γ1' := fresh_state W1' Γ_2) (Γ1 := Γ_3) (Γ := Γ_2). clear DC.

  autounfold with den_db.
  repeat rewrite merge_nil_l.
  (*
  repeat rewrite denote_tensor.
  Search (⟨ _ | _ ⊩ output _ ⟩).
  rewrite denote_output.
  autorewrite with proof_db.*)
  admit (* stuck *). 
  * apply types_g; auto.
  * intros.
    destruct H1. econstructor. reflexivity.
    econstructor. 4: apply H2. assumption. 
    rewrite merge_comm in pf_merge. apply pf_merge.
    unfold Γ_3.
    Search (pat_to_ctx) fresh_pat.
    admit (* need a variant of fresh_pat_typed *).
  * unfold Γ_3.
    assert (valid_Γ_2 : is_valid Γ_2) by admit.
    generalize (fresh_state_decompose W1' Γ_2 valid_Γ_2); intros assertion.
    solve_merge.
    rewrite pf_merge. monoid.
  * apply types_f; auto.
  * intros. eapply compose_typing. apply types_g. apply H0.
    intros. econstructor. reflexivity. econstructor.
    destruct H3. assumption.
    2: apply H2. 2: apply H4. 
    rewrite merge_comm. destruct H3. apply pf_merge.
    destruct H1; constructor; [|rewrite merge_comm]; easy.
  * admit (* this is not true... *).
  * rewrite size_octx_fresh; auto. validate.
  * unfold Γ_1. rewrite size_octx_fresh. auto. validate.
  * unfold Γ_2, Γ_1. repeat rewrite size_octx_fresh. auto.
    validate. validate.
Admitted.

Lemma HOAS_Equiv_inSeq : forall w1 w2 w3 (c1 c1' : Box w1 w2) (c2 c2' : Box w2 w3),
    Typed_Box c1 -> Typed_Box c1' ->  Typed_Box c2 -> Typed_Box c2' -> 
    c1 ≡ c1' -> c2 ≡ c2' -> (c2 · c1) ≡ (c2' · c1').
Proof.
  intros w1 w2 w3 c1 c1' c2 c2' T1 T1' T2 T2' E1 E2.
  intros ρ b Mρ.
  simpl_rewrite inSeq_correct; trivial.
  simpl_rewrite inSeq_correct; trivial.
  unfold compose_super.
  rewrite E1 by easy.
  rewrite E2. (* unsafe case? *)
  easy. 
  admit. 
Admitted.  
