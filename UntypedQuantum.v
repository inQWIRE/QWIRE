Require Import Program.
Require Import Psatz.
Require Import Omega.
Require Import Reals.
Require Import Bool.
Require Export UntypedMatrix.
Require Export Coquelicot.Complex.


(* Using our (complex, unbounded) matrices, their complex numbers *)

Open Scope R_scope.
Open Scope C_scope.
Open Scope matrix_scope.

(* WARNING: Resize should only be used where m = m' and n = n'.
   It should be followed with a proof of this: resize_safe. *) 
Definition resize (m n : nat) (A : Matrix) : Matrix := Mat m n (entry A).
Definition resize_safe (m n m' n' : nat) : Prop := m = m' /\ n = n'.
Transparent resize.

Definition ket0 : Matrix := Mat 2 1
 (fun x y => match x, y with 
          | 0, 0 => 1
          | 1, 0 => 0
          | _, _ => 0
          end).
Definition ket1 : Matrix := Mat 2 1
 (fun x y => match x, y with 
          | 0, 0 => 0
          | 1, 0 => 1
          | _, _ => 0
          end).

Definition ket (x : nat) : Matrix := if x =? 0 then ket0 else ket1.
Transparent ket0.
Transparent ket1.
Transparent ket.

Notation "|0⟩" := ket0.
Notation "|1⟩" := ket1.
Notation "⟨0|" := ket0†.
Notation "⟨1|" := ket1†.
Notation "|0⟩⟨0|" := (|0⟩×⟨0|).
Notation "|1⟩⟨1|" := (|1⟩×⟨1|).
Notation "|1⟩⟨0|" := (|1⟩×⟨0|).
Notation "|0⟩⟨1|" := (|0⟩×⟨1|).

Definition hadamard : Matrix := Mat 2 2 
  (fun x y => match x, y with
          | 0, 0 => (1 / √2)
          | 0, 1 => (1 / √2)
          | 1, 0 => (1 / √2)
          | 1, 1 => -(1 / √2)
          | _, _ => 0
          end).

Fixpoint hadamard_k (k : nat) : Matrix := 
  match k with
  | 0 => Id 1
  | S k' => hadamard ⊗ hadamard_k k'
  end.

(*
Lemma hadamard_1 : hadamard_k 1 = hadamard.
Proof. apply kron_1_r. Qed.
*)

Definition pauli_x : Matrix := Mat 2 2
  (fun x y => match x, y with
          | 0, 0 => 0
          | 0, 1 => 1
          | 1, 0 => 1
          | 1, 1 => 0
          | _, _ => 0
          end).

Definition pauli_y : Matrix := Mat 2 2
  (fun x y => match x, y with
          | 0, 1 => -Ci
          | 1, 0 => Ci
          | _, _ => 0
          end).

Definition pauli_z : Matrix := Mat 2 2 
  (fun x y => match x, y with
          | 0, 0 => 1
          | 1, 1 => -1
          | _, _ => 0
          end).
  
Definition control A := Mat (2*dim_x A) (2*dim_y A) (fun x y =>
    let n := dim_x A in
    if (x <? n) && (y <? n) then entry (Id n) x y
    else if (n <=? x) && (n <? y) then entry A (x-n)%nat (y-n)%nat
    else 0).

(* Definition cnot := control pauli_x. *)
(* Direct definition makes our lives easier *)
Definition cnot : Matrix := Mat 4 4
 (fun x y => match x, y with 
          | 0, 0 => 1
          | 1, 1 => 1
          | 2, 3 => 1
          | 3, 2 => 1
          | _, _ => 0
          end).


(* Swap Matrices *)

Definition swap : Matrix := Mat 4 4
  (fun x y => match x, y with
          | 0, 0 => 1
          | 1, 2 => 1
          | 2, 1 => 1
          | 3, 3 => 1
          | _, _ => 0
          end).
Lemma WF_swap : WF_Matrix 4 4 swap.
Proof.
  constructor; auto.
  intros; simpl. 
  assert (~(0 >= 4)%nat) by omega.
  assert (~(1 >= 4)%nat) by omega.
  assert (~(2 >= 4)%nat) by omega.
  assert (~(3 >= 4)%nat) by omega.
  destruct H. 
  - destruct x as [|[|[|[|]]]]; try contradiction; auto.
  - destruct y as [|[|[|[|]]]]; try contradiction; auto.
    destruct x as [|[|[|[|]]]]; auto.
Qed.
Hint Resolve WF_swap.

Lemma double_mult : forall (n : nat), (n + n = 2 * n)%nat.
Proof. intros. omega. Qed.
Lemma pow_two_succ_l : forall x, (2^x * 2 = 2 ^ (x + 1))%nat.
Proof. intros. rewrite mult_comm. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma pow_two_succ_r : forall x, (2 * 2^x = 2 ^ (x + 1))%nat.
Proof. intros. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma double_pow : forall (n : nat), (2^n + 2^n = 2^(n+1))%nat. 
Proof. intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity. Qed.
Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> (a^m = b^n)%nat.
Proof. intuition. Qed.
Lemma pow_gt_0 : forall m n, (m > 0)%nat -> (m ^ n <> 0)%nat.
Proof. intros; induction n; simpl; [intuition | ]. SearchAbout (_ * _ = 0)%nat.
  apply Nat.neq_mul_0; split; omega.
Qed.

Ltac unify_pows_two :=
  repeat match goal with
  (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
  | [ |- context[ 4%nat ]]                  => replace 4%nat with (2^2)%nat by reflexivity
  | [ |- context[ (0 + ?a)%nat]]            => rewrite plus_0_l 
  | [ |- context[ (?a + 0)%nat]]            => rewrite plus_0_r 
  | [ |- context[ (2 * 2^?x)%nat]]          => rewrite <- Nat.pow_succ_r'
  | [ |- context[ (2^?x * 2)%nat]]          => rewrite pow_two_succ_l
  | [ |- context[ (2^?x + 2^?x)%nat]]       => rewrite double_pow 
  | [ |- context[ (2^?x * 2^?y)%nat]]       => rewrite <- Nat.pow_add_r 
  | [ |- context[ (?a + (?b + ?c))%nat ]]   => rewrite plus_assoc 
  | [ |- (2^?x = 2^?y)%nat ]                => apply pow_components; try omega 
  | [ |- (_ ^ _ <> 0)%nat ]                 => apply pow_gt_0; try omega
  end.

(* The input k is really k+1, to appease to Coq termination gods *)
(* NOTE: Check that the offsets are right *)
(* Requires: i + 1 < n *)
Fixpoint swap_to_0_aux (n i : nat) {struct i} : Matrix := (*(2^n) (2^n) := *)
  match i with
  | O    => swap ⊗ Id (2^(n-2))
  | S i' => (* #1: 2^(i'+2+n-i'-2) square matrix *)
            (* #2: 2^n square matrix *)
            (* #3: 2^(i'+2+n-i'-2) *)
            (Id (2^i') ⊗ swap ⊗ Id (2^(n-i'-2))) × (* swap i-1 with i *) 
            swap_to_0_aux n i' × 
            (Id (2^i') ⊗ swap ⊗ Id (2^(n-i'-2))) (* swap i-1 with 0 *)
  end.
Lemma WF_swap_to_0_aux : forall i n, (S i < n)%nat ->
      WF_Matrix (2^n) (2^n) (swap_to_0_aux n i).
Proof.
  induction i; intros; simpl. 
  - show_wf; try apply WF_swap; unify_pows_two.
  - show_wf; try apply WF_swap; try reflexivity; unify_pows_two. 
    replace (2^(i+2+(n-i-2)))%nat with (2^n)%nat by unify_pows_two.
    apply IHi. omega.
Qed.
Hint Resolve WF_swap_to_0_aux.


(* Requires: i < n *)
Definition swap_to_0 (n i : nat) : Matrix :=
  match i with 
  | O    => Id (2^n) 
  | S i' => swap_to_0_aux n i'
  end.
Lemma WF_swap_to_0 : forall i n, (i < n)%nat -> 
      WF_Matrix (2^n)%nat (2^n) (swap_to_0 n i).
Proof.
  destruct i; intros; simpl; show_wf; auto.
Qed.
Hint Resolve WF_swap_to_0.
 
(* Requires i < j, j < n *)
Fixpoint swap_two_aux (n i j : nat) :=
  match i with 
  | O    => swap_to_0 n j 
  | S i' => Id 2 ⊗ swap_two_aux (n-1) (i') (j-1)
  end.
Lemma WF_swap_two_aux : forall i j n, (i < j)%nat -> (j < n)%nat -> 
      WF_Matrix (2^n) (2^n) (swap_two_aux n i j).
Proof.
  induction i; intros; simpl; auto.
  replace (2^n)%nat with (2 * 2^(n-1))%nat by unify_pows_two.
  show_wf; auto; unify_pows_two.
  apply IHi; omega. 
Qed.
Hint Resolve WF_swap_two_aux.

(* Requires i < n, j < n *)
Definition swap_two (n i j : nat) :=
  if i =? j then Id (2^n) 
  else if i <? j then swap_two_aux n i j
  else swap_two_aux n j i.
Lemma WF_swap_two : forall n i j, (i<n)%nat -> (j<n)%nat ->
      WF_Matrix (2^n) (2^n) (swap_two n i j).
Proof.
  intros; unfold swap_two.
  destruct (i =? j) eqn:eq. show_wf.
  destruct (i <? j) eqn:lt. 
      apply Nat.ltb_lt in lt; auto. SearchAbout (_ =? _).
      apply Nat.ltb_ge in lt. apply beq_nat_false in eq. 
      assert (j < i)%nat by omega; auto.
Qed.
Hint Resolve WF_swap_two.


(* Simpler version of swap_to_0 that shifts other elements *)
(* Requires: i+1 < n *)
Definition move_to_0_aux (n i : nat) :=
  match i with
  | O => swap ⊗ Id (2^(n-2))
  | S i' => (Id (2^i') ⊗ swap ⊗ Id (2^(n-i'-2))) × swap_to_0_aux n i
  end.
Lemma WF_move_to_0_aux : forall n i, (S i < n)%nat ->
      WF_Matrix (2^n) (2^n) (move_to_0_aux n i).
Proof.
  intros. destruct i; simpl.
Admitted.
  

Lemma move_to_0_aux_safe : forall (i' n : nat), (i'+2 < n)%nat -> 
  resize_safe (2^i' * 4 * 2^(n-i'-2)) (2^i' * 4 * 2^(n-i'-2)) (2^n) (2^n).
Proof. intros. unfold resize_safe. split; unify_pows_two. Qed.
             
(* Requires: i < n *)
Definition move_to_0 (n i : nat) :=
  match i with 
  | O => Id (2^n) 
  | S i' => move_to_0_aux n i'
  end.
 
(* Always moves up in the matrix from i to k *)
(* Requires: k < i < n *)
Fixpoint move_to (n i k : nat) :=
  match k with 
  | O => move_to_0 n i 
  | S k' => Id 2 ⊗ move_to (n-1) (i-1) (k')
  end.

Lemma swap_two_base : swap_two 2 1 0 = swap.
Proof. 
  unfold swap_two; simpl. 
  eapply kron_1_r; eauto.
Qed.

Lemma swap_second_two : swap_two 3 1 2 = Id 2 ⊗ swap.
Proof. unfold swap_two.
       simpl.
       erewrite kron_1_r; eauto.
Qed.

(*
Eval compute in ((swap_two 1 0 1) 0 0)%nat.
Eval compute in (print_matrix (swap_two 1 0 2)).
*)

(** Unitaries are well-formed **)



Lemma WF_hadamard : WF_Matrix 2 2 hadamard. Proof. show_wf_manual. Qed.
Lemma WF_pauli_x : WF_Matrix 2 2 pauli_x. Proof. show_wf_manual. Qed.
Lemma WF_pauli_y : WF_Matrix 2 2 pauli_y. Proof. show_wf_manual. Qed.
Lemma WF_pauli_z : WF_Matrix 2 2 pauli_z. Proof. show_wf_manual. Qed.

Hint Resolve WF_hadamard.
Hint Resolve WF_pauli_x.
Hint Resolve WF_pauli_y.
Hint Resolve WF_pauli_z.

Lemma WF_ket0 : WF_Matrix 2 1 |0⟩.
Proof. show_wf_manual. Qed.
Lemma WF_ket1 : WF_Matrix 2 1 |1⟩.
Proof. show_wf_manual. Qed.
Hint Resolve WF_ket0. Hint Resolve WF_ket1.
Lemma WF_bra0 : WF_Matrix 1 2 ⟨0|.
Proof. show_wf; auto. Qed.
Lemma WF_bra1 : WF_Matrix 2 1 |1⟩.
Proof. show_wf; auto. Qed.
Hint Resolve WF_bra0. Hint Resolve WF_bra1.

Lemma WF_braket1 : WF_Matrix 2 2 |1⟩⟨1|.
Proof. show_wf; apply WF_ket1. Qed.
Lemma WF_braket0 : WF_Matrix 2 2 |0⟩⟨0|.
Proof. show_wf; apply WF_ket0. Qed.
Hint Resolve WF_braket1.
Hint Resolve WF_braket0.

Lemma braket0_conj_transpose : |0⟩⟨0|† = |0⟩⟨0|.
Proof.
  mlra; apply WF_ket0.
Qed.
Lemma braket1_conj_transpose : |1⟩⟨1|† = |1⟩⟨1|.
Proof.
  mlra; apply WF_ket1.
Qed.


Lemma WF_control : forall {n} (U : Matrix), 
      WF_Matrix n n U -> WF_Matrix (2* n) (2*n) (control U).
Proof.
  intros n U WFU. show_wf_manual; show_wf.
  + replace (x <? n) with false by (symmetry; apply Nat.ltb_ge; omega). simpl.
    destruct (n <=? x) eqn:Hx, (n <? y) eqn:Hy; simpl; auto.
    rewrite_all_wf_matrix; omega.
  + replace (dim_y U) with n in * by rewrite_all_wf_matrix.
    replace (y <? n)%nat with false by (symmetry; apply Nat.ltb_ge; omega).
    rewrite andb_false_r.
    rewrite_all_wf_matrix; try omega.
    destruct ((n <=? x) && (n <? y))%nat; reflexivity.
Qed.
Hint Resolve WF_control.

Lemma WF_cnot : WF_Matrix 4 4 cnot. Proof. show_wf_manual. Qed.
(* Proof. replace 4%nat with (2*2)%nat by auto. apply WF_control. apply WF_pauli_x. Qed. *)
Hint Resolve WF_cnot.

(** Unitaries are unitary **)


Record Unitary n (U : Matrix) : Prop :=
  is_unitary { unitary_wf : WF_Matrix n n U
             ; unitary_transpose : U † × U = Id n }.
Ltac solve_unitary :=
  repeat match goal with
  | [ |- Unitary _ _ ] => constructor
  | [ H : Unitary _ _ |- _ ] => destruct H
  end; rewrite_all_wf_matrix; simpl; auto.
(*  repeat match goal with
  | [ eq : ?x = ?y |- _ ] => rewrite eq in *; clear eq
  end.*)

(* More precise *)
(* Definition unitary_matrix' {n: nat} (A : Matrix n n): Prop := Minv A A†. *)

Lemma H_unitary : Unitary 2 hadamard.
Proof. 
  solve_unitary.
  mlra; eauto. 
  destruct x as [| [|x]]; destruct y as [|[|y]]; Csimpl; try Csolve.
  replace ((S (S x) <? 2)) with (false) by reflexivity.
  rewrite andb_false_r.
  reflexivity.
Qed.
Hint Resolve H_unitary.

Lemma σx_unitary : Unitary 2 pauli_x.
Proof. 
  solve_unitary.
  mlra; eauto.
  destruct x as [| [|x]]; destruct y as [|[|y]]; Csimpl; try Csolve.
  replace ((S (S x) <? 2)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.
Hint Resolve σx_unitary.

Lemma σy_unitary : Unitary 2 pauli_y.
Proof.
  solve_unitary.
  mlra; eauto.
  destruct x as [| [|x]]; destruct y as [|[|y]]; Csimpl; try Csolve.
  replace ((S (S x) <? 2)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.
Hint Resolve σy_unitary.

Lemma σz_unitary : Unitary 2 pauli_z.
Proof.
  solve_unitary.
  mlra; try apply WF_pauli_z.
  destruct x as [| [|x]]; destruct y as [|[|y]]; Csimpl; try Csolve.
  replace ((S (S x) <? 2)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.
Hint Resolve σz_unitary.

Lemma control_unitary : forall n (A : Matrix),
                          Unitary n A -> Unitary (2*n)%nat (control A). 
Proof.
  intros n A H.
  assert (WF_Matrix (2 * n) (2 * n) (control A)).
  { apply WF_control. solve_unitary. }
  solve_unitary. 
  mlra. 
  generalize dependent n. induction n; intros; simpl.
  + replace (x <? 0) with false by reflexivity. omega. 
  + 
Admitted.
Hint Resolve control_unitary.

Lemma transpose_unitary : forall n A, Unitary n A -> Unitary n (A†).
  intros. solve_unitary; [show_wf | ].

  erewrite conj_transpose_involutive; eauto.
  apply Minv_left; auto. show_wf. (* NB: Admitted lemma *)
Qed.
Hint Resolve transpose_unitary.

Lemma cnot_unitary : Unitary 4 cnot.
Proof.
  solve_unitary. 
  mlra; eauto.
  do 4 (try destruct x; try destruct y; try clra).
  replace ((S (S (S (S x))) <? 4)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.
Hint Resolve cnot_unitary.

Lemma id_unitary : forall n, Pos n -> Unitary n (Id n). 
Proof.
  intros; solve_unitary; [mlra | ].
  rewrite id_conj_transpose_eq; auto.
  eapply Mmult_1_l; mlra.
Qed.
Hint Resolve id_unitary.

Lemma swap_unitary : Unitary 4 swap.
Proof. 
  solve_unitary.
  mlra; eauto.
  do 4 (try destruct x; try destruct y; try clra).
  replace ((S (S (S (S x))) <? 4)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.


Lemma kron_unitary : forall m n A B,
  Unitary m A -> Unitary n B -> Unitary (m*n)%nat (A ⊗ B).
Admitted.

Lemma unitary_swap_to_0 : forall n i, (i < n)%nat -> Unitary (2^n) (swap_to_0 n i).
Proof.
  intros n i.
  generalize dependent n.
  split.
  + (* well-formedness *)
    induction i. 
    simpl. apply WF_Id; solve_pos.
    simpl in *.
    unfold swap_to_0 in IHi.
    destruct i; simpl in *; auto.
Admitted. 
(*
    (* We need a tactic here *)
    apply WF_kron; try (apply Nat.pow_nonzero; omega).
    apply WF_swap.
    apply WF_Id.
    replace (2^n)%nat with  (2 ^ i * 4 * 2 ^ (n - i - 2))%nat by unify_pows_two.
    apply WF_mult.
    apply WF_mult.
    apply WF_kron; try (apply Nat.pow_nonzero; omega).
    apply WF_kron; try omega. 
    apply WF_Id.
    apply WF_swap.
    apply WF_Id.
    replace (2 ^ i * 4 * 2 ^ (n - i - 2))%nat with (2^n)%nat by unify_pows_two.
    apply IHi.
    omega.
    apply WF_kron; try (apply Nat.pow_nonzero; omega).
    apply WF_kron; try omega. 
    apply WF_Id.
    apply WF_swap.
    apply WF_Id.
  + induction i; simpl.
    - apply id_unitary.
    - unfold swap_to_0 in IHi. 
      destruct i.
      * simpl.
        remember ( Id (2 ^ (n - 2))) as A.
        remember swap as B.
        setoid_rewrite (kron_conj_transpose B A).            
    
(*    rewrite (kron_mixed_product B† A† B A). *)



        specialize (kron_mixed_product B† A† B A); intros H'.
        assert (is_unitary B). subst. apply swap_unitary.
        assert (is_unitary A). subst. apply id_unitary.
        destruct H0 as [_ H0], H1 as [_ H1].
        rewrite H0 in H'.
        rewrite H1 in H'.
        replace (Id (2 ^ n)) with (Id 4 ⊗ Id (2 ^ (n - 2))).
        (* apply H doesn't work. 
         Surprisingly, that's the matrix types failing to line up *)
        rewrite <- H'.
        replace (4 * (2 ^ (n - 2)))%nat with (2 ^ n)%nat.
        reflexivity.
        unify_pows_two.
        unify_pows_two.
        replace (2^n)%nat with (2^2 * 2^(n-2))%nat by unify_pows_two.
        rewrite id_kron.
        reflexivity.
      * simpl.
Admitted.
*)

Lemma unitary_swap_two : forall n i j, (i < n)%nat -> (j < n)%nat ->
                                  Unitary (2^n) (swap_two n i j).
Proof.
  intros n i j P1 P2. solve_unitary. 
  destruct (lt_eq_lt_dec i j) as [[ltij | eq] | ltji].
  + mlra.
Admitted.

(* Pure and Mixed States *)

(* Wiki:
In operator language, a density operator is a positive semidefinite, hermitian 
operator of trace 1 acting on the state space. A density operator describes 
a pure state if it is a rank one projection. Equivalently, a density operator ρ 
describes a pure state if and only if ρ = ρ ^ 2 *)

(*Notation Density n := (Matrix n n) (only parsing). *)

Inductive Pure_State n (ρ : Matrix) : Prop :=
  pure_state { WF_pure : WF_Matrix n n ρ
             ; pure_inv : ρ = ρ × ρ }.
Hint Resolve WF_pure.

Lemma pure0 : Pure_State 2 |0⟩⟨0|. Proof. constructor; auto. mlra; eauto. Qed.
Lemma pure1 : Pure_State 2 |1⟩⟨1|. Proof. constructor; auto. mlra; eauto. Qed.

(* Wiki:
For a finite-dimensional function space, the most general density operator 
is of the form:

  ρ =∑_j p_j |ψ_j⟩⟨ ψ_j| 

where the coefficients p_j are non-negative and add up to one. *)

Inductive Mixed_State : nat -> Matrix -> Prop :=
| Pure_S : forall n ρ, Pure_State n ρ -> Mixed_State n ρ
| Mix_S : forall n (p : R) ρ1 ρ2, 0 < p < 1 ->
                                Mixed_State n ρ1 ->
                                Mixed_State n ρ2 ->
                                Mixed_State n (p .* ρ1 .+ (1-p)%R .* ρ2).

Lemma WF_Mixed : forall n ρ, Mixed_State n ρ -> WF_Matrix n n ρ.
Proof.
  induction 1; auto.
  show_wf. 
Qed.
Hint Resolve WF_Mixed.

(** Density matrices and superoperators **)

Definition Superoperator := Matrix -> Matrix.

Definition WF_Superoperator m n f := 
    (forall ρ, Mixed_State m ρ -> Mixed_State n (f ρ)).
Hint Unfold WF_Superoperator.

Definition super M : Superoperator := fun ρ => M × ρ × M†.
Hint Unfold super.

Lemma WF_super : forall m n A ρ, WF_Matrix m n A -> WF_Matrix n n ρ ->
      WF_Matrix m m (super A ρ).
Proof.
  intros.
  unfold super.
  show_wf.
Qed.
Hint Resolve WF_super.  

Definition compose_super (g f : Superoperator) := fun ρ => g (f ρ).


Lemma compose_super_correct : forall m n p g f, 
      WF_Superoperator n p g -> WF_Superoperator m n f ->
      WF_Superoperator m p (compose_super g f).
Proof.
  intros m n p g f pf_g pf_f ρ pf_mixed.
  unfold compose_super.
  apply pf_g. apply pf_f. auto.
Qed.

Definition sum_super f g : Superoperator :=
  fun ρ => (1/2)%R .* f ρ .+ (1 - 1/2)%R .* g ρ.
Lemma WF_sum_super : forall m n f g,
      WF_Superoperator m n f -> WF_Superoperator m n g -> 
      WF_Superoperator m n (sum_super f g).
Proof.
  intros m n f g wf_f wf_g ρ pf_ρ.
  unfold sum_super. 
  set (wf_f' := wf_f _ pf_ρ).
  set (wf_g' := wf_g _ pf_ρ). 
  apply Mix_S; auto. Rsolve.
Qed.
  

(* To do: correctness conditions for density matrices and superoperators *)
(* NOTE: I think these all need fixing *)

(*
Definition new0_op : Superoperator 1 2 := super |0⟩.
Definition new1_op : Superoperator 1 2 := super |1⟩.
Definition meas_op : Superoperator 2 2 := fun ρ => super |0⟩⟨0| ρ .+ super |1⟩⟨1| ρ.
Definition discard_op : Superoperator 2 1 := fun ρ => super ⟨0| ρ .+ super ⟨1| ρ.
*)

Definition new0_op : Superoperator := super |0⟩.
Definition new1_op : Superoperator := super |1⟩.
Definition meas_op : Superoperator := fun ρ => super |0⟩⟨0| ρ .+ super |1⟩⟨1| ρ.
Definition discard_op : Superoperator := fun ρ => super ⟨0| ρ .+ super ⟨1| ρ.




Lemma pure_unitary : forall n (U ρ : Matrix), 
  Unitary n U -> Pure_State n ρ -> Pure_State n (super U ρ).
Proof.
  intros n U ρ [WFU H] [WFρ P].
  constructor; unfold super.
  - show_wf.
  - 
  remember (U × ρ × (U) † × (U × ρ × (U) †)) as rhs.
  rewrite P.
  replace (ρ × ρ) with (ρ × Id n × ρ) by (erewrite Mmult_1_r; eauto).
  rewrite <- H.
  rewrite Heqrhs. 
  repeat erewrite Mmult_assoc; show_wf. 
  reflexivity.
Qed.  

Lemma pure_hadamard_1 : Pure_State 2 (super hadamard |1⟩⟨1|).
Proof. apply pure_unitary. 
       + apply H_unitary.       
       + apply pure1. 
Qed.

Definition dm12 : Matrix := Mat 2 2
  (fun x y => match x, y with
          | 0, 0 => 1 / 2
          | 0, 1 => 1 / 2
          | 1, 0 => 1 / 2
          | 1, 1 => 1 / 2
          | _, _ => 0
          end).

Lemma WF_dm12 : WF_Matrix 2 2 dm12.
Proof. show_wf_manual. Qed.
Hint Resolve WF_dm12.
Lemma pure_dm12 : Pure_State 2 dm12. 
Proof. constructor; auto.
  mlra; eauto.
  destruct x as [| [|x]]; destruct y as [|[|y]]; clra.
Qed.

Lemma mixed_meas_12 : Mixed_State 2 (meas_op dm12).
Proof. unfold meas_op. 
       replace (super |0⟩⟨0| dm12) with ((1/2)%R .* |0⟩⟨0|) 
         by (mlra; eauto).
       replace (super |1⟩⟨1| dm12) with ((1 - 1/2)%R .* |1⟩⟨1|) 
         by (mlra; eauto).
       apply Mix_S.
       lra.
       apply Pure_S; constructor; mlra; eauto.
       apply Pure_S; constructor; mlra; eauto.
Qed.

Lemma mixed_unitary' : forall n (U ρ : Matrix), 
  Unitary n U -> Mixed_State n ρ -> Mixed_State n (super U ρ).
Proof.
  intros n U ρ H M.
  solve_unitary.
  induction M.
  + apply Pure_S.
    apply pure_unitary; auto. solve_unitary.
  + unfold super in *.
    erewrite Mmult_plus_distr_l; show_wf; eauto.
    erewrite Mmult_plus_distr_r; show_wf; eauto.
    erewrite 2 Mscale_mult_dist_r; show_wf; eauto.
    erewrite 2 Mscale_mult_dist_l; show_wf; eauto.
    apply Mix_S; [| apply IHM1 | apply IHM2]; auto.
Qed.
Lemma mixed_unitary : forall n U, Unitary n U -> WF_Superoperator n n (super U).
Proof.
  intros n U pf_U ρ. apply mixed_unitary'; auto.
Qed.




(* *)