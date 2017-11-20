Require Import Program.
Require Import Psatz.
Require Import Omega.
Require Import Reals.
Require Import Bool.
Require Export Complex.
Require Export Matrix.

(* Using our (complex, unbounded) matrices, their complex numbers *)

Open Scope R_scope.
Open Scope C_scope.
Open Scope matrix_scope.

(* WARNING: Resize should only be used where m = m' and n = n'.
   It should be followed with a proof of this: resize_safe. *) 
Definition resize (m n m' n' : nat) (A : Matrix m n) : Matrix m' n' := A.
Definition resize_safe (m n m' n' : nat) : Prop := m = m' /\ n = n'.
Transparent resize.

Definition ket0 : Matrix 2 1:= 
  fun x y => match x, y with 
          | 0, 0 => 1
          | 1, 0 => 0
          | _, _ => 0
          end.
Definition ket1 : Matrix 2 1 := 
  fun x y => match x, y with 
          | 0, 0 => 0
          | 1, 0 => 1
          | _, _ => 0
          end.

Definition ket (x : nat) : Matrix 2 1 := if x =? 0 then ket0 else ket1.
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

Definition hadamard : Matrix 2 2 := 
  (fun x y => match x, y with
          | 0, 0 => (1 / √2)
          | 0, 1 => (1 / √2)
          | 1, 0 => (1 / √2)
          | 1, 1 => -(1 / √2)
          | _, _ => 0
          end).

Fixpoint hadamard_k (k : nat) : Matrix (2^k) (2^k):= 
  match k with
  | 0 => Id 1
  | S k' => hadamard ⊗ hadamard_k k'
  end. 

Lemma hadamard_1 : hadamard_k 1 = hadamard.
Proof. apply kron_1_r. Qed.

(* Alternative definitions:
Definition pauli_x : Matrix 2 2 := fun x y => if x + y =? 1 then 1 else 0.
Definition pauli_y : Matrix 2 2 := fun x y => if x + y =? 1 then (-1) ^ x * Ci else 0.
Definition pauli_z : Matrix 2 2 := fun x y => if (x =? y) && (x <? 2) 
                                           then (-1) ^ x * Ci else 0.
*)

Definition pauli_x : Matrix 2 2 := 
  (fun x y => match x, y with
          | 0, 0 => 0
          | 0, 1 => 1
          | 1, 0 => 1
          | 1, 1 => 0
          | _, _ => 0
          end).

Definition pauli_y : Matrix 2 2 := 
  (fun x y => match x, y with
          | 0, 1 => -Ci
          | 1, 0 => Ci
          | _, _ => 0
          end).

Definition pauli_z : Matrix 2 2 := 
  (fun x y => match x, y with
          | 0, 0 => 1
          | 1, 1 => -1
          | _, _ => 0
          end).
  
Definition control {n : nat} (A : Matrix n n) : Matrix (2*n) (2*n) :=
  (fun x y => if (x <? n) && (y <? n) then (Id n) x y 
          else if (n <=? x) && (n <=? y) then A (x-n)%nat (y-n)%nat 
          else 0).

(* Definition cnot := control pauli_x. *)
(* Direct definition makes our lives easier *)
Definition cnot : Matrix 4 4 :=
  fun x y => match x, y with 
          | 0, 0 => 1
          | 1, 1 => 1
          | 2, 3 => 1
          | 3, 2 => 1
          | _, _ => 0
          end.          


(* Swap Matrices *)

Definition swap : Matrix 4 4 :=
  (fun x y => match x, y with
          | 0, 0 => 1
          | 1, 2 => 1
          | 2, 1 => 1
          | 3, 3 => 1
          | _, _ => 0
          end).

(* Rotation Matrices (theta, phi, lambda) := Rz(phi) Ry(theta) Rz(lambda) *)

Definition rotation (theta phi lambda : R) : Matrix 2 2 :=
  (fun x y => match x, y with
        | 0, 0 => (cos((phi + lambda) / 2) - Ci * sin((phi + lambda) / 2)) * cos (theta / 2)
        | 0, 1 => -(cos((phi - lambda) / 2) - Ci * sin((phi - lambda) / 2)) * sin (theta / 2)
        | 1, 0 => (cos((phi - lambda) / 2) + Ci * sin((phi - lambda) / 2)) * sin (theta / 2)
        | 1, 1 => (cos((phi + lambda) / 2) + Ci * sin((phi + lambda) / 2)) * cos (theta / 2)
        | _, _ => 0
        end).

(* Does this overwrite the other Hint DB M? *)
Hint Unfold ket0 ket1 hadamard pauli_x pauli_y pauli_z control cnot swap : M_db.

Lemma double_mult : forall (n : nat), (n + n = 2 * n)%nat. Proof. intros. omega. Qed.
Lemma pow_two_succ_l : forall x, (2^x * 2 = 2 ^ (x + 1))%nat.
Proof. intros. rewrite mult_comm. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma pow_two_succ_r : forall x, (2 * 2^x = 2 ^ (x + 1))%nat.
Proof. intros. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma double_pow : forall (n : nat), (2^n + 2^n = 2^(n+1))%nat. 
Proof. intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity. Qed.
Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> (a^m = b^n)%nat.
Proof. intuition. Qed.

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
  end.

(* The input k is really k+1, to appease to Coq termination gods *)
(* NOTE: Check that the offsets are right *)
(* Requires: i + 1 < n *)
Fixpoint swap_to_0_aux (n i : nat) {struct i} : Matrix (2^n) (2^n) := 
  match i with
  | O => swap ⊗ Id (2^(n-2))
  | S i' =>  (Id (2^i') ⊗ swap ⊗ Id (2^(n-i'-2))) × (* swap i-1 with i *)
            swap_to_0_aux n i' × 
            (Id (2^i') ⊗ swap ⊗ Id (2^(n-i'-2))) (* swap i-1 with 0 *)
  end.

(* Requires: i < n *)
Definition swap_to_0 (n i : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => Id (2^n) 
  | S i' => swap_to_0_aux n i'
  end.
 
(* Requires i < j, j < n *)
Fixpoint swap_two_aux (n i j : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => swap_to_0 n j 
  | S i' => Id 2 ⊗ swap_two_aux (n-1) (i') (j-1)
  end.

(* Requires i < n, j < n *)
Definition swap_two (n i j : nat) : Matrix (2^n) (2^n) :=
  if i =? j then Id (2^n) 
  else if i <? j then swap_two_aux n i j
  else swap_two_aux n j i.

(* Simpler version of swap_to_0 that shifts other elements *)
(* Requires: i+1 < n *)
Fixpoint move_to_0_aux (n i : nat) {struct i}: Matrix (2^n) (2^n) := 
  match i with
  | O => swap ⊗ Id (2^(n-2))
  | S i' =>  (resize (2^i' * 4 * 2^(n-i'-2)) (2^i' * 4 * 2^(n-i'-2)) (2^n) (2^n) 
             (Id (2^i') ⊗ swap ⊗ Id (2^(n-i'-2)))) × swap_to_0_aux n i
  end.

Lemma move_to_0_aux_safe : forall (i' n : nat), (i'+2 < n)%nat -> 
  resize_safe (2^i' * 4 * 2^(n-i'-2)) (2^i' * 4 * 2^(n-i'-2)) (2^n) (2^n).
Proof. intros. unfold resize_safe. split; unify_pows_two. Qed.
             
(* Requires: i < n *)
Definition move_to_0 (n i : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => Id (2^n) 
  | S i' => move_to_0_aux n i'
  end.
 
(* Always moves up in the matrix from i to k *)
(* Requires: k < i < n *)
Fixpoint move_to (n i k : nat) : Matrix (2^n) (2^n) := 
  match k with 
  | O => move_to_0 n i 
  | S k' => Id 2 ⊗ move_to (n-1) (i-1) (k')
  end.

Lemma swap_two_base : swap_two 2 1 0 = swap.
Proof. unfold swap_two. simpl. apply kron_1_r. Qed.

Lemma swap_second_two : swap_two 3 1 2 = Id 2 ⊗ swap.
Proof. unfold swap_two.
       simpl.
       rewrite kron_1_r.
       reflexivity.
Qed.

(*
Eval compute in ((swap_two 1 0 1) 0 0)%nat.
Eval compute in (print_matrix (swap_two 1 0 2)).
*)

(** Well Formedness of Quantum States and Unitaries **)

Lemma WF_bra0 : WF_Matrix 1 2 ⟨0|. Proof. show_wf. Qed.
Lemma WF_bra1 : WF_Matrix 1 2 ⟨1|. Proof. show_wf. Qed.
Lemma WF_ket0 : WF_Matrix 2 1 |0⟩. Proof. show_wf. Qed.
Lemma WF_ket1 : WF_Matrix 2 1 |1⟩. Proof. show_wf. Qed.
Lemma WF_braket0 : WF_Matrix 2 2 |0⟩⟨0|. Proof. show_wf. Qed.
Lemma WF_braket1 : WF_Matrix 2 2 |1⟩⟨1|. Proof. show_wf. Qed.

Hint Resolve WF_bra0 WF_bra1 WF_ket0 WF_ket1 WF_braket0 WF_braket1 : wf_db.

Lemma WF_hadamard : WF_Matrix 2 2 hadamard. Proof. show_wf. Qed.
Lemma WF_pauli_x : WF_Matrix 2 2 pauli_x. Proof. show_wf. Qed.
Lemma WF_pauli_y : WF_Matrix 2 2 pauli_y. Proof. show_wf. Qed.
Lemma WF_pauli_z : WF_Matrix 2 2 pauli_z. Proof. show_wf. Qed.
Lemma WF_cnot : WF_Matrix 4 4 cnot. Proof. show_wf. Qed.
Lemma WF_swap : WF_Matrix 4 4 swap. Proof. show_wf. Qed.

Lemma WF_rotation : forall (t p l : R), WF_Matrix 2 2 (rotation t p l).
Proof.
  intros t p l x y H1. destruct H1 as [H2 | H2].
  - destruct H2 eqn:Hx.
    + reflexivity.
    + simpl. destruct m eqn:Heqm.
      * inversion H2. inversion H0.
      * reflexivity. 
  - destruct x eqn:Hx.
    + destruct H2 eqn:Hy.
      * reflexivity.
      * simpl. destruct m; [inversion g | reflexivity].
    + destruct H2 eqn:Hy.
      * destruct n; reflexivity.
      * destruct n; try reflexivity.
        destruct m; [inversion g | reflexivity].
Qed.

Lemma WF_control : forall (n m : nat) (U : Matrix n n), 
      (m = 2 * n)%nat ->
      WF_Matrix n n U -> WF_Matrix m m (control U).
Proof.
  intros n m U E WFU. subst.
  unfold control, WF_Matrix in *.
  intros x y [Hx | Hy]; simpl.
  + replace (x <? n) with false by (symmetry; apply Nat.ltb_ge; omega). simpl.
    rewrite WFU.
    * destruct (n <=? x), (n <=? y); reflexivity.
    * left. omega. 
  + replace (y <? n) with false by (symmetry; apply Nat.ltb_ge; omega). 
    rewrite andb_false_r.
    rewrite WFU.
    * destruct (n <=? x), (n <=? y); reflexivity.
    * right. omega.
Qed.

Hint Resolve WF_hadamard WF_pauli_x WF_pauli_y WF_pauli_z WF_cnot WF_swap 
             WF_rotation WF_control : wf_db.

(** Unitaries are unitary **)

Definition is_unitary {n: nat} (U : Matrix n n): Prop :=
  WF_Matrix n n U /\ U † × U = Id n.

Hint Unfold is_unitary : M_db.

(* More precise *)
(* Definition unitary_matrix' {n: nat} (A : Matrix n n): Prop := Minv A A†. *)

Lemma H_unitary : is_unitary hadamard.
Proof.
  split.
  show_wf.
  unfold Mmult, Id.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try Csolve.
  simpl.
  replace ((S (S x) <? 2)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma σx_unitary : is_unitary pauli_x.
Proof. 
  split.
  show_wf.
  unfold Mmult, Id.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try Csolve.
  simpl.
  replace ((S (S x) <? 2)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma σy_unitary : is_unitary pauli_y.
Proof.
  split.
  show_wf.
  unfold Mmult, Id.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try Csolve.
  simpl.
  replace ((S (S x) <? 2)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma σz_unitary : is_unitary pauli_z.
Proof.
  split.
  show_wf.
  unfold Mmult, Id.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try Csolve.
  simpl.
  replace ((S (S x) <? 2)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma control_unitary : forall n (A : Matrix n n), 
                          is_unitary A -> is_unitary (control A). 
Proof.
  intros n A.
  split.
  destruct H; auto with wf_db.
  induction n.
  + unfold control, is_unitary, conj_transpose, Mmult, Id.
    prep_matrix_equality.
    replace (x <? 0) with false by reflexivity.
    rewrite andb_false_r.
    reflexivity.
  + unfold control, is_unitary, Mmult, Id.
    prep_matrix_equality.    
    simpl.

(*
  intros.
  unfold control.
  prep_matrix_equality.
  unfold conj_transpose, Mmult, Id in *.
  destruct (x <? n) eqn:Ltxn, (y <? n) eqn:Ltyn.
  simpl.
*)    

Admitted.

Lemma transpose_unitary : forall n (A : Matrix n n), is_unitary A -> is_unitary (A†).
  intros. 
  simpl.
  split.
  + destruct H; auto with wf_db.
  + unfold is_unitary in *.
    rewrite conj_transpose_involutive.
    destruct H as [_ H].
    apply Minv_left in H as [_ S]. (* NB: Admitted lemma *)
    assumption.
Qed.

Lemma cnot_unitary : is_unitary cnot.
Proof.
  split. 
  apply WF_cnot.
  unfold Mmult, Id.
  prep_matrix_equality.
  do 4 (try destruct x; try destruct y; try clra).
  replace ((S (S (S (S x))) <? 4)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma id_unitary : forall n, is_unitary (Id n). 
Proof.
  split.
  apply WF_Id.
  unfold is_unitary.
  rewrite id_conj_transpose_eq.
  apply Mmult_1_l.
  apply WF_Id.
Qed.

Lemma swap_unitary : is_unitary swap.
Proof. 
  split.
  apply WF_swap.
  unfold is_unitary, Mmult, Id.
  prep_matrix_equality.
  do 4 (try destruct x; try destruct y; try clra).
  replace ((S (S (S (S x))) <? 4)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma rotation_unitary : forall (t p l : R), is_unitary (rotation t p l).
Proof.
  split.
  show_wf.
  unfold Mmult, Id, rotation.
  prep_matrix_equality.
  destruct x as [| [|x]].
  - destruct y as [|[|y]].
    + Admitted.
  
Lemma kron_unitary : forall {m n} (A : Matrix m m) (B : Matrix n n),
  is_unitary A -> is_unitary B -> is_unitary (A ⊗ B).
Admitted.

Lemma unitary_swap_to_0 : forall n i, (i < n)%nat -> is_unitary (swap_to_0 n i).
Proof.
  intros n i.
  generalize dependent n.
  unfold is_unitary; split.
  + (* well-formedness *)
    induction i. 
    simpl. auto with wf_db.     
    simpl in *.
    unfold swap_to_0 in IHi.
    destruct i; simpl in *.
    - specialize Nat.pow_nonzero; intros NZ.
      replace (2 ^ n)%nat with (4 * 2^(n-2))%nat by unify_pows_two.
      auto with wf_db.
    - specialize Nat.pow_nonzero; intros NZ.
      replace (2^n)%nat with  (2 ^ i * 4 * 2 ^ (n - i - 2))%nat by unify_pows_two.
      auto with wf_db.
      apply WF_mult; auto with wf_db.
      apply WF_mult; auto with wf_db.
      replace (2 ^ i * 4 * 2 ^ (n - i - 2))%nat with (2^n)%nat by unify_pows_two.
      apply IHi.
      omega.
  + induction i; simpl.
    - apply id_unitary.
    - unfold swap_to_0 in IHi. 
      destruct i.
      * simpl.
        remember ( Id (2 ^ (n - 2))) as A.
        remember swap as B.
        setoid_rewrite (kron_conj_transpose _ _ _ _ B A).            
    
(*    rewrite (kron_mixed_product B† A† B A). *)

        specialize (kron_mixed_product _ _ _ _ _ _ B† A† B A); intros H'.
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

Lemma unitary_swap_two : forall n i j, (i < n)%nat -> (j < n)%nat ->
                                  is_unitary (swap_two n i j).
Proof.
  intros n i j P1 P2.
  unfold is_unitary.
  unfold swap_two.
  destruct (lt_eq_lt_dec i j) as [[ltij | eq] | ltji].
  + induction i.
    simpl.
Admitted.

(* Our unitaries are self-adjoint *)

Definition id_sa := id_conj_transpose_eq.

Lemma hadamard_sa : hadamard† = hadamard.
Proof.
  prep_matrix_equality.
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma pauli_x_sa : pauli_x† = pauli_x.
Proof. 
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma pauli_y_sa : pauli_y† = pauli_y.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma pauli_z_sa : pauli_z† = pauli_z.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma cnot_sa : cnot† = cnot.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma swap_sa : swap† = swap.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma control_sa : forall (n : nat) (A : Square n), 
    A† = A -> (control A)† = (control A).
Proof.
  intros n A H.
  prep_matrix_equality.
  autounfold with M_db in *.
  autounfold with M_db in *.
  bdestruct (x =? y); bdestruct (y =? x); 
  bdestruct (y <? n); bdestruct (x <? n); 
  bdestruct (n <=? y); bdestruct (n <=? x); 
    try omega; simpl; try clra.
  subst. 
  (* ah, rewriting at X *)
  remember (Cconj (A (y - n)%nat (y - n)%nat)) as L.
  rewrite <- H. subst.
  reflexivity.
  remember (Cconj (A (y - n)%nat (x - n)%nat)) as L. (* oh hackyness *)
  rewrite <- H. subst.
  reflexivity.
Qed.  

Lemma braket0_sa : |0⟩⟨0|† = |0⟩⟨0|. Proof. mlra. Qed.
Lemma braket1_sa : |1⟩⟨1|† = |1⟩⟨1|. Proof. mlra. Qed.

Hint Rewrite hadamard_sa pauli_x_sa pauli_y_sa pauli_z_sa cnot_sa swap_sa 
             braket1_sa braket0_sa : M_db.

Hint Rewrite control_sa using (autorewrite with M_db; reflexivity) : M_db.


(* Pure and Mixed States *)

(* Wiki:
In operator language, a density operator is a positive semidefinite, hermitian 
operator of trace 1 acting on the state space. A density operator describes 
a pure state if it is a rank one projection. Equivalently, a density operator ρ 
describes a pure state if and only if ρ = ρ ^ 2 *)

(* We need an additional restriction that trace = 1 to
   exclude the identity and zero matrices. *)

Notation Density n := (Matrix n n) (only parsing). 

Definition Pure_State {n} (ρ : Density n) : Prop := 
  WF_Matrix n n ρ /\ trace ρ = 1 /\ ρ = ρ × ρ.

Lemma pure0 : Pure_State |0⟩⟨0|. 
Proof. split; [|split]; [auto with wf_db| clra |mlra]. Qed.
Lemma pure1 : Pure_State |1⟩⟨1|. 
Proof. split; [|split]; [auto with wf_db| clra |mlra]. Qed.

(* Wiki:
For a finite-dimensional function space, the most general density operator 
is of the form:

  ρ =∑_j p_j |ψ_j⟩⟨ ψ_j| 

where the coefficients p_j are non-negative and add up to one. *)

Inductive Mixed_State {n} : (Matrix n n) -> Prop :=
| Pure_S : forall ρ, Pure_State ρ -> Mixed_State ρ
| Mix_S : forall (p : R) ρ1 ρ2, 0 < p < 1 -> Mixed_State ρ1 -> Mixed_State ρ2 ->
                                        Mixed_State (p .* ρ1 .+ (1-p)%R .* ρ2).  

Lemma WF_Pure : forall {n} (ρ : Density n), Pure_State ρ -> WF_Matrix n n ρ.
Proof. unfold Pure_State. intuition. Qed.
Hint Resolve WF_Pure : wf_db.
Lemma WF_Mixed : forall {n} (ρ : Density n), Mixed_State ρ -> WF_Matrix n n ρ.
Proof. induction 1; auto with wf_db. Qed.
Hint Resolve WF_Mixed : wf_db.

(** Density matrices and superoperators **)

Definition Superoperator m n := Density m -> Density n.

Definition WF_Superoperator {m n} (f : Superoperator m n) := 
  (forall ρ, Mixed_State ρ -> Mixed_State (f ρ)).   

(* Transparent Density. *)

Definition super {m n} (M : Matrix m n) : Superoperator n m := fun ρ => 
  M × ρ × M†.

Definition compose_super {m n p} (g : Superoperator n p) (f : Superoperator m n)
                      : Superoperator m p :=
  fun ρ => g (f ρ).
Lemma compose_super_correct : forall {m n p} 
                              (g : Superoperator n p) (f : Superoperator m n),
      WF_Superoperator g -> WF_Superoperator f ->
      WF_Superoperator (compose_super g f).
Proof.
  intros m n p g f pf_g pf_f.
  unfold WF_Superoperator.
  intros ρ mixed.
  unfold compose_super.
  apply pf_g. apply pf_f. auto.
Qed.

Definition sum_super {m n} (f g : Superoperator m n) : Superoperator m n :=
  fun ρ => (1/2)%R .* f ρ .+ (1 - 1/2)%R .* g ρ.
Lemma WF_sum_super : forall m n (f g : Superoperator m n),
      WF_Superoperator f -> WF_Superoperator g -> WF_Superoperator (sum_super f g).
Proof.
  intros m n f g wf_f wf_g ρ pf_ρ.
  unfold sum_super. 
  set (wf_f' := wf_f _ pf_ρ).
  set (wf_g' := wf_g _ pf_ρ).
  apply (Mix_S (1/2) (f ρ) (g ρ)); auto. Rsolve.
Qed.
  

(* To do: correctness conditions for density matrices and superoperators *)
(* NOTE: I think these all need fixing *)


Definition new0_op : Superoperator 1 2 := super |0⟩.
Definition new1_op : Superoperator 1 2 := super |1⟩.
Definition meas_op : Superoperator 2 2 := fun ρ => super |0⟩⟨0| ρ .+ super |1⟩⟨1| ρ.
Definition discard_op : Superoperator 2 1 := fun ρ => super ⟨0| ρ .+ super ⟨1| ρ.

Lemma pure_unitary : forall {n} (U ρ : Matrix n n), 
  is_unitary U -> Pure_State ρ -> Pure_State (super U ρ).
Proof.
  intros n U ρ [WFU H] [WFρ [trP P]].
  unfold Pure_State, is_unitary, super in *.
  split; [|split].
  + auto with wf_db.
  + (* I don't actually know how to prove this *)
    rewrite P.
    autounfold with M_db; simpl.
    admit.
  + remember (U × ρ × (U) † × (U × ρ × (U) †)) as rhs.
    rewrite P.
    replace (ρ × ρ) with (ρ × Id n × ρ) by (rewrite Mmult_1_r; trivial).
    rewrite <- H.
    rewrite Heqrhs.
    repeat rewrite Mmult_assoc. (* Admitted lemma *)
    reflexivity.
Admitted.

Lemma pure_hadamard_1 : Pure_State (super hadamard |1⟩⟨1|).
Proof. apply pure_unitary. 
       + apply H_unitary.       
       + apply pure1. 
Qed.

Definition dm12 : Matrix 2 2 :=
  (fun x y => match x, y with
          | 0, 0 => 1 / 2
          | 0, 1 => 1 / 2
          | 1, 0 => 1 / 2
          | 1, 1 => 1 / 2
          | _, _ => 0
          end).

Lemma pure_dm12 : Pure_State dm12. Proof.
  split; [|split].
  show_wf.
  unfold dm12; simpl; clra. 
  unfold dm12, conj_transpose, super, Mmult.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; clra.
Qed.

Lemma mixed_meas_12 : Mixed_State (meas_op dm12).
Proof. unfold meas_op. 
       replace (super |0⟩⟨0| dm12) with ((1/2)%R .* |0⟩⟨0|) 
         by (unfold dm12, super; mlra).
       replace (super |1⟩⟨1| dm12) with ((1 - 1/2)%R .* |1⟩⟨1|) 
         by (unfold dm12, super; mlra).
       apply Mix_S.
       lra.
       constructor; split; [|split]; [auto with wf_db|clra|mlra].
       constructor; split; [|split]; [auto with wf_db|clra|mlra].
Qed.

Lemma mixed_unitary : forall {n} (U ρ : Matrix n n), 
  WF_Matrix n n U -> is_unitary U -> Mixed_State ρ -> Mixed_State (super U ρ).
Proof.
  intros n U ρ WFU H M.
  induction M.
  + apply Pure_S.
    apply pure_unitary; trivial.
  + unfold is_unitary, super in *.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    rewrite 2 Mscale_mult_dist_r.
    rewrite 2 Mscale_mult_dist_l.
    apply Mix_S; trivial.
Qed.

Lemma mixed_state_trace_1 : forall {n} (ρ : Density n), Mixed_State ρ -> trace ρ = 1.
Proof.
  intros.
  induction H.
  + unfold Pure_State in H; intuition.
  + (* Needs two lemmas we didn't prove in Matrix.v *)
    Lemma trace_plus_dist : forall n (A B : Square n), trace (A .+ B) = trace A + trace B. 
    Admitted.
    Lemma trace_mult_dist : forall n p (A : Square n), trace (p .* A) = p * trace A. 
    Admitted.
    rewrite trace_plus_dist.
    rewrite 2 trace_mult_dist.
    rewrite IHMixed_State1, IHMixed_State2.
    clra.
Qed.

Lemma pure_state_id1 : forall (ρ : Square 1), Pure_State ρ -> ρ = Id 1.
Proof.
  intros ρ [WFP [TRP PPP]].
  prep_matrix_equality.
  destruct x.
  destruct y.  
  + unfold trace in TRP; simpl in TRP.
    rewrite Cplus_0_l in TRP.
    rewrite TRP; reflexivity.
  + rewrite WFP, WF_Id; trivial; omega.
  + rewrite WFP, WF_Id; trivial; omega.
Qed.    

Lemma mixed_state_id1 : forall (ρ : Square 1), Mixed_State ρ -> ρ = Id 1.
Proof.
  intros.  
  induction H.
  + apply pure_state_id1; trivial.
  + rewrite IHMixed_State1, IHMixed_State2.
    prep_matrix_equality.
    clra.
Qed.  
(* *)