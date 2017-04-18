Require Import Program.
Require Import Psatz.
Require Import Omega.
Require Import Reals.
Require Import Bool.
Require Export Coquelicot.Complex.
Require Export UMatrix.

(* Using our (complex, unbounded) matrices, their complex numbers *)

Open Scope R_scope.
Open Scope C_scope.
Open Scope matrix_scope.

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

(*
Lemma hadamard_1 : hadamard_k 1 = hadamard.
Proof. apply kron_1_r. Qed.
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

Definition cnot := control pauli_x.
          

(* Swap Matrices *)

Definition swap : Matrix 4 4 :=
  (fun x y => match x, y with
          | 0, 0 => 1
          | 1, 2 => 1
          | 2, 1 => 1
          | 3, 3 => 1
          | _, _ => 0
          end).

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

Local Obligation Tactic := program_simpl; unify_pows_two; try omega.

(* The input k is really k+1, to appease to Coq termination gods *)
(* NOTE: Check that the offsets are right *)
Program Fixpoint swap_to_0' (n i : nat) {pf : lt (i+1) n} {struct i}
        : Matrix (2^n) (2^n) := 
  match i with
  | O => swap ⊗ Id (2^(n-2))
  | S i' =>  (Id (2^i') ⊗ swap ⊗ Id (2^(n-i'-2))) × (* swap i-1 with i *)
            swap_to_0' n i' × 
            (Id (2^i') ⊗ swap ⊗ Id (2^(n-i'-2))) (* swap i-1 with 0 *)
  end.

Program Definition swap_to_0 (n i : nat) {pf : lt i n} : Matrix (2^n) (2^n) := 
  match i with 
  | O => Id (2^n) 
  | S i' => @swap_to_0' n i' _
  end.
 
(* Requires i < j *)
Program Fixpoint swap_two' (n i j : nat) {ltij : lt i j} {ltjn : lt j n} : Matrix (2^n) (2^n) := 
  match i with 
  | O => swap_to_0 n j 
  | S i' => Id 2 ⊗ swap_two' (n-1) (i') (j-1)
  end.

Definition swap_two (n i j : nat) {ltin : lt i n} {ltjn : lt j n} : Matrix (2^n) (2^n).
  destruct (lt_eq_lt_dec i j) as [[ltij | eq] | ltji].
  exact (@swap_two' n i j ltij ltjn).
  exact (Id (2^n)).
  exact (@swap_two' n j i ltji ltin).
Defined.

(* Simpler version of swap_to_0 that shifts other elements *)
Program Fixpoint move_to_0' (n i : nat) {pf : lt (i+1) n} {struct i}: Matrix (2^n) (2^n) := 
  match i with
  | O => swap ⊗ Id (2^(n-2))
  | S i' =>  (Id (2^i') ⊗ swap ⊗ Id (2^(n-i'-2))) × swap_to_0' n i
  end.

Program Definition move_to_0 (n i : nat) {pf : lt i n} : Matrix (2^n) (2^n) := 
  match i with 
  | O => Id (2^n) 
  | S i' => @move_to_0' n i' _
  end.
 
(* Always moves up in the matrix from i to k *)
Program Fixpoint move_to (n i k : nat) {ltij : lt k i} {ltjn : lt i n} : Matrix (2^n) (2^n) := 
  match k with 
  | O => move_to_0 n i 
  | S k' => Id 2 ⊗ move_to (n-1) (i-1) (k')
  end.

Program Definition lt02 : (0 < 2)%nat := _. 
Program Definition lt12 : (1 < 2)%nat := _. 
Program Definition lt13 : (1 < 3)%nat := _. 
Program Definition lt23 : (2 < 3)%nat := _. 

Lemma swap_two_base : @swap_two 2 1 0 lt12 lt02 = swap.
Proof. unfold swap_two. simpl. apply kron_1_r. Qed.

Lemma swap_second_two : @swap_two 3 1 2 lt13 lt23 = Id 2 ⊗ swap.
Proof. unfold swap_two.
       simpl.
       rewrite kron_1_r.
       reflexivity.
Qed.

(* Works!
Eval compute in ((swap_two 1 0 1) 0 0)%nat.
Eval compute in (print_matrix (swap_two 1 0 2)).
*)

(** Unitaries are well-formed **)

Lemma WF_hadamard : WF_Matrix hadamard. Proof. show_wf. Qed.
Lemma WF_pauli_x : WF_Matrix pauli_x. Proof. show_wf. Qed.
Lemma WF_pauli_y : WF_Matrix pauli_y. Proof. show_wf. Qed.
Lemma WF_pauli_z : WF_Matrix pauli_z. Proof. show_wf. Qed.

Lemma WF_control : forall {n} (U : Matrix n n), WF_Matrix U -> WF_Matrix (control U).
Proof.
  intros n U WFU.
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

(** Unitaries are unitary **)

Definition unitary_matrix {n: nat} (A : Matrix n n): Prop :=
  A† × A = Id n.

(* More precise *)
Definition unitary_matrix' {n: nat} (A : Matrix n n): Prop := Minv A A†.

Lemma H_unitary : unitary_matrix hadamard.
Proof.
  unfold unitary_matrix, Minv, Mmult, Id.
  prep_matrix_equality.
  simpl.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try Csolve.
  replace ((S (S x) <? 2)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma σx_unitary : unitary_matrix pauli_x.
Proof. 
  unfold unitary_matrix, Mmult, Id.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try clra.
  replace ((S (S x) <? 2)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma σy_unitary : unitary_matrix pauli_y.
Proof.
  unfold unitary_matrix, Mmult, Id.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try clra.
  replace ((S (S x) <? 2)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma σz_unitary : unitary_matrix pauli_z.
Proof.
  unfold unitary_matrix, Mmult, Id.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try clra.
  replace ((S (S x) <? 2)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma control_unitary : forall n (A : Matrix n n), 
                          unitary_matrix A -> unitary_matrix (control A). 
Proof.
  intros n A. 
  induction n.
  + intros H.
    unfold control, unitary_matrix, conj_transpose, Mmult, Id.
    prep_matrix_equality.
    replace (x <? 0) with false by reflexivity.
    rewrite andb_false_r.
    reflexivity.
  + intros H.
    unfold control, unitary_matrix, Mmult, Id.
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

Lemma cnot_unitary : unitary_matrix cnot.
Proof.
  unfold unitary_matrix, Mmult, Id.
  prep_matrix_equality.
  do 4 (try destruct x; try destruct y; try clra).
  replace ((S (S (S (S x))) <? 4)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma id_unitary : forall n, unitary_matrix (Id n). 
Proof.
  intros n.
  unfold unitary_matrix.
  rewrite id_conj_transpose_eq.
  apply Mmult_1_l.
  apply WF_Id.
Qed.

Lemma swap_unitary : unitary_matrix swap.
Proof. 
  unfold unitary_matrix, Mmult, Id.
  prep_matrix_equality.
  do 4 (try destruct x; try destruct y; try clra).
  replace ((S (S (S (S x))) <? 4)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.


Lemma kron_unitary : forall {m n} (A : Matrix m m) (B : Matrix n n),
  unitary_matrix A -> unitary_matrix B -> unitary_matrix (A ⊗ B).
Admitted.

Lemma unitary_swap_to_0 : forall n i P, unitary_matrix (@swap_to_0 n i P).
Proof.
  intros n i P.
  generalize dependent n.
  unfold unitary_matrix.
  induction i; intros n P; simpl.
  + apply id_unitary.
  + unfold swap_to_0 in IHi. 
    destruct i.
    - simpl.
      remember ( Id (2 ^ (n - 2))) as A.
      remember swap as B.

      setoid_rewrite (kron_conj_transpose B A).
(*    rewrite (kron_mixed_product B† A† B A). *)

      specialize (kron_mixed_product B† A† B A); intros H.
      assert (unitary_matrix B). subst. apply swap_unitary.
      assert (unitary_matrix A). subst. apply id_unitary.
      rewrite H0 in H.
      rewrite H1 in H.
      replace (Id (2 ^ n)) with (Id 4 ⊗ Id (2 ^ (n - 2))).
      (* apply H doesn't work. 
         Surprisingly, that's the matrix types failing to line up *)
      rewrite <- H.
      replace (Init.Nat.mul (S (S (S (S O))))
       (Nat.pow (S (S O)) (Init.Nat.sub n (S (S O))))) 
              with
              (Nat.pow (S (S O)) n).
      reflexivity.

      destruct n; try omega.
      destruct n; try omega.
      simpl. repeat rewrite plus_0_r, Nat.sub_0_r. omega.

      replace (2 ^ n)%nat with (4 * 2^(n-2))%nat.
      apply id_kron.
      
      specialize (id_kron 4 (2 ^ (n - 2))); intros Eq.
      destruct n; try omega.
      destruct n; try omega.
      simpl. repeat rewrite plus_0_r, Nat.sub_0_r. omega.
    - 
      simpl.
Admitted.

Lemma unitary_swap_two : forall n i j P1 P2, unitary_matrix (@swap_two n i j P1 P2).
Proof.
  intros n i j P1 P2.
  unfold unitary_matrix.
  unfold swap_two.
  destruct (lt_eq_lt_dec i j) as [[ltij | eq] | ltji].
  + induction i.
    simpl.
Admitted.

(** Density matrices and superoperators **)

Notation Density n := (Matrix n n) (only parsing). 
Definition Superoperator m n := Density m -> Density n.

(* Transparent Density. *)

Definition super {m n} (M : Matrix m n) : Superoperator n m := fun ρ => 
  M × ρ × M†.

(* To do: correctness conditions for density matrices and superoperators *)
(* NOTE: I think these all need fixing *)


Definition new0_op : Superoperator 1 2 := super |0⟩.
Definition new1_op : Superoperator 1 2 := super |1⟩.
Definition meas_op : Superoperator 2 2 := fun ρ => super |0⟩⟨0| ρ .+ super |1⟩⟨1| ρ.
Definition discard_op : Superoperator 2 1 := fun ρ => super ⟨0| ρ .+ super ⟨1| ρ.


(* Pure and Mixed States *)

(* Wiki:
In operator language, a density operator is a positive semidefinite, hermitian 
operator of trace 1 acting on the state space. A density operator describes 
a pure state if it is a rank one projection. Equivalently, a density operator ρ 
describes a pure state if and only if ρ = ρ ^ 2 *)

Definition Pure_State {n} (ρ : Density n) : Prop := WF_Matrix ρ /\ ρ = ρ × ρ.

Lemma pure0 : Pure_State |0⟩⟨0|. Proof. split; [show_wf|mlra]. Qed.
Lemma pure1 : Pure_State |1⟩⟨1|. Proof. split; [show_wf|mlra]. Qed.

(* Very simple version of a general lemma saying that all unitaries map pure states
   to pure states *)
(* Takes forever. Msolve *can* solve this, but it takes 2^forever. *)
(*
Lemma pure_hadamard_0 : Pure_State (super hadamard |0⟩⟨0|).
Proof. 
  unfold Pure_State, hadamard, ket0, conj_transpose, super, Mmult.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  destruct x as [| [|x]]; destruct y as [|[|y]]; Csolve.
Qed.
*)

(*  Less slow, but slow:
Lemma pure_σx_1 : Pure_State (super pauli_x |0⟩⟨0|). Proof. mlra. Qed.
Lemma pure_σy_1 : Pure_State (super pauli_y |0⟩⟨0|). Proof. mlra. Qed.
Lemma pure_σz_1 : Pure_State (super pauli_z |0⟩⟨0|). Proof. mlra. Qed.
*)

Lemma pure_unitary : forall {n} (U ρ : Matrix n n), 
  WF_Matrix U -> unitary_matrix U -> Pure_State ρ -> Pure_State (super U ρ).
Proof.
  intros n U ρ WFU H [WFρ P].
  unfold Pure_State, unitary_matrix, super in *.
  split.
  show_wf.
  remember (U × ρ × (U) † × (U × ρ × (U) †)) as rhs.
  rewrite P.
  replace (ρ × ρ) with (ρ × Id n × ρ) by (rewrite Mmult_1_r; trivial).
  rewrite <- H.
  rewrite Heqrhs.
  repeat rewrite Mmult_assoc. (* Admitted *)
  reflexivity.
Qed.  

Lemma pure_hadamard_1 : Pure_State (super hadamard |1⟩⟨1|).
Proof. apply pure_unitary. 
       + apply WF_hadamard.       
       + apply H_unitary.
       + apply pure1. 
Qed.

(* Wiki:
For a finite-dimensional function space, the most general density operator 
is of the form:

  ρ =∑_j p_j |ψ_j⟩⟨ ψ_j| 

where the coefficients p_j are non-negative and add up to one. *)

Inductive Mixed_State {n} : (Matrix n n) -> Prop :=
| Pure_S : forall ρ, Pure_State ρ -> Mixed_State ρ
| Mix_S : forall (p : R) ρ1 ρ2, 0 < p < 1 -> Mixed_State ρ1 -> Mixed_State ρ2 ->
                                        Mixed_State (p .* ρ1 .+ (1-p)%R .* ρ2).  

Definition dm12 : Matrix 2 2 :=
  (fun x y => match x, y with
          | 0, 0 => 1 / 2
          | 0, 1 => 1 / 2
          | 1, 0 => 1 / 2
          | 1, 1 => 1 / 2
          | _, _ => 0
          end).

Lemma pure_dm12 : Pure_State dm12. Proof.
  split.
  show_wf.
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
       constructor; split; [show_wf|mlra].
       constructor; split; [show_wf|mlra].
Qed.

Lemma mixed_unitary : forall {n} (U ρ : Matrix n n), 
  WF_Matrix U -> unitary_matrix U -> Mixed_State ρ -> Mixed_State (super U ρ).
Proof.
  intros n U ρ WFU H M.
  induction M.
  + apply Pure_S.
    apply pure_unitary; trivial.
  + unfold unitary_matrix, super in *.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    rewrite 2 Mscale_mult_dist_r.
    rewrite 2 Mscale_mult_dist_l.
    apply Mix_S; trivial.
Qed.



(* *)