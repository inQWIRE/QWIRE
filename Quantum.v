Require Import Psatz.
Require Import Reals.

Require Export Prelim.
Require Export Complex.
Require Export Matrix.

(* Using our (complex, unbounded) matrices, their complex numbers *)

Open Scope R_scope.
Open Scope C_scope.
Open Scope matrix_scope.

(*******************************************)
(* Representations of quantum basis states *)
(*******************************************)

Definition ket0 : Matrix 2 1:= 
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 0 => C0
          | _, _ => C0
          end.
Definition ket1 : Matrix 2 1 := 
  fun x y => match x, y with 
          | 0, 0 => C0
          | 1, 0 => C1
          | _, _ => C0
          end.

Notation "|0⟩" := ket0.
Notation "|1⟩" := ket1.
Notation "⟨0|" := ket0†.
Notation "⟨1|" := ket1†.
Notation "|0⟩⟨0|" := (|0⟩×⟨0|).
Notation "|1⟩⟨1|" := (|1⟩×⟨1|).
Notation "|1⟩⟨0|" := (|1⟩×⟨0|).
Notation "|0⟩⟨1|" := (|0⟩×⟨1|).

Definition bra (x : nat) : Matrix 2 1 := if x =? 0 then ⟨0| else ⟨1|.
Definition ket (x : nat) : Matrix 2 1 := if x =? 0 then |0⟩ else |1⟩.

(*                                                      
Notation "'⟨' x '|'" := (bra x). (* Unfortunately, this gives the Coq parser headaches *)
Notation "'|' x '⟩'" := (ket x).
*)
                                                                 
Transparent bra.
Transparent ket.
Transparent ket0.
Transparent ket1.


Definition bool_to_matrix (b : bool) : Matrix 2 2 := if b then |1⟩⟨1| else |0⟩⟨0|.

Definition bool_to_matrix' (b : bool) : Matrix 2 2 := fun x y =>
  match x, y with
  | 0, 0 => if b then 0 else 1
  | 1, 1 => if b then 1 else 0
  | _, _ => 0
  end.  

Definition bool_to_ket (b : bool) : Matrix 2 1 := if b then |1⟩ else |0⟩.
  
Lemma bool_to_matrix_eq : forall b, bool_to_matrix b = bool_to_matrix' b.
Proof. intros. destruct b; simpl; solve_matrix. Qed.

Lemma bool_to_ket_matrix_eq : forall b, outer_product (bool_to_ket b) = bool_to_matrix b.
Proof. unfold outer_product. destruct b; simpl; reflexivity. Qed.

Definition bools_to_matrix (l : list bool) : Square (2^(length l)) := 
  big_kron (map bool_to_matrix l).


(*************)
(* Unitaries *)
(*************)

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

Definition σx : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 1 => C1
          | 1, 0 => C1
          | _, _ => C0
          end.

Definition σy : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 1 => -Ci
          | 1, 0 => Ci
          | _, _ => C0
          end.

Definition σz : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 1 => -C1
          | _, _ => C0
          end.

Definition phase_shift (ϕ : R) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 1 => Cexp ϕ
          | _, _ => C0
          end.
  
Definition control {n : nat} (A : Matrix n n) : Matrix (2*n) (2*n) :=
  fun x y => if (x <? n) && (y =? x) then 1 else 
          if (n <=? x) && (n <=? y) then A (x-n)%nat (y-n)%nat else 0.

(* Definition cnot := control pauli_x. *)
(* Direct definition makes our lives easier *)
Definition cnot : Matrix 4 4 :=
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 1 => C1
          | 2, 3 => C1
          | 3, 2 => C1
          | _, _ => C0
          end.          

Lemma cnot_eq : cnot = control σx.
Proof.
  unfold cnot, control, σx.
  solve_matrix.
Qed.

(* Swap Matrices *)

Definition swap : Matrix 4 4 :=
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 2 => C1
          | 2, 1 => C1
          | 3, 3 => C1
          | _, _ => C0
          end.

(* Does this overwrite the other Hint DB M? *)
Hint Unfold ket0 ket1 hadamard σx σy σz control cnot swap : M_db.

(* Lemmas *)
Lemma MmultX1 : σx × |1⟩ = |0⟩. Proof. solve_matrix. Qed.
Lemma Mmult1X : ⟨1| × σx = ⟨0|. Proof. solve_matrix. Qed.
Lemma MmultX0 : σx × |0⟩ = |1⟩. Proof. solve_matrix. Qed.
Lemma Mmult0X : ⟨0| × σx = ⟨1|. Proof. solve_matrix. Qed.
Hint Rewrite Mmult0X Mmult1X MmultX0 MmultX1 : M_db.

Lemma swap_swap : swap × swap = Id 4. Proof. solve_matrix. Qed.

Lemma swap_swap_r : forall n A, WF_Matrix n 4 A ->
      A × swap × swap = A.
Proof.
  intros.
  rewrite Mmult_assoc.
  rewrite swap_swap. 
  apply Mmult_1_r.
  auto.
Qed.

Hint Rewrite swap_swap swap_swap_r using (auto 100 with wf_db): M_db.



(* The input k is really k+1, to appease to Coq termination gods *)
(* NOTE: Check that the offsets are right *)
(* Requires: i + 1 < n *)
Fixpoint swap_to_0_aux (n i : nat) {struct i} : Matrix (2^n) (2^n) := 
  match i with
  | O => swap ⊗ Id (2^(n-2))
  | S i' =>  (Id (2^i) ⊗ swap ⊗ Id (2^(n-i-2))) × (* swap i-1 with i *)
            swap_to_0_aux n i' × 
            (Id (2^i) ⊗ swap ⊗ Id (2^(n-i-2))) (* swap i-1 with 0 *)
  end.

(* Requires: i < n *)
Definition swap_to_0 (n i : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => Id (2^n) 
  | S i' => swap_to_0_aux n i'
  end.
  
(* Swapping qubits i and j in an n-qubit system, where i < j *) 
(* Requires i < j, j < n *)
Fixpoint swap_two_aux (n i j : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => swap_to_0 n j 
  | S i' => Id 2 ⊗ swap_two_aux (n-1) (i') (j-1)
  end.

(* Swapping qubits i and j in an n-qubit system *)
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
  | S i' => (move_to_0_aux n i') × (Id (2^i) ⊗ swap ⊗ Id (2^(n-i-2))) 
                  
  end.
             
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
Lemma WF_bool_to_ket : forall b, WF_Matrix 2 1 (bool_to_ket b). 
Proof. destruct b; show_wf. Qed.
Lemma WF_bool_to_matrix : forall b, WF_Matrix 2 2 (bool_to_matrix b).
Proof. destruct b; show_wf. Qed.
Lemma WF_bool_to_matrix' : forall b, WF_Matrix 2 2 (bool_to_matrix' b).
Proof. destruct b; show_wf. Qed.

Lemma WF_bools_to_matrix : forall l, 
  WF_Matrix (2^(length l)) (2^(length l))  (bools_to_matrix l).
Proof. 
  induction l; auto with wf_db.
  unfold bools_to_matrix in *; simpl.
  apply WF_kron; try rewrite map_length; try omega.
  apply WF_bool_to_matrix.
  apply IHl.
Qed.

Hint Resolve WF_bra0 WF_bra1 WF_ket0 WF_ket1 WF_braket0 WF_braket1 : wf_db.
Hint Resolve WF_bool_to_ket WF_bool_to_matrix WF_bool_to_matrix' : wf_db.
Hint Resolve WF_bools_to_matrix : wf_db.

Lemma WF_hadamard : WF_Matrix 2 2 hadamard. Proof. show_wf. Qed.
Lemma WF_σx : WF_Matrix 2 2 σx. Proof. show_wf. Qed.
Lemma WF_σy : WF_Matrix 2 2 σy. Proof. show_wf. Qed.
Lemma WF_σz : WF_Matrix 2 2 σz. Proof. show_wf. Qed.
Lemma WF_cnot : WF_Matrix 4 4 cnot. Proof. show_wf. Qed.
Lemma WF_swap : WF_Matrix 4 4 swap. Proof. show_wf. Qed.
Lemma WF_phase : forall ϕ, WF_Matrix 2 2 (phase_shift ϕ). Proof. intros. show_wf. Qed.

Lemma WF_control : forall (n m : nat) (U : Matrix n n), 
      (m = 2 * n)%nat ->
      WF_Matrix n n U -> WF_Matrix m m (control U).
Proof.
  intros n m U E WFU. subst.
  unfold control, WF_Matrix in *.
  intros x y [Hx | Hy];
  bdestruct (x <? n); bdestruct (y =? x); bdestruct (n <=? x); bdestruct (n <=? y);
    simpl; try reflexivity; try omega. 
  all: rewrite WFU; [reflexivity|omega].
Qed.

Hint Resolve WF_hadamard WF_σx WF_σy WF_σz WF_cnot WF_swap WF_phase WF_control : wf_db.

Hint Extern 2 (WF_Matrix 2 2 (phase_shift _)) => apply WF_phase : wf_db.
Hint Extern 2 (WF_Matrix 2 2 (control _)) => apply WF_control : wf_db.

(***************************)
(** Unitaries are unitary **)
(***************************)

Definition WF_Unitary {n: nat} (U : Matrix n n): Prop :=
  WF_Matrix n n U /\ U † × U = Id n.

Hint Unfold WF_Unitary : M_db.

(* More precise *)
(* Definition unitary_matrix' {n: nat} (A : Matrix n n): Prop := Minv A A†. *)

Lemma H_unitary : WF_Unitary hadamard.
Proof.
  split.
  show_wf.
  unfold Mmult, Id.
  prep_matrix_equality.
  autounfold with M_db.
  destruct x as [| [|x]]; destruct y as [|[|y]]; simpl; autorewrite with C_db; 
    try reflexivity.
  replace ((S (S x) <? 2)) with false by reflexivity.
  rewrite andb_false_r.
  reflexivity.
Qed.

Lemma σx_unitary : WF_Unitary σx.
Proof. 
  split.
  show_wf.
  unfold Mmult, Id.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try clra.
  simpl.
  replace ((S (S x) <? 2)) with false by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma σy_unitary : WF_Unitary σy.
Proof.
  split.
  show_wf.
  unfold Mmult, Id.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try clra.
  simpl.
  replace ((S (S x) <? 2)) with false by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma σz_unitary : WF_Unitary σz.
Proof.
  split.
  show_wf.
  unfold Mmult, Id.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try clra.
  simpl.
  replace ((S (S x) <? 2)) with false by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.

Lemma phase_unitary : forall ϕ, @WF_Unitary 2 (phase_shift ϕ).
Proof.
  intros ϕ.
  split; [show_wf|].
  unfold Mmult, Id, phase_shift, adjoint, Cexp.
  prep_matrix_equality.
  destruct x as [| [|x]]; destruct y as [|[|y]]; try clra.
  - simpl.
    Csimpl.
    unfold Cconj, Cmult.
    simpl.
    unfold Rminus.
    rewrite Ropp_mult_distr_l.
    rewrite Ropp_involutive.
    replace (cos ϕ * cos ϕ)%R with ((cos ϕ)²) by easy.
    replace (sin ϕ * sin ϕ)%R with ((sin ϕ)²) by easy. 
    rewrite Rplus_comm.
    rewrite sin2_cos2.
    clra.
  - simpl. Csimpl.
    replace ((S (S x) <? 2)) with false by reflexivity.
    rewrite andb_false_r.
    clra.
Qed.

Lemma control_unitary : forall n (A : Matrix n n), 
                          WF_Unitary A -> WF_Unitary (control A). 
Proof.
  intros n A H.
  destruct H as [WF U].
  split; auto with wf_db.
  unfold control, adjoint, Mmult, Id.
  prep_matrix_equality.
  simpl.
  bdestructΩ (x =? y).
  - subst; simpl.
    rewrite Csum_sum.
    bdestructΩ (y <? n + (n + 0)).
    + bdestructΩ (n <=? y).
      * rewrite Csum_0_bounded. Csimpl.
        rewrite (Csum_eq _ (fun x => A x (y - n)%nat ^* * A x (y - n)%nat)).
        ++ unfold control, adjoint, Mmult, Id in U.
           rewrite Nat.add_0_r.
           eapply (equal_f) in U. 
           eapply (equal_f) in U. 
           rewrite U.
           rewrite Nat.eqb_refl. simpl.
           bdestructΩ (y - n <? n).
           easy.
        ++ apply functional_extensionality. intros x.
           bdestructΩ (n + x <? n).
           bdestructΩ (n <=? n + x).
           rewrite minus_plus.
           easy.
        ++ intros x L.
           bdestructΩ (y =? x).
           rewrite andb_false_r.
           bdestructΩ (n <=? x).
           simpl. clra.
      * rewrite (Csum_unique 1). 
        rewrite Csum_0_bounded.
        ++ clra.
        ++ intros.
           rewrite andb_false_r.
           bdestructΩ (n + x <? n).
           simpl.
           clra.
        ++ exists y.
           repeat rewrite andb_false_r.
           split. easy.
           split. 
           rewrite Nat.eqb_refl.
           bdestructΩ (y <? n).
           simpl. clra.
           intros x Ne.
           bdestructΩ (y =? x ).
           repeat rewrite andb_false_r.
           clra.
    + rewrite 2 Csum_0_bounded; [clra| |].
      * intros x L.
        rewrite WF by (right; omega).
        bdestructΩ (n + x <? n).
        bdestructΩ (n <=? n + x).
        bdestructΩ (n <=? y).
        clra.
      * intros x L.
        bdestructΩ (y =? x).
        rewrite andb_false_r.
        bdestructΩ (n <=? x).
        simpl. clra.
  - simpl.
    rewrite Csum_sum.
    bdestructΩ (y <? n + (n + 0)).
    + bdestructΩ (n <=? y).
      * rewrite Csum_0_bounded. Csimpl.
        bdestructΩ (n <=? x).
        rewrite (Csum_eq _ (fun z => A z (x - n)%nat ^* * A z (y - n)%nat)).
        ++ unfold control, adjoint, Mmult, Id in U.
           rewrite Nat.add_0_r.
           eapply (equal_f) in U. 
           eapply (equal_f) in U. 
           rewrite U.
           bdestructΩ (x - n =? y - n).
           simpl.
           easy.
        ++ apply functional_extensionality. intros z.
           bdestructΩ (n + z <? n).
           bdestructΩ (n <=? n + z).
           rewrite minus_plus.
           easy.
        ++ rewrite Csum_0. easy.
           intros z.
           bdestructΩ (n + z <? n).
           rewrite andb_false_r.
           Csimpl. easy. 
        ++ intros z L.
           bdestructΩ (z <? n).
           bdestructΩ (n <=? z).
           bdestructΩ (x =? z); bdestructΩ (y =? z); try clra. 
      * bdestructΩ (n <=? x).        
        ++ rewrite Csum_0_bounded.
           rewrite Csum_0_bounded. clra.
           ** intros z L.
              bdestructΩ (n + z <? n).
              rewrite andb_false_r.
              clra.
           ** intros z L.
              bdestructΩ (z <? n).
              rewrite andb_false_r.
              bdestructΩ (x =? z); bdestructΩ (y =? z); try clra.
              bdestructΩ (n <=? z).
              clra.
        ++ rewrite 2 Csum_0_bounded; [clra| |].
           ** intros z L.
              rewrite andb_false_r.
              bdestructΩ (x =? n + z); bdestructΩ (y =? n + z); rewrite andb_false_r; clra.
           ** intros z L.
              rewrite andb_false_r.
              bdestructΩ (x =? z); bdestructΩ (y =? z); rewrite andb_false_r; clra.
    + rewrite 2 Csum_0_bounded; [clra| |].
      * intros z L.
        bdestructΩ (n + z <? n). 
        bdestructΩ (n <=? n + z). 
        bdestructΩ (n <=? y).
        rewrite (WF _ (y-n)%nat) by (right; omega).
        clra.
      * intros z L.
        bdestructΩ (y =? z).
        rewrite andb_false_r.
        rewrite (WF _ (y-n)%nat) by (right; omega).
        destruct ((n <=? z) && (n <=? y)); clra.
Qed.

Lemma transpose_unitary : forall n (A : Matrix n n), WF_Unitary A -> WF_Unitary (A†).
Proof.
  intros. 
  simpl.
  split.
  + destruct H; auto with wf_db.
  + unfold WF_Unitary in *.
    rewrite adjoint_involutive.
    destruct H as [_ H].
    apply Minv_left in H as [_ S]. (* NB: admitted lemma *)
    assumption.
Qed.

Lemma cnot_unitary : WF_Unitary cnot.
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

Lemma id_unitary : forall n, WF_Unitary (Id n). 
Proof.
  split.
  apply WF_Id.
  unfold WF_Unitary.
  rewrite id_adjoint_eq.
  apply Mmult_1_l.
  apply WF_Id.
Qed.

Lemma swap_unitary : WF_Unitary swap.
Proof. 
  split.
  apply WF_swap.
  unfold WF_Unitary, Mmult, Id.
  prep_matrix_equality.
  do 4 (try destruct x; try destruct y; try clra).
  replace ((S (S (S (S x))) <? 4)) with (false) by reflexivity.
  rewrite andb_false_r.
  clra.
Qed.


Lemma kron_unitary : forall {m n} (A : Matrix m m) (B : Matrix n n),
  WF_Unitary A -> WF_Unitary B -> WF_Unitary (A ⊗ B).
Proof.
  intros m n A B [WFA UA] [WFB UB].
  unfold WF_Unitary in *.
  split.
  auto with wf_db.
  rewrite kron_adjoint.
  rewrite kron_mixed_product.
  rewrite UA, UB.
  rewrite id_kron. 
  easy.
Qed.

Lemma Mmult_unitary : forall (n : nat) (A : Square n) (B : Square n),
  WF_Unitary A ->
  WF_Unitary B ->
  WF_Unitary (A × B).  
Proof.
  intros n A B [WFA UA] [WFB UB].
  split.
  auto with wf_db.
  autorewrite with M_db.
  rewrite Mmult_assoc.
  rewrite <- (Mmult_assoc _ _ _ _ (A†)).
  rewrite UA.
  autorewrite with M_db.
  apply UB.
Qed.


(********************)
(* Self-adjointness *)
(********************)

Definition id_sa := id_adjoint_eq.

Lemma hadamard_sa : hadamard† = hadamard.
Proof.
  prep_matrix_equality.
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma σx_sa : σx† = σx.
Proof. 
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma σy_sa : σy† = σy.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try clra; trivial).
Qed.

Lemma σz_sa : σz† = σz.
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

Lemma control_adjoint : forall n (U : Square n), (control U)† = control (U†).
Proof.
  intros n U.
  unfold control, adjoint.
  prep_matrix_equality.
  rewrite Nat.eqb_sym.
  bdestruct (y =? x). 
  - subst.
    bdestruct (x <? n); bdestruct (n <=? x); try omega; simpl; clra.
  - rewrite 2 andb_false_r.
    rewrite andb_comm.
    rewrite (if_dist _ _ _ Cconj).
    rewrite Cconj_0.
    reflexivity.
Qed.

Lemma control_sa : forall (n : nat) (A : Square n), 
    A† = A -> (control A)† = (control A).
Proof.
  intros n A H.
  rewrite control_adjoint.
  rewrite H.
  easy.
Qed.  

Lemma phase_adjoint : forall ϕ, (phase_shift ϕ)† = phase_shift (-ϕ). 
Proof.
  intros ϕ.
  unfold phase_shift, adjoint.
  prep_matrix_equality.
  destruct_m_eq; try clra.
  unfold Cexp, Cconj. 
  rewrite cos_neg, sin_neg.
  easy.
Qed.

Lemma braket0_sa : |0⟩⟨0|† = |0⟩⟨0|. Proof. mlra. Qed.
Lemma braket1_sa : |1⟩⟨1|† = |1⟩⟨1|. Proof. mlra. Qed.

Hint Rewrite hadamard_sa σx_sa σy_sa σz_sa cnot_sa swap_sa 
             braket1_sa braket0_sa control_adjoint phase_adjoint : M_db.

(* Rather use control_adjoint :
Hint Rewrite control_sa using (autorewrite with M_db; reflexivity) : M_db. *)


(**************)
(* Automation *)
(**************)

(* For when autorewrite needs some extra help *)

Ltac Msimpl := 
  repeat match goal with 
  | [ |- context[(?A ⊗ ?B)†]]    => let H := fresh "H" in 
                                  specialize (kron_adjoint _ _ _ _ A B) as H;
                                  simpl in H; rewrite H; clear H
  | [ |- context[(control ?U)†]] => let H := fresh "H" in 
                                  specialize (control_sa _ U) as H;
                                  simpl in H; rewrite H; 
                                  [clear H | Msimpl; reflexivity]
  | [|- context[(?A ⊗ ?B) × (?C ⊗ ?D)]] => 
                                  let H := fresh "H" in 
                                  specialize (kron_mixed_product _ _ _ _ _ _ A B C D);
                                  intros H; simpl in H; rewrite H; clear H
  | _                           => autorewrite with M_db
  end.


(*****************************)
(* Positive Semidefiniteness *)
(*****************************)

Definition positive_semidefinite {n} (A : Square n) : Prop :=
  forall (z : Matrix n 1), WF_Matrix 2 1 z -> fst ((z† × A × z) O O) >= 0.  

Lemma braket0_psd : positive_semidefinite |0⟩⟨0|.
Proof. 
  intros z WFz. 
  do 3 reduce_matrices. 
  simpl.
  rewrite <- Ropp_mult_distr_l.
  unfold Rminus.
  rewrite Ropp_involutive.
  replace (fst (z 0%nat 0%nat) * fst (z 0%nat 0%nat))%R with ((fst (z 0%nat 0%nat))²) by easy. 
  replace (snd (z 0%nat 0%nat) * snd (z 0%nat 0%nat))%R with ((snd (z 0%nat 0%nat))²) by easy. 
  apply Rle_ge.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Lemma braket1_psd : positive_semidefinite |1⟩⟨1|.
Proof. 
  intros z WFz. 
  do 3 reduce_matrices. 
  simpl.
  rewrite <- Ropp_mult_distr_l.
  unfold Rminus.
  rewrite Ropp_involutive.
  replace (fst (z 1%nat 0%nat) * fst (z 1%nat 0%nat))%R with ((fst (z 1%nat 0%nat))²) by easy. 
  replace (snd (z 1%nat 0%nat) * snd (z 1%nat 0%nat))%R with ((snd (z 1%nat 0%nat))²) by easy. 
  apply Rle_ge.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Lemma H0_psd : positive_semidefinite (hadamard × |0⟩⟨0| × hadamard).
Proof.
  intros z WFz.
  do 5 reduce_matrices.  
  simpl.
  autorewrite with R_db.
  replace (√ 2 * / 2 * (√ 2 * / 2))%R with ((√ 2 / 2)²) by reflexivity.
  rewrite Rsqr_div by lra.
  rewrite Rsqr_sqrt by lra.
  Search (_ * ?x + _ * ?x).
  rewrite <- Rmult_plus_distr_r.
  Search (- _ + - _).
  rewrite <- Ropp_plus_distr.
  repeat rewrite <- Ropp_mult_distr_l.
  repeat rewrite Ropp_involutive.
  rewrite <- Rmult_plus_distr_r.
  rewrite (Rmult_comm _ (2/2²)).
  rewrite (Rmult_comm _ (2/2²)).
  repeat rewrite Rmult_assoc.
  repeat rewrite <- Rmult_plus_distr_l.
  apply Rle_ge.
  apply Rmult_le_pos. 
  left. 
  apply Rmult_lt_0_compat. 
  lra.
  apply Rinv_0_lt_compat.
  apply Rmult_lt_0_compat; lra.
  Search ((_ + _) * _)%R.
  repeat rewrite Rmult_plus_distr_r.
  remember (fst (z 0 0)%nat) as a.
  remember (snd (z 0 0)%nat) as b.
  remember (fst (z 1 0)%nat) as c.
  remember (snd (z 1 0)%nat) as d.
  (* This is (a + b)² + (b + c)². *)
  clear.
  rewrite <- Rplus_assoc.
  remember (a * a + c * a)%R as ac1. 
  remember (b * b + d * b)%R as bd1. 
  remember (a * c + c * c)%R as ac2. 
  remember (b * d + d * d)%R as bd2.
  rewrite (Rplus_assoc ac1).
  rewrite (Rplus_comm bd1).
  repeat rewrite <- Rplus_assoc.
  rewrite (Rplus_assoc _ bd1).
  apply Rplus_le_le_0_compat.
  replace (ac1 + ac2)%R with ((a + c)²).
  apply Rle_0_sqr.
  unfold Rsqr. lra.
  replace (bd1 + bd2)%R with ((b + d)²).
  apply Rle_0_sqr.
  unfold Rsqr. lra.
Qed.
    
(*************************)
(* Pure and Mixed States *)
(*************************)

Notation Density n := (Matrix n n) (only parsing). 

Definition Pure_State_Vector {n} (φ : Matrix n 1): Prop := 
  WF_Matrix n 1 φ /\ φ† × φ = 'I_ 1.

Definition Pure_State {n} (ρ : Density n) : Prop := 
  exists φ, Pure_State_Vector φ /\ ρ = φ × φ†.

Inductive Mixed_State {n} : Matrix n n -> Prop :=
| Pure_S : forall ρ, Pure_State ρ -> Mixed_State ρ
| Mix_S : forall (p : R) ρ1 ρ2, 0 < p < 1 -> Mixed_State ρ1 -> Mixed_State ρ2 ->
                                       Mixed_State (p .* ρ1 .+ (1-p)%R .* ρ2).  

Lemma WF_Pure : forall {n} (ρ : Density n), Pure_State ρ -> WF_Matrix n n ρ.
Proof. intros. destruct H as [φ [[WFφ IP1] Eρ]]. rewrite Eρ. auto with wf_db. Qed.
Hint Resolve WF_Pure : wf_db.

Lemma WF_Mixed : forall {n} (ρ : Density n), Mixed_State ρ -> WF_Matrix n n ρ.
Proof. induction 1; auto with wf_db. Qed.
Hint Resolve WF_Mixed : wf_db.

Lemma pure0 : Pure_State |0⟩⟨0|. 
Proof. exists |0⟩. intuition. split. auto with wf_db. solve_matrix. Qed.

Lemma pure1 : Pure_State |1⟩⟨1|. 
Proof. exists |1⟩. intuition. split. auto with wf_db. solve_matrix. Qed.

Lemma pure_id1 : Pure_State ('I_ 1).
Proof. exists ('I_ 1). split. split. auto with wf_db. solve_matrix. solve_matrix. Qed.

Lemma pure_dim1 : forall (ρ : Square 1), Pure_State ρ -> ρ = 'I_ 1.
Proof.
  intros ρ [φ [[WFφ IP1] Eρ]]. 
  apply Minv_flip in IP1.
  rewrite Eρ; easy.
Qed.    
                              
Lemma pure_state_kron : forall m n (ρ : Square m) (φ : Square n),
  Pure_State ρ -> Pure_State φ -> Pure_State (ρ ⊗ φ).
Proof.
  intros m n ρ φ [u [[WFu Pu] Eρ]] [v [[WFv Pv] Eφ]].
  exists (u ⊗ v).
  split; [split |].
  - auto with wf_db.
  - Msimpl. rewrite Pv, Pu. Msimpl. easy.
  - Msimpl. subst. easy.
Qed.

Lemma mixed_state_kron : forall m n (ρ : Square m) (φ : Square n),
  Mixed_State ρ -> Mixed_State φ -> Mixed_State (ρ ⊗ φ).
Proof.
  intros m n ρ φ Mρ Mφ.
  induction Mρ.
  induction Mφ.
  - apply Pure_S. apply pure_state_kron; easy.
  - rewrite kron_plus_distr_l.
    rewrite 2 Mscale_kron_dist_r.
    apply Mix_S; easy.
  - rewrite kron_plus_distr_r.
    rewrite 2 Mscale_kron_dist_l.
    apply Mix_S; easy.
Qed.

Lemma pure_state_trace_1 : forall {n} (ρ : Density n), Pure_State ρ -> trace ρ = 1.
Proof.
  intros n ρ [u [[WFu Uu] E]]. 
  subst.
  clear -Uu.
  unfold trace.
  unfold Mmult, adjoint in *.
  simpl in *.
  match goal with
    [H : ?f = ?g |- _] => assert (f O O = g O O) by (rewrite <- H; easy)
  end. 
  unfold Id in H; simpl in H.
  rewrite <- H.
  apply Csum_eq.
  apply functional_extensionality.
  intros x.
  rewrite Cplus_0_l, Cmult_comm.
  easy.
Qed.

Lemma mixed_state_trace_1 : forall {n} (ρ : Density n), Mixed_State ρ -> trace ρ = 1.
Proof.
  intros n ρ H. 
  induction H. 
  - apply pure_state_trace_1. easy.
  - rewrite trace_plus_dist.
    rewrite 2 trace_mult_dist.
    rewrite IHMixed_State1, IHMixed_State2.
    clra.
Qed.

(* The following two lemmas say that for any mixed states, the elements along the 
   diagonal are real numbers in the [0,1] interval. *)

Lemma mixed_state_diag_in01 : forall {n} (ρ : Density n) i , Mixed_State ρ -> 
                                                        0 <= fst (ρ i i) <= 1.
Proof.
  intros.
  induction H.
  - destruct H as [φ [[WFφ IP1] Eρ]].
    destruct (lt_dec i n). 
    Focus 2.
      rewrite Eρ. unfold Mmult, adjoint. simpl. rewrite WFφ. simpl. lra.
      omega.
    rewrite Eρ.
    unfold Mmult, adjoint in *.
    simpl in *.
    rewrite Rplus_0_l.
    match goal with
    [H : ?f = ?g |- _] => assert (f O O = g O O) by (rewrite <- H; easy)
    end. 
    unfold Id in H. simpl in H. clear IP1.
    match goal with
    [ H : ?x = ?y |- _] => assert (H': fst x = fst y) by (rewrite H; easy); clear H
    end.
    simpl in H'.
    rewrite <- H'.    
    split.
    + unfold Rminus. rewrite <- Ropp_mult_distr_r. rewrite Ropp_involutive.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat; apply Rle_0_sqr.    
    + match goal with 
      [ |- ?x <= fst (Csum ?f ?m)] => specialize (Csum_member_le f n) as res
      end.
      simpl in *.
      unfold Rminus in *.
      Search (_ * - _)%R.
      rewrite <- Ropp_mult_distr_r.
      rewrite Ropp_mult_distr_l.
      apply res with (x := i); trivial. 
      intros x.
      unfold Rminus. rewrite <- Ropp_mult_distr_l. rewrite Ropp_involutive.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat; apply Rle_0_sqr.    
  - simpl.
    repeat rewrite Rmult_0_l.
    repeat rewrite Rminus_0_r.
    split.
    assert (0 <= p * fst (ρ1 i i)).
      apply Rmult_le_pos; lra.
    assert (0 <= (1 - p) * fst (ρ2 i i)).
      apply Rmult_le_pos; lra.
    lra.
    assert (p * fst (ρ1 i i) <= p)%R. 
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l; lra.
    assert ((1 - p) * fst (ρ2 i i) <= (1-p))%R. 
      rewrite <- Rmult_1_r.
      apply Rmult_le_compat_l; lra.
    lra.
Qed.

Lemma mixed_state_diag_real : forall {n} (ρ : Density n) i , Mixed_State ρ -> 
                                                        snd (ρ i i) = 0.
Proof.
  intros.
  induction H.
  + unfold Pure_State in H. 
  - destruct H as [φ [[WFφ IP1] Eρ]].
    rewrite Eρ.
    simpl. 
    lra.
  + simpl.
    rewrite IHMixed_State1, IHMixed_State2.
    repeat rewrite Rmult_0_r, Rmult_0_l.
    lra.
Qed.

Lemma mixed_dim1 : forall (ρ : Square 1), Mixed_State ρ -> ρ = 'I_ 1.
Proof.
  intros.  
  induction H.
  + apply pure_dim1; trivial.
  + rewrite IHMixed_State1, IHMixed_State2.
    prep_matrix_equality.
    clra.
Qed.  


(** Density matrices and superoperators **)

Definition Superoperator m n := Density m -> Density n.

Definition WF_Superoperator {m n} (f : Superoperator m n) := 
  (forall ρ, Mixed_State ρ -> Mixed_State (f ρ)).   

Definition super {m n} (M : Matrix m n) : Superoperator n m := fun ρ => 
  M × ρ × M†.

Lemma super_I : forall n ρ,
      WF_Matrix n n ρ ->
      super ('I_n) ρ = ρ.
Proof.
  intros.
  unfold super.
  autorewrite with M_db.
  reflexivity.
Qed.

Lemma WF_super : forall  m n (U : Matrix m n) (ρ : Square n), 
  WF_Matrix m n U -> WF_Matrix n n ρ -> WF_Matrix m m (super U ρ).
Proof.
  unfold super.
  auto with wf_db.
Qed.

Hint Resolve WF_super : wf_db.

Lemma super_outer_product : forall m (φ : Matrix m 1) (U : Matrix m m), 
    super U (outer_product φ) = outer_product (U × φ).
Proof.
  intros. unfold super, outer_product.
  autorewrite with M_db.
  repeat rewrite Mmult_assoc. reflexivity.
Qed.

Definition compose_super {m n p} (g : Superoperator n p) (f : Superoperator m n)
                      : Superoperator m p :=
  fun ρ => g (f ρ).

Lemma WF_compose_super : forall m n p (g : Superoperator n p) (f : Superoperator m n) 
  (ρ : Square m), 
  WF_Matrix m m ρ ->
  (forall A, WF_Matrix m m A -> WF_Matrix n n (f A)) ->
  (forall A, WF_Matrix n n A -> WF_Matrix p p (g A)) ->
  WF_Matrix p p (compose_super g f ρ).
Proof.
  unfold compose_super.
  auto.
Qed.

Hint Resolve WF_compose_super : wf_db.


Lemma compose_super_correct : forall {m n p} 
                              (g : Superoperator n p) (f : Superoperator m n),
      WF_Superoperator g -> 
      WF_Superoperator f ->
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

Lemma sum_super_correct : forall m n (f g : Superoperator m n),
      WF_Superoperator f -> WF_Superoperator g -> WF_Superoperator (sum_super f g).
Proof.
  intros m n f g wf_f wf_g ρ pf_ρ.
  unfold sum_super. 
  set (wf_f' := wf_f _ pf_ρ).
  set (wf_g' := wf_g _ pf_ρ).
  apply (Mix_S (1/2) (f ρ) (g ρ)); auto. 
  lra.
Qed.

(* Maybe we shouldn't call these superoperators? Neither is trace-preserving *)
Definition SZero {n} : Superoperator n n := fun ρ => Zero n n.
Definition Splus {m n} (S T : Superoperator m n) : Superoperator m n :=
  fun ρ => S ρ .+ T ρ.

(* These are *)
Definition new0_op : Superoperator 1 2 := super |0⟩.
Definition new1_op : Superoperator 1 2 := super |1⟩.
Definition meas_op : Superoperator 2 2 := Splus (super |0⟩⟨0|) (super |1⟩⟨1|).
Definition discard_op : Superoperator 2 1 := Splus (super ⟨0|) (super ⟨1|).

Lemma pure_unitary : forall {n} (U ρ : Matrix n n), 
  WF_Unitary U -> Pure_State ρ -> Pure_State (super U ρ).
Proof.
  intros n U ρ [WFU H] [φ [[WFφ IP1] Eρ]].
  rewrite Eρ.
  exists (U × φ).
  split.
  - split; auto with wf_db.
    rewrite (Mmult_adjoint _ _ _ U φ).
    rewrite Mmult_assoc.
    rewrite <- (Mmult_assoc _ _ _ _ (U†)).
    rewrite H, Mmult_1_l, IP1; easy.
  - unfold super.
    rewrite (Mmult_adjoint _ _ _ U φ).
    repeat rewrite Mmult_assoc.
    reflexivity.
Qed.    

Lemma mixed_unitary : forall {n} (U ρ : Matrix n n), 
  WF_Unitary U -> Mixed_State ρ -> Mixed_State (super U ρ).
Proof.
  intros n U ρ H M.
  induction M.
  + apply Pure_S.
    apply pure_unitary; trivial.
  + unfold WF_Unitary, super in *.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    rewrite 2 Mscale_mult_dist_r.
    rewrite 2 Mscale_mult_dist_l.
    apply Mix_S; trivial.
Qed.

Lemma super_unitary_correct : forall {n} (U : Matrix n n), 
  WF_Unitary U -> WF_Superoperator (super U).
Proof.
  intros n U H ρ Mρ.
  apply mixed_unitary; easy.
Qed.

Lemma compose_super_assoc : forall {m n p q}
      (f : Superoperator m n) (g : Superoperator n p) (h : Superoperator p q), 
      compose_super (compose_super f g) h
    = compose_super f (compose_super g h).
Proof. easy. Qed.


(* This is compose_super_correct 
Lemma WF_Superoperator_compose : forall m n p (s : Superoperator n p) (s' : Superoperator m n),
    WF_Superoperator s ->
    WF_Superoperator s' ->
    WF_Superoperator (compose_super s s').
Proof.
  unfold WF_Superoperator.
  intros m n p s s' H H0 ρ H1.
  unfold compose_super.
  apply H.
  apply H0.
  easy.
Qed.
*)

(****************************************)
(* Tests and Lemmas about swap matrices *)
(****************************************)

Lemma swap_spec : forall (q q' : Matrix 2 1), WF_Matrix 2 1 q -> 
                                         WF_Matrix 2 1 q' ->
                                         swap × (q ⊗ q') = q' ⊗ q.
Proof.
  intros q q' WF WF'.
  solve_matrix.
  - destruct y. clra. 
    rewrite WF by omega. 
    rewrite (WF' O (S y)) by omega.
    clra.
  - destruct y. clra. 
    rewrite WF by omega. 
    rewrite (WF' O (S y)) by omega.
    clra.
  - destruct y. clra. 
    rewrite WF by omega. 
    rewrite (WF' 1%nat (S y)) by omega.
    clra.
  - destruct y. clra. 
    rewrite WF by omega. 
    rewrite (WF' 1%nat (S y)) by omega.
    clra.
Qed.  

Example swap_to_0_test_24 : forall (q0 q1 q2 q3 : Matrix 2 1), 
  WF_Matrix 2 1 q0 -> WF_Matrix 2 1 q1 -> WF_Matrix 2 1 q2 -> WF_Matrix 2 1 q3 ->
  swap_to_0 4 2 × (q0 ⊗ q1 ⊗ q2 ⊗ q3) = (q2 ⊗ q1 ⊗ q0 ⊗ q3). 
Proof.
  intros q0 q1 q2 q3 WF0 WF1 WF2 WF3.
  unfold swap_to_0, swap_to_0_aux.
  repeat rewrite Mmult_assoc.
  rewrite (kron_assoc _ _ _ _ _ _ q0 q1).
  rewrite kron_mixed_product.
  rewrite (kron_mixed_product _ _ _ _ _ _ ('I_ (2^1)) swap).
  rewrite swap_spec by assumption.
  Msimpl.
  rewrite (kron_assoc _ _ _ _ _ _ q0).
  rewrite (kron_assoc _ _ _ _ _ _ q2 q1).
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ q0 q2 (q1 ⊗ q3)).
  simpl.
  setoid_rewrite (kron_mixed_product _ _ _ _ _ _ swap ('I_4) (q0 ⊗ q2) (q1 ⊗ q3)).
  rewrite swap_spec by assumption.
  Msimpl.
  rewrite (kron_assoc _ _ _ _ _ _ q2 q0).
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ q0 q1 q3).
  setoid_rewrite (kron_assoc _ _ _ _ _ _ ('I_2)).  
  setoid_rewrite (kron_mixed_product _ _ _ _ _ _ ('I_2) (swap ⊗ 'I_2) q2 _).
  setoid_rewrite (kron_mixed_product _ _ _ _ _ _ swap ('I_2) _ _).
  Msimpl.
  rewrite swap_spec by assumption.
  repeat setoid_rewrite kron_assoc.
  reflexivity.
Qed.

Lemma swap_two_base : swap_two 2 1 0 = swap.
Proof. unfold swap_two. simpl. apply kron_1_r. Qed.

Lemma swap_second_two : swap_two 3 1 2 = Id 2 ⊗ swap.
Proof. unfold swap_two.
       simpl.
       rewrite kron_1_r.
       reflexivity.
Qed.

Lemma swap_0_2 : swap_two 3 0 2 = ('I_2 ⊗ swap) × (swap ⊗ 'I_2) × ('I_2 ⊗ swap).
Proof.
  unfold swap_two.
  simpl.
  Msimpl.
  reflexivity.
Qed.

(*
Proposition swap_to_0_spec : forall (q q0 : Matrix 2 1) (n k : nat) (l1 l2 : list (Matrix 2 1)), 
   length l1 = (k - 1)%nat ->
   length l2 = (n - k - 2)%nat ->   
   @Mmult (2^n) (2^n) 1 (swap_to_0 n k) (⨂ ([q0] ++ l1 ++ [q] ++ l2)) = 
     ⨂ ([q] ++ l1 ++ [q0] ++ l2).

Proposition swap_two_spec : forall (q q0 : Matrix 2 1) (n0 n1 n2 n k : nat) (l0 l1 l2 : list (Matrix 2 1)), 
   length l0 = n0 ->
   length l1 = n1 ->
   length l2 = n2 ->   
   n = (n0 + n1 + n2 + 2)%nat ->
   @Mmult (2^n) (2^n) 1 
     (swap_two n n0 (n0+n1+1)) (⨂ (l0 ++ [q0] ++ l1 ++ [q] ++ l2)) = 
     ⨂ (l0 ++ [q] ++ l1 ++ [q0] ++ l2).
*)

Example move_to_0_test_24 : forall (q0 q1 q2 q3 : Matrix 2 1), 
  WF_Matrix 2 1 q0 -> WF_Matrix 2 1 q1 -> WF_Matrix 2 1 q2 -> WF_Matrix 2 1 q3 ->
  move_to_0 4 2 × (q0 ⊗ q1 ⊗ q2 ⊗ q3) = (q2 ⊗ q0 ⊗ q1 ⊗ q3). 
Proof.
  intros q0 q1 q2 q3 WF0 WF1 WF2 WF3.
  unfold move_to_0, move_to_0_aux.
  repeat rewrite Mmult_assoc.
  rewrite (kron_assoc _ _ _ _ _ _ q0 q1).
  simpl.
  setoid_rewrite (kron_mixed_product _ _ _ _ _ _ (('I_2) ⊗ swap) ('I_2) 
                                     (q0 ⊗ (q1 ⊗ q2)) q3).
  setoid_rewrite (kron_mixed_product _ _ _ _ _ _ ('I_2) swap q0 (q1 ⊗ q2)).
  Msimpl.
  rewrite swap_spec by assumption.
  setoid_rewrite <- (kron_assoc _ _ _ _ _ _ q0 q2 q1).
  setoid_rewrite (kron_assoc _ _ _ _ _ _ (q0 ⊗ q2) q1 q3).
  setoid_rewrite (kron_mixed_product _ _ _ _ _ _ swap ('I_4) (q0 ⊗ q2) (q1 ⊗ q3)).
  rewrite swap_spec by assumption.
  Msimpl.
  repeat setoid_rewrite kron_assoc.
  reflexivity.
Qed.

(* *)
