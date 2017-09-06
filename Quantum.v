From mathcomp Require Import all_ssreflect all_algebra all_field.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Require Import mxtens. Instead using mxutil.v *)
Require Import mxutil.

(*
Require Import Arith.
Require Import Omega.
*)

Import GRing.Theory Num.Theory UnityRootTheory.
Local Open Scope ring_scope.

Open Scope ring_scope.
Bind Scope C with algC.

(* Currently doesn't support conjC *)
(* Variable C : closedFieldType. (* can be used as an alternative to algC *) *)

Notation "√ n" := (sqrtC n) (at level 20).

(* Natural number arithmetic *)

(* Use SSR_nat ? *)
Lemma double_mult : forall (n : nat), (n + n = 2 * n)%nat. 
Proof. move => n; rewrite mul2n addnn //. Qed.
Lemma pow_two_succ_l : forall n, (2^n * 2 = 2^(n.+1))%nat.
Proof. move => n. rewrite mulnC. rewrite expnS //. Qed.
Lemma pow_two_succ_r : forall n, (2 * 2^n = 2 ^ (n.+1))%nat.
Proof. move => n; rewrite expnS //. Qed.
Lemma double_pow : forall (n : nat), (2^n + 2^n = 2^(n.+1))%nat. 
Proof. move => n. rewrite addnn expnS mul2n //. Qed.
Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> (a^m = b^n)%nat.
Proof. intuition. Qed.

(* Coq_nat: *)
(*
Lemma double_mult : forall (n : nat), (n + n = 2 * n)%coq_nat. Proof. intros. omega. Qed. 
Lemma pow_two_succ_l : forall x, (2^x * 2 = Nat.pow 2 (x + 1))%coq_nat.
Proof. intros. rewrite mult_comm. rewrite <- Nat.pow_succ_r'. rewrite addn1. reflexivity. Qed.
Lemma pow_two_succ_r : forall x, (2 * 2^x = Nat.pow 2 (x + 1))%coq_nat.
Proof. intros. rewrite <- Nat.pow_succ_r'. rewrite addn1. reflexivity. Qed.
Lemma double_pow : forall (n : nat), (2^n + 2^n = Nat.pow 2 (n+1))%coq_nat. 
Proof. intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity. Qed.
Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> (a^m = b^n)%nat.
Proof. intuition. Qed.
*)

Search expn addn.
About addnA.
Ltac unify_pows_two :=
  repeat match goal with
  (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
  | [ |- context[ 4%nat ]]                  => replace 4%nat with (2^2)%nat by reflexivity
  | [ |- context[ (0 + ?a)%nat]]            => rewrite add0n 
  | [ |- context[ (?a + 0)%nat]]            => rewrite addn0 
  | [ |- context[ (2 * 2^?x)%nat]]          => rewrite pow_two_succ_r
  | [ |- context[ (2^?x * 2)%nat]]          => rewrite pow_two_succ_l
  | [ |- context[ (2^?x + 2^?x)%nat]]       => rewrite double_pow 
  | [ |- context[ (2^?x * 2^?y)%nat]]       => rewrite -expnD 
  | [ |- context[ (?a + (?b + ?c))%nat ]]   => rewrite addnA 
  | [ |- (2^?x = 2^?y)%nat ]                => apply pow_components; trivial 
  end.


(* Coq nat:
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
*)

(* /Natural Numbers *)

(* Matrix Stuff *)
Definition conj_trmx {m n : nat} (A : 'M[algC]_(m,n)) : 'M[algC]_(n,m) := 
  \matrix_(i, j) conjC (A j i).

Notation I := 1%:M.
Notation I_ x := (1%:M : 'M_(x)).
Infix "×" := mulmx (at level 40, left associativity) : matrix_scope.
(* Infix "⊗" := tensmx (at level 40, left associativity) : matrix_scope. *)
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Notation "A ⊤" := (trmx A) (at level 0) : matrix_scope. 
Notation "A †" := (conj_trmx A) (at level 0) : matrix_scope. 

(* /Matrix stuff *)

Open Scope matrix_scope.

Example test : (1 * 1 + 'i = 1 + 0 + 'i)%C.
Proof. rewrite mul1r. rewrite addr0. reflexivity. Qed.

(* This database will need expanding *)
Hint Rewrite add0r addr0 mul1r mulr1 : C_db.

Definition o0 : 'I_2 := inord 0.
Definition o1 : 'I_2 := inord 1.
Notation Ord n := (@Ordinal _ n _).

Definition ket0 : 'M[algC]_(2,1) := \matrix_(i,j) if i == o0 then 1 else 0. 
Definition ket1 : 'M[algC]_(2,1) := \matrix_(i,j) if i == o1 then 1 else 0. 
Definition bra0 : 'M[algC]_(1,2) := \matrix_(i,j) if j == o0 then 1 else 0. 
Definition bra1 : 'M[algC]_(1,2) := \matrix_(i,j) if j == o1 then 1 else 0. 
Definition ket (x : nat) : 'M[algC]_(2,1) := if x == 0%nat then ket0 else ket1.
Transparent ket0.
Transparent ket1.
Transparent ket.
Notation "|0⟩" := ket0.
Notation "|1⟩" := ket1.
Notation "⟨0|" := bra0.
Notation "⟨1|" := bra1.
Notation "|0⟩⟨0|" := (|0⟩×⟨0|).
Notation "|1⟩⟨1|" := (|1⟩×⟨1|).
Notation "|1⟩⟨0|" := (|1⟩×⟨0|).
Notation "|0⟩⟨1|" := (|0⟩×⟨1|).

Lemma bra0_conj : ⟨0| † = |0⟩.
Proof. by apply/matrixP=> i j; rewrite !mxE (fun_if conjC) rmorph1 rmorph0. Qed.
Lemma ket0_conj : |0⟩ † = ⟨0|.
Proof. by apply/matrixP=> i j; rewrite !mxE (fun_if conjC) rmorph1 rmorph0. Qed.
Lemma bra1_conj : ⟨1| † = |1⟩.
Proof. by apply/matrixP=> i j; rewrite !mxE (fun_if conjC) rmorph1 rmorph0. Qed.
Lemma ket1_conj : |1⟩ † = ⟨1|.
Proof. by apply/matrixP=> i j; rewrite !mxE (fun_if conjC) rmorph1 rmorph0. Qed.


(* Coercion nat_as_ord : nat >-> ord. *)

Definition hadamard : 'M[algC]_2 :=  \matrix_(i,j) 
   if (o1 == i) && (o1 == j)
   then -(1 / √(2%:R))
   else 1 / √(2%:R).

Inductive hadamard_spec : 'I_2 -> 'I_2 -> algC -> Type :=
  | hadamard_pos                       : hadamard_spec o1 o1 (-(1 / √(2%:R))) 
  | hadamard_neg i j of ~~ [&& i == o1 & j == o1] : hadamard_spec i j (1 / √(2%:R)).

Lemma hadamardP i j : hadamard_spec i j (hadamard i j).
Proof.
rewrite /hadamard mxE; case: ifP.
case/andP=> /eqP <- /eqP <-; constructor.
move/negbT; rewrite negb_and => hor; constructor 2.
by case/orP: hor; rewrite negb_and eq_sym // => ->; rewrite ?orbT.
Qed. 

(* Lemma U : hadamard (inord 1) (inord 1) = -(1 / √(2%:R)).
Proof.
case: hadamardP => //.

*)

(* This uses coq exponentiation. 
Fixpoint hadamard_k (k : nat) : 'M_(2^k)%nat := 
  match k with
  | 0 => I
  | S k' => hadamard ⊗ hadamard_k k'
  end. 
*)

(* For ssreflect exponentiation this requires casting: *)
Fixpoint hadamard_k (k : nat) : 'M_(2^k)%nat :=
  match k with
  | 0    => I
  | S k' => castmx (esym (expnS _ _),esym (expnS _ _))
                   (hadamard ⊗ hadamard_k k')
  end.


(* Neither kronecker product library has unit lemmas??? 
Lemma hadamard_1 : hadamard_k 1 = hadamard.
Proof. rewrite /hadamard_k. Search (_ ⊗ I). apply kron_1_r. Qed.
*)

Definition pauli_x : 'M[algC]_2 :=
  \matrix_(i,j) if i == j then 0 else 1.

Definition pauli_y : 'M[algC]_2 :=
  \matrix_(i,j) if i == j then 0 else (-1) ^+ j * 'i.

Definition pauli_z : 'M[algC]_2 :=
  \matrix_(i,j) if i == j then (-1) ^+ j else 0.
 
Definition control {n : nat} (A : 'M[algC]_n) : 'M[algC]_(n+n) := block_mx I 0 0 A.

Definition cnot := control pauli_x.

(* Swap Matrices *)

Definition swap : 'M[algC]_4 := \matrix_(i,j)
  match i, j with 
  | Ord 0, Ord 0 => 1
  | Ord 1, Ord 2 => 1
  | Ord 2, Ord 1 => 1
  | Ord 3, Ord 3 => 1
  | _, _ => 0
  end.

(** Giuseppe Sergioli's approach **)

(* Projection and Ladder Operators *)

Definition P0 := |0⟩⟨0|. (* may define directly *)
Definition P1 := |1⟩⟨1|.
Definition L0 := |0⟩⟨1|.
Definition L1 := |1⟩⟨0|.

Definition SWAP : 'M[algC]_4 := block_mx P0 L1 L0 P1.

Lemma swap_eq : SWAP = swap.
Proof.
  apply/matrixP=> i j. rewrite !mxE.
  case: i => m i //. 
Admitted.

(* Slides use I_(n-1) but this doesn't work out in terms of dimensions *)
Definition P0' n := I_(2^(n-2)) ⊗ |0⟩⟨0|.
Definition P1' n := I_(2^(n-2)) ⊗ |1⟩⟨1|.
Definition L0' n := I_(2^(n-2)) ⊗ |0⟩⟨1|.
Definition L1' n := I_(2^(n-2)) ⊗ |1⟩⟨0|.

(* SWAPs first and last qubits of an n qubit matrix *)
Definition SWAP' n := block_mx (P0' n) (L1' n) (L0' n) (P1' n).

Check SWAP'.

Lemma swap_eq' : SWAP' 2 = swap.
Proof. 
Admitted.


(* k = num qubits. m = 1st qubit to be swapped. m + n = 2nd qubit to be swapped. *) 
Definition SWAP'' k m n := I_(2^m) ⊗ SWAP' n ⊗ I_(2^(k-m-n)). 

(* Properly typed *)
Locate "+".
Locate "<=".
Program Definition SWAP''' (k m n : nat) (pf1 : leq 2 n) (pf2 : leq (addn m n) k) 
  : 'M[algC]_(2^k)%nat := 
  I_(2^m) ⊗ SWAP' n ⊗ I_(2^(k-m-n)). 
Next Obligation. 
  unify_pows_two.
  rewrite subn2 /=.
  replace (n.-2.+2) with n.
  Focus 2. destruct n. inversion pf1. destruct n. inversion pf1. by [].
  rewrite -subnDA addnBA //=.
  rewrite addKn //.
Defined.  
Next Obligation. 
  unify_pows_two.
  rewrite subn2 /=.
  replace (n.-2.+2) with n.
  Focus 2. destruct n. inversion pf1. destruct n. inversion pf1. by [].
  rewrite -subnDA addnBA //=.
  rewrite addKn //.
Defined.  

(*
(* The input k is really k+1, to appease to Coq termination gods *)
(* NOTE: Check that the offsets are right *)
(* Requires: i + 1 < n *)
Program Fixpoint swap_to_0_aux (n i : nat) {pf : (i + 1 < n)%nat} {struct i} : 'M[algC]_(2^n) := 
  match i with
  | O => swap ⊗ I_(2^(n-2))
  | S i' =>  (I_(2^i') ⊗ swap ⊗ I_(2^(n-i'-2))) × (* swap i-1 with i *)
            swap_to_0_aux n i' × 
            (I_(2^i') ⊗ swap ⊗ I_(2^(n-i'-2))) (* swap i-1 with 0 *)
  end.
Next Obligation. unify_pows_two.

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
*)

(* Lemma  *)
Lemma bra0_conj_lift i j : (⟨0| i j)^* = (⟨0| †) j i.
Proof. by rewrite !mxE. Qed.

Lemma ket0_conj_lift i j : (|0⟩ i j)^* = (|0⟩ †) j i.
Proof. by rewrite !mxE. Qed.

Lemma bra1_conj_lift i j : (⟨1| i j)^* = (⟨1| †) j i.
Proof. by rewrite !mxE. Qed.

Lemma ket1_conj_lift i j : (|1⟩ i j)^* = (|1⟩ †) j i.
Proof. by rewrite !mxE. Qed.

Definition brE0 := (bra0_conj_lift, bra0_conj, ket0_conj_lift, ket0_conj).
Definition brE1 := (bra1_conj_lift, bra1_conj, ket1_conj_lift, ket1_conj).

Lemma braket0_conj_transpose : |0⟩⟨0|† = |0⟩⟨0|.
Proof.
apply/matrixP => i j; rewrite !mxE rmorph_sum; apply/eq_bigr=> k _.
by rewrite rmorphM mulrC !brE0.
Qed.

Lemma braket1_conj_transpose : |1⟩⟨1|† = |1⟩⟨1|.
apply/matrixP => i j; rewrite !mxE rmorph_sum; apply/eq_bigr=> k _.
by rewrite rmorphM mulrC !brE1.
Qed.

(** Unitaries are unitary **)

Definition is_unitary {n: nat} (U : Matrix n n): Prop := U † × U = I_n.

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

(* Pure and Mixed States *)

(* Wiki:
In operator language, a density operator is a positive semidefinite, hermitian 
operator of trace 1 acting on the state space. A density operator describes 
a pure state if it is a rank one projection. Equivalently, a density operator ρ 
describes a pure state if and only if ρ = ρ ^ 2 *)

Notation Density n := (Matrix n n) (only parsing). 

Definition Pure_State {n} (ρ : Density n) : Prop := WF_Matrix n n ρ /\ ρ = ρ × ρ.

Lemma pure0 : Pure_State |0⟩⟨0|. Proof. split; [auto with wf_db|mlra]. Qed.
Lemma pure1 : Pure_State |1⟩⟨1|. Proof. split; [auto with wf_db|mlra]. Qed.

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
Proof.
  unfold Pure_State. intuition.
Qed.
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
  intros n U ρ [WFU H] [WFρ P].
  unfold Pure_State, is_unitary, super in *.
  split.
  auto with wf_db.
  remember (U × ρ × (U) † × (U × ρ × (U) †)) as rhs.
  rewrite P.
  replace (ρ × ρ) with (ρ × Id n × ρ) by (rewrite Mmult_1_r; trivial).
  rewrite <- H.
  rewrite Heqrhs.
  repeat rewrite Mmult_assoc. (* Admitted lemma *)
  reflexivity.
Qed.  

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
       constructor; split; [auto with wf_db|mlra].
       constructor; split; [auto with wf_db|mlra].
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

(* *)