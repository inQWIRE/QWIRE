Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASLib.
Require Import Denotation.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import Ancilla.
Require Import SemanticLib.

Require Import List.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.
Delimit Scope matrix_scope with M.

(**********************)
(* Syntactic Property *)
(**********************)

Close Scope matrix_scope.
Open Scope circ_scope.
Open Scope nat_scope.

Definition unitary_at1 n (U : Unitary Qubit) (i : Var) (pf : i < n)
        : Box (n ⨂ Qubit) (n ⨂ Qubit).
Proof.
  gen n U.
  induction i as [ | i]; intros n pf U.
  * destruct n as [ | n]; [omega | ]. simpl.
    refine (box_ q ⇒ let_ (q,qs) ← q; 
                     let_ q ← X $q; 
                     output (q,qs)).
  * destruct n as [ | n]; [omega | ]. simpl.
    refine (box_ q ⇒ let_ (q,qs) ← q; 
                     let_ qs ← IHi n _ U $ qs;
                     output (q,qs)). 
    omega.
Defined.

Lemma unitary_at1_WT : forall n (U : Unitary Qubit) i (pf : i < n),
    Typed_Box (unitary_at1 n U i pf).
Proof.
  intros n U i pf. gen n U. 
  induction i; intros n pf U.
  * simpl. destruct n as [ | n]; [omega | ].
    type_check.
  * simpl. destruct n as [ | n]; [omega | ]. simpl.
    type_check.
    apply IHi.
    type_check.
Qed.
Definition X_at n i (pf : i < n) := unitary_at1 n X i pf.

Lemma lt_leS_le : forall i j k,
    i < j -> j <= S k -> i <= k.
Proof. intros. omega. Qed.

Lemma strong_induction' : 
  forall P : nat -> Type,
  (forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
  forall n i, i <= n -> P i.
Proof. 
  intros P H.
  induction n.
    - intros i H0.
      assert (i0 : i = 0). 
      { inversion H0. reflexivity. }
      subst.
      apply H.
      intros. 
      absurd (False); [auto | inversion H1].
    - intros i Hi.
      apply H. intros k Hk.
      apply IHn. 
      apply (lt_leS_le _ _ _ Hk Hi).
Defined.


Theorem strong_induction:
forall P : nat -> Type,
(forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
forall n : nat, P n.
Proof.
  intros P H n.
  apply (strong_induction' P H n). constructor.
Defined.
Transparent strong_induction.


Lemma le_hprop : forall (a b : nat) (pf1 pf2 : a <= b), pf1 = pf2.
Proof. 
  induction a as [ | a]; induction b as [ | b]; intros pf1 pf2.
  * dependent destruction pf1. dependent destruction pf2.
    reflexivity.
  * dependent destruction pf1.
    dependent destruction pf2.
    apply f_equal. apply IHb.
  * dependent destruction pf1.
  * dependent destruction pf1.
    + dependent destruction pf2. 
      ++ reflexivity.
      ++ omega.
    + dependent destruction pf2.
      ++ omega.
      ++ apply f_equal. apply IHb.
Qed.

Lemma lt_hprop : forall (a b : nat) (pf1 pf2 : a < b), pf1 = pf2.
Proof. 
  intros.
  apply le_hprop.
Qed.

Lemma False_hprop : forall (pf1 pf2 : False), pf1 = pf2.
Proof.
  destruct pf1.
Qed.

Lemma nat_neq_hprop : forall (m n : nat) (pf1 pf2 : m <> n), pf1 = pf2.
Proof.
  intros m n pf1 pf2.
  apply functional_extensionality.
  intros pf_eq.
  apply False_hprop.
Qed.

    
(* Precondition: 0 < j < n *)
Definition CNOT_at_i0 (n j : nat) (pf_j : 0 < j) (pf_n : j < n) 
                     : Box (n ⨂ Qubit) (n ⨂ Qubit).
Proof.
  gen n.
  induction j as [ | [ | j']]; intros n pf_n.
  * (* i = 0, j = 0 *) absurd False; auto. inversion pf_j.
  * (* i = 0, j = 1 *)
    destruct n as [ | [ | n']]. 
    { absurd False; auto. inversion pf_n. }
    { absurd False; auto. inversion pf_n. inversion H0. }
    refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q; 
                     let_ (q0,q1) ← CNOT $(q0,q1);
                     output (q0,(q1,qs))).
  * (* i = 0, j = S (S j') *)
    destruct n as [ | [ | n']]. 
    { absurd False; auto. inversion pf_n. }
    { absurd False; auto. inversion pf_n. inversion H0. }
       refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q;
                        let_ (q0,qs) ← IHj _ (S n') _ $ output (q0,qs);
                        output (q0,(q1,qs))).
       + apply Nat.lt_0_succ.
       + apply lt_S_n. auto.
Defined.
Lemma CNOT_at_i0_WT : forall (n j : nat) (pf_j : 0 < j) (pf_n : j < n),
      Typed_Box (CNOT_at_i0 n j pf_j pf_n).
Proof.
  intros n j pf_j.
  gen n.
  induction j as [ | [ | j']]; intros n pf_n.
  * (* i = 0, j = 0 *) absurd False; auto. inversion pf_j.
  * (* i = 0, j = 1 *)
    destruct n as [ | [ | n']]. 
    { absurd False; auto. inversion pf_n. }
    { absurd False; auto. inversion pf_n. inversion H0. }
    simpl. type_check.
  * (* i = 0, j = S (S j') *)
    destruct n as [ | [ | n']]. 
    { absurd False; auto. inversion pf_n. }
    { absurd False; auto. inversion pf_n. inversion H0. }
    set (pf_j' := (Nat.lt_0_succ _ : 0 < S j')).
    set (pf_n' := (lt_S_n _ _ pf_n : S j' < S n')).
    assert (IH : Typed_Box (CNOT_at_i0 (S n') (S j') pf_j' pf_n')).
    { intros. apply IHj. }
    clear IHj.
    type_check.
Qed. 

Lemma CNOT_at_i0_SS : forall n j
                             (pfj : 0 < S (S j)) (pfj' : 0 < S j)
                             (pfn : S (S j) < S (S n)) (pfn' : S j < S n),
      CNOT_at_i0 (S (S n)) (S (S j)) pfj pfn
    = box_ q ⇒ let_ (q0,(q1,qs)) ← q;
               let_ (q0,qs) ← CNOT_at_i0 (S n) (S j) pfj' pfn' $ (q0,qs);
               output (q0,(q1,qs)).
Proof.
  intros. simpl. 
  replace (lt_S_n (S j) (S n) pfn) with pfn'.
  simpl.
  replace pfj' with (Nat.lt_0_succ j).
  reflexivity.
  * apply lt_hprop.
  * apply lt_hprop.
Qed.

  

Definition CNOT_at_j0 (n i : nat) (pf_j : 0 < i) (pf_n : i < n) 
                     : Box (n ⨂ Qubit) (n ⨂ Qubit).
Proof.
  gen n.
  induction i as [ | [ | i']]; intros n pf_n.
  * (* i = 0, j = 0 *) absurd False; auto. inversion pf_j.
  * (* i = 1, j = 0 *)
    destruct n as [ | [ | n']]. 
    { absurd False; auto. inversion pf_n. }
    { absurd False; auto. inversion pf_n. inversion H0. }
       refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q; 
                        let_ (q1,q0) ← CNOT $(q1,q0);
                        output (q0,(q1,qs))).
  * (* i = S (S i'), j = 0 *)
    destruct n as [ | [ | n']]. 
    { absurd False; auto. inversion pf_n. }
    { absurd False; auto. inversion pf_n. inversion H0. }
       refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q;
                        let_ (q0,qs) ← IHi _ (S n') _ $(q0,qs);
                        output (q0,(q1,qs))).
       + apply Nat.lt_0_succ.
       + apply lt_S_n. auto.
Defined.


Lemma CNOT_at_j0_WT : forall (n i : nat) (pf_i : 0 < i) (pf_n : i < n),
      Typed_Box (CNOT_at_j0 n i pf_i pf_n).
Proof.
  intros n i pf_i.
  gen n.
  induction i as [ | [ | i']]; intros n pf_n.
  * (* i = 0, j = 0 *) absurd False; auto. inversion pf_i.
  * (* i = 1, j = 0 *)
    destruct n as [ | [ | n']]. 
    { absurd False; auto. inversion pf_n. }
    { absurd False; auto. inversion pf_n. inversion H0. }
    simpl. type_check.
  * (* i = S (S i'), j = 0 *)
    destruct n as [ | [ | n']]. 
    { absurd False; auto. inversion pf_n. }
    { absurd False; auto. inversion pf_n. inversion H0. }
    set (pf_i' := (Nat.lt_0_succ _ : 0 < S i')).
    set (pf_n' := (lt_S_n _ _ pf_n : S i' < S n')).
    assert (IH : Typed_Box (CNOT_at_j0 (S n') (S i') pf_i' pf_n')).
    { intros. apply IHi. }
    clear IHi.
    type_check.
Qed. 

Lemma CNOT_at_j0_SS : forall n i
                             (pfi : 0 < S (S i)) (pfi' : 0 < S i)
                             (pfn : S (S i) < S (S n)) (pfn' : S i < S n),
      CNOT_at_j0 (S (S n)) (S (S i)) pfi pfn
    = box_ q ⇒ let_ (q0,(q1,qs)) ← q;
               let_ (q0,qs) ← CNOT_at_j0 (S n) (S i) pfi' pfn' $(q0,qs);
                output (q0,(q1,qs)).
Proof.
  intros. simpl. 
  replace (lt_S_n (S i) (S n) pfn) with pfn'.
  simpl.
  replace pfi' with (Nat.lt_0_succ i).
  reflexivity.
  * apply lt_hprop.
  * apply lt_hprop.
Qed.


Definition CNOT_at' (n i j : nat) 
                    (pf_i : i < n) (pf_j : j < n) (pf_i_j : i <> j) 
                    : Box (n ⨂ Qubit) (n ⨂ Qubit).
Proof.
  dependent induction n.
  - (* n = 0 *) absurd False; auto. inversion pf_i.
  - destruct i as [ | i'], j as [ | j'].
    * (* i = 0, j = 0 *) contradiction.
    * (* i = 0, j = S j' *) refine (CNOT_at_i0 (S n) (S j') _ pf_j).
      + apply Nat.lt_0_succ.
    * (* i = S i', j = 0 *) refine (CNOT_at_j0 (S n) (S i') _ pf_i).
      + apply Nat.lt_0_succ.
    * (* i = S i', j = S j' *)
    refine (box_ q ⇒ let_ (q0,qs) ← q;
                     let_ qs ←  IHn i' j' _ _ _ $qs;
                     output (q0,qs)).  
      + apply (lt_S_n _ _ pf_i).
      + apply (lt_S_n _ _ pf_j).
      + apply Nat.succ_inj_wd_neg. apply pf_i_j.
Defined.

Opaque CNOT_at_i0.
Opaque CNOT_at_j0.

Lemma CNOT_at'_WT : forall (n i j : nat) 
                    (pf_i : i < n) (pf_j : j < n) (pf_i_j : i <> j),
      Typed_Box (CNOT_at' n i j pf_i pf_j pf_i_j).
Proof.
  induction n; intros i j pf_i pf_j pf_i_j.
  - (* n = 0 *) absurd False; auto. inversion pf_i.
  - destruct i as [ | i'], j as [ | j'].
    * (* i = 0, j = 0 *) contradiction.
    * (* i = 0, j = S j' *) 
      apply CNOT_at_i0_WT.
    * (* i = S i', j = 0 *) 
      apply CNOT_at_j0_WT.
    * (* i = S i', j = S j' *) simpl.
      set (H' := Nat.succ_inj_wd_neg i' j').
      destruct H' eqn:H''.
      set (IH := IHn i' j' (lt_S_n i' n pf_i) (lt_S_n j' n pf_j) (n0 pf_i_j)).
      type_check.
Qed.


Definition CNOT_at (n i j : nat) : Box (n ⨂ Qubit) (n ⨂ Qubit).
  destruct (lt_dec i n) as [H_i_lt_n | H_i_ge_n];
    [ | exact id_circ (* ERROR *) ].
  destruct (lt_dec j n) as [H_j_lt_n | H_j_ge_n];
    [ | exact id_circ (* ERROR *) ].
  destruct (eq_nat_dec i j) as [H_i_j | H_i_j];
    [ exact id_circ (* ERROR *) | ].
  exact (CNOT_at' n i j H_i_lt_n H_j_lt_n H_i_j).
Defined.

Theorem CNOT_at_WT : forall n i j, Typed_Box (CNOT_at n i j).
Proof.
  intros n i j. 
  unfold CNOT_at.
  destruct (lt_dec i n) as [H_i_lt_n | H_i_ge_n] eqn:H_i_n;
    [ | type_check].
  destruct (lt_dec j n) as [H_j_lt_n | H_j_ge_n] eqn:H_j_n;
    [ | type_check]. 
  destruct (eq_nat_dec i j) as [H_i_j | H_i_j] eqn:H_i_j';
    [ type_check | ]. 
  apply CNOT_at'_WT.
Qed.

Lemma CNOT_at_0 : forall i j, CNOT_at 0 i j = id_circ.
Proof.
  intros i j.
  destruct i as [ | i'], j as [ | j'];
  compute; reflexivity.
Qed.

Lemma CNOT_at_1 : forall i j, CNOT_at 1 i j = id_circ.
Proof.
  intros i j.
  destruct i as [ | i'], j as [ | j']; compute; reflexivity.
Qed.
  
Lemma CNOT_at_n_0_SS : forall n' j', j' < n' -> 
      CNOT_at (S (S n')) 0 (S (S j'))
    = box_ q ⇒ let_ (q0,(q1,qs)) ← q;
               let_ (q0,qs) ← CNOT_at (S n') 0 (S j') $ (q0,qs);
               output (q0,(q1,qs)).
Proof.
  intros. 
  unfold CNOT_at.
  simpl. 
  destruct (lt_dec (S (S j')) (S (S n'))); [ | omega].
  destruct (lt_dec (S j') (S n')); [ | omega].
  erewrite CNOT_at_i0_SS. reflexivity.
Qed.
  
Lemma CNOT_at_n_SS_0 : forall n' i', i' < n' ->
      CNOT_at (S (S n')) (S (S i')) 0 
    = box_ q ⇒ let_ (q0,(q1,qs)) ← q;
               let_ (q0,qs) ← CNOT_at (S n') (S i') 0 $(q0,qs);
               output (q0,(q1,qs)).
Proof.
  intros.
  unfold CNOT_at.
  simpl. 
  destruct (lt_dec (S (S i')) (S (S n'))); [ | omega].
  destruct (lt_dec (S i') (S n')); [ | omega].
  erewrite CNOT_at_j0_SS. reflexivity.
Qed.




Lemma CNOT_at_at' : forall n i j (pfi : i < n) (pfj : j < n) (pf_i_j : i <> j),
      CNOT_at n i j = CNOT_at' n i j pfi pfj pf_i_j.
Proof.
  intros. unfold CNOT_at.
  destruct (lt_dec i n); [ | omega].
  destruct (lt_dec j n); [ | omega].
  destruct (Nat.eq_dec i j); [omega | ].
  replace l with pfi by apply lt_hprop.
  replace l0 with pfj by apply lt_hprop.
  replace n0 with pf_i_j by apply nat_neq_hprop.
  reflexivity.
Qed.
  
Lemma CNOT_at_n_S_S : forall n' i' j',
                      i' < n' -> j' < n' -> i' <> j' ->
      CNOT_at (S n') (S i') (S j')
    = box_ q ⇒ let_ (q0,qs) ← q;
               let_ qs ← CNOT_at n' i' j' $ output qs;
               output (q0,qs).
Proof.
  intros n' i' j' pf_i pf_j pf_i_j.
  erewrite CNOT_at_at'. 
  simpl.
  erewrite CNOT_at_at'.
  reflexivity.
  Unshelve.
  * omega.
  * omega.
  * omega.
Qed.

Definition Toffoli_at' n (i j k : Var) (pf_i : i < n) (pf_j : j < n) (pf_k : k < n)
                                      (pf_i_j : i <> j) (pf_i_k : i <> k) (pf_j_k : j <> k)
         : Box (n ⨂ Qubit) (n ⨂ Qubit).
Admitted.

Lemma Toffoli_at'_WT : forall n (i j k : Var) (pf_i : i < n) (pf_j : j < n) (pf_k : k < n)
                             (pf_i_j : i <> j) (pf_i_k : i <> k) (pf_j_k : j <> k),
      Typed_Box (Toffoli_at' n i j k pf_i pf_j pf_k pf_i_j pf_i_k pf_j_k).
Admitted.


Definition Toffoli_at n (i j k : Var) : Box (n ⨂ Qubit) (n ⨂ Qubit).
  destruct (lt_dec i n) as [H_i_lt_n | H_i_ge_n];
    [ | exact id_circ (* ERROR *) ].
  destruct (lt_dec j n) as [H_j_lt_n | H_j_ge_n];
    [ | exact id_circ (* ERROR *) ].
  destruct (lt_dec k n) as [H_k_lt_n | H_k_ge_n];
    [ | exact id_circ (* ERROR *) ].
  destruct (eq_nat_dec i j) as [H_i_j | H_i_j];
    [ exact id_circ (* ERROR *) | ].
  destruct (eq_nat_dec i k) as [H_i_k | H_i_k];
    [ exact id_circ (* ERROR *) | ].
  destruct (eq_nat_dec j k) as [H_j_k | H_j_k];
    [ exact id_circ (* ERROR *) | ].
  exact (Toffoli_at' n i j k H_i_lt_n H_j_lt_n H_k_lt_n H_i_j H_i_k H_j_k).
Defined.

Lemma Toffoli_at_WT : forall n (i j k : Var), Typed_Box (Toffoli_at n i j k).
Proof.
  intros n i j k. 
  unfold Toffoli_at.
  destruct (lt_dec i n); [ | type_check].
  destruct (lt_dec j n); [ | type_check].
  destruct (lt_dec k n); [ | type_check].
  destruct (eq_nat_dec i j); [ type_check | ]. 
  destruct (eq_nat_dec i k); [ type_check | ]. 
  destruct (eq_nat_dec j k); [ type_check | ]. 
  apply Toffoli_at'_WT.
Qed.


Definition strip_one_l_in {W W' : WType} (c : Box (One ⊗ W) W') : Box W W' :=
  box (fun p => unbox c ((),p)).
Lemma strip_one_l_in_WT : forall W W' (c : Box (One ⊗ W) W'), 
    Typed_Box c -> Typed_Box (strip_one_l_in c).
Proof. type_check. Qed.
Lemma strip_one_l_in_eq : forall W W' (c : Box (One ⊗ W) W') (ρ : Matrix (2^⟦W⟧)%nat (2^⟦W'⟧)%nat),
  denote_box true (strip_one_l_in c) ρ = denote_box true c ρ.
Proof.
  intros.
  unfold strip_one_l_in.
  matrix_denote. 
  unfold unbox. unfold denote_db_box.
  destruct c.
  simpl.
  reflexivity.
Qed.

Definition strip_one_l_out {W W' : WType} (c : Box W (One ⊗ W')) : Box W W' :=
  box_ p ⇒ let_ (_,p') ← unbox c p; output p'.
Lemma strip_one_l_out_WT : forall W W' (c : Box W (One ⊗ W')), 
    Typed_Box c -> Typed_Box (strip_one_l_out c).
Proof. type_check. Qed.
Lemma strip_one_l_out_eq : forall W W' (c : Box W (One ⊗ W')) (ρ : Matrix (2^⟦W⟧)%nat (2^⟦W'⟧)%nat),
  denote_box true (strip_one_l_out c) ρ = denote_box true c ρ.
Proof.
  intros.
  unfold strip_one_l_out.
  matrix_denote. 
  unfold unbox. unfold denote_db_box.
  destruct c.
  simpl.
Admitted.

Definition strip_one_r_in {W W' : WType} (c : Box (W ⊗ One) W') : Box W W' :=
  box (fun p => unbox c (p,())).
Lemma strip_one_r_in_WT : forall W W' (c : Box (W ⊗ One) W'), 
    Typed_Box c -> Typed_Box (strip_one_r_in c).
Proof. type_check. Qed.
Lemma strip_one_r_in_eq : forall W W' (c : Box (W ⊗ One) W') (ρ : Matrix (2^⟦W⟧)%nat (2^⟦W'⟧)%nat),
  denote_box true (strip_one_r_in c) ρ = denote_box true c ρ.
Proof.
  intros.
  unfold strip_one_r_in.
  matrix_denote. 
  unfold unbox. unfold denote_db_box.
  destruct c.
  simpl. rewrite Nat.add_0_r.
  reflexivity.
Qed.

Definition strip_one_r_out {W W' : WType} (c : Box W (W' ⊗ One)) : Box W W' :=
  box_ p ⇒ let_ (p',_) ← unbox c p; output p'.
Lemma strip_one_r_out_WT : forall W W' (c : Box W (W' ⊗ One)), 
    Typed_Box c -> Typed_Box (strip_one_r_out c).
Proof. type_check. Qed.
Lemma strip_one_r_out_eq : forall W W' (c : Box W (W' ⊗ One)) (ρ : Matrix (2^⟦W⟧)%nat (2^⟦W'⟧)%nat),
  denote_box true (strip_one_r_out c) ρ = denote_box true c ρ.
Proof.
  intros.
  unfold strip_one_r_out.
  matrix_denote. 
  unfold unbox. unfold denote_db_box.
  destruct c.
  simpl.
Admitted.

Fixpoint assert_at (b : bool) (n i : nat) {struct i}: Box (S n ⨂ Qubit) (n ⨂ Qubit) :=
  match i with
  | 0    => strip_one_l_out (assert b ∥ id_circ) 
  | S i' => match n with
           | 0 => strip_one_l_out (assert b ∥ id_circ) (* error *)
           | S n' => (id_circ ∥ assert_at b n' i')
           end
  end.

Lemma assert_at_WT : forall b n i, Typed_Box (assert_at b n i).
Proof.
  intros b n i.
  gen n.
  induction i.
  - type_check.
  - destruct n; simpl. 
    + type_check.
    + apply inPar_WT.
      type_check.
      apply IHi.
Qed.

Fixpoint init_at (b : bool) (n i : nat) {struct i}: Box (n ⨂ Qubit) (S n ⨂ Qubit) :=
  match i with 
  | 0    => strip_one_l_in (init b ∥ id_circ)
  | S i' => match n with
           | 0    => strip_one_l_in (init b ∥ id_circ) (* error *)
           | S n' => id_circ ∥ init_at b n' i'
           end
  end.

Lemma init_at_WT : forall b n i, Typed_Box (init_at b n i).
Proof.
  intros b n i.
  gen n.
  induction i.
  - type_check.
  - destruct n; simpl. 
    + type_check.
    + apply inPar_WT.
      type_check.
      apply IHi.
Qed.

Definition in_scope (n t i : nat) := i < n+t.
Definition in_target (n t i : nat) := (n <= i).
Definition in_source (n t i : nat) := i < n.
Lemma in_source_in_scope : forall n t i, in_source n t i -> in_scope n t i.
Proof.
  intros. apply lt_le_trans with (m := n); auto. omega. 
Qed.

Inductive gate_acts_on {m} k : Box (m ⨂ Qubit) (m ⨂ Qubit) -> Set :=
| X_on : forall (pf_k : k < m), gate_acts_on k (X_at m k pf_k)
| CNOT_on {i} : i < m -> k < m -> i <> k ->
                gate_acts_on k (CNOT_at m i k)
| Toffoli_on {i j} : i < m -> j < m -> k < m -> i <> j -> i <> k -> j <> k ->
                gate_acts_on k (Toffoli_at m i j k)
.

Inductive source_symmetric : forall n t, Box ((n+t) ⨂ Qubit) ((n+t) ⨂ Qubit) -> Set :=
| sym_id n t : source_symmetric n t id_circ
| sym_gate n t k c g : gate_acts_on k g ->
                       source_symmetric n t c ->
                       source_symmetric n t (g · c · g)
| target_gate_l n t k c g : gate_acts_on k g ->
                            source_symmetric n t c ->
                            n <= k -> (* k is in the target *)
                            source_symmetric n t (g · c)
| target_gate_r n t k c g : gate_acts_on k g ->
                            source_symmetric n t c ->
                            n <= k -> (* k is in the target *)
                            source_symmetric n t (c · g)
| sym_ancilla n t c b i : i < n ->
              source_symmetric (S n) t c ->
              source_symmetric n t (assert_at b (n+t) i · c · init_at b (n+t) i).


Fixpoint symmetric_reverse  n t c (pf_sym : source_symmetric n t c)
                            : Box ((n+t) ⨂ Qubit) ((n+t) ⨂ Qubit) :=
  match pf_sym with
  | sym_id _ _ => id_circ
  | sym_gate n t k c g pf_g pf_c => let c' := symmetric_reverse n t c pf_c in
                                      (g · c' · g)
  | target_gate_l n t k c g pf_g pf_c pf_k => 
                                      let c' := symmetric_reverse n t c pf_c in
                                      (c' · g)
  | target_gate_r n t k c g pf_g pf_c pf_k => let c' := symmetric_reverse n t c pf_c in
                                      (g · c')
  | sym_ancilla n t c b i pf_i pf_c => let c' := symmetric_reverse (S n) t c pf_c in
                                        (assert_at b (n+t) i · c' · init_at b (n+t) i)
  end.


Lemma symmetric_reverse_symmetric : forall n t c (pf_sym : source_symmetric n t c),
      source_symmetric n t (symmetric_reverse n t c pf_sym).
Proof.
  induction pf_sym.
  - apply sym_id.
  - eapply sym_gate; eauto.
  - apply target_gate_r with (k := k); auto.
  - apply target_gate_l with (k := k); auto.
  - apply sym_ancilla; auto.
Defined.

(* Symmetric gates are well-typed *)

Lemma gate_acts_on_WT : forall m (g : Box (m ⨂ Qubit) (m ⨂ Qubit)) k, 
                        gate_acts_on k g -> Typed_Box g.
Proof.
  intros m g k pf_g.
  induction pf_g.
  * apply unitary_at1_WT.
  * apply CNOT_at_WT.
  * apply Toffoli_at_WT.
Qed.

Lemma source_symmetric_WT : forall n t c,
      source_symmetric n t c ->
      Typed_Box c.
Proof.
  intros n t c pf_c.
  induction pf_c.
  * type_check.
  *  assert (Typed_Box g)
       by (eapply gate_acts_on_WT; eauto).
    repeat apply inSeq_WT; auto.
  * apply inSeq_WT; auto.
    eapply gate_acts_on_WT; eauto.
  * apply inSeq_WT; auto.
    eapply gate_acts_on_WT; eauto.
  * repeat apply inSeq_WT; auto.
    + apply init_at_WT; auto. 
    + apply assert_at_WT; auto. 
Qed.

(* Symmetric gates are no-ops on source wires *)

Definition noop_on (m i : nat) (c : Square_Box (S m ⨂ Qubit)) : Prop :=
  forall b, valid_ancillae_box' (assert_at b m i · c · init_at b m i).

Definition noop_source (n t : nat) : (Square_Box ((n+t) ⨂ Qubit)) -> Prop :=
  match n with
  | 0 => fun _ => True
  | S n' => fun c => 
            forall i, i < S n' -> noop_on _ i c
  end.

Lemma gate_acts_on_noop_at : forall m g k i,
      @gate_acts_on (S m) k g -> 
      i <> k -> i < S m ->
      noop_on m i g.
Proof.
  intros m g k i pf_g pf_i_k pf_i.
  dependent destruction pf_g.
  * admit.
  * admit.
  * admit.
Admitted.

(* Move to DBCircuits *)
Lemma fresh_state_ntensor : forall n (Γ : Ctx), fresh_state (n ⨂ Qubit) (Valid Γ) = 
                                           Valid (Γ ++ List.repeat (Some Qubit) n).
Proof.                            
  induction n. 
  - intros. simpl. rewrite app_nil_r; reflexivity.
  - intros. simpl. rewrite IHn. rewrite <- app_assoc. reflexivity.
Qed.

(* Strong sematics for init and assert *)
Open Scope matrix_scope.
Lemma init_at_spec_strong : forall b n i (ρ : Square (2^n)), i <= n ->
  ⟦init_at b n i⟧ ρ = ('I_ (2^i) ⊗ bool_to_ket b ⊗ 'I_ (2^ (n-i))) × ρ × 
                     ('I_ (2^i) ⊗ (bool_to_ket b)† ⊗ 'I_ (2^ (n-i))).
Admitted.

(* Safe semantics *)
Lemma assert_at_spec_strong : forall b n i (ρ : Square (2^n)), i <= n ->
  ⟦assert_at b n i⟧ ρ = 
  ('I_ (2^i) ⊗ ⟨0| ⊗ 'I_ (2^ (n-i))) × ρ × ('I_ (2^i) ⊗ |0⟩ ⊗ 'I_ (2^ (n-i))) .+ 
  ('I_ (2^i) ⊗ ⟨1| ⊗ 'I_ (2^ (n-i))) × ρ × ('I_ (2^i) ⊗ |1⟩ ⊗ 'I_ (2^ (n-i))).
Admitted.

Lemma assert_init_at_id : forall b m i, i < S m ->
    (assert_at b m i · init_at b m i  ≡ id_circ)%qc.
Proof. 
  intros b m i Lt ρ M. simpl.
  simpl_rewrite id_circ_Id; auto with wf_db.
  simpl_rewrite inSeq_correct; [ | apply assert_at_WT | apply init_at_WT].
  unfold compose_super.
  simpl_rewrite (init_at_spec_strong b m i); [|omega].
  simpl_rewrite (assert_at_spec_strong b m i); [|omega].
  gen ρ. rewrite size_ntensor. simpl. rewrite Nat.mul_1_r.
  intros ρ M.
  repeat rewrite Mmult_assoc.
  Msimpl.  
  match goal with
  | [|- @Mmult ?a ?b ?c ?A (@Mmult ?d ?e ?f ?B ?C) .+ _ = _] => 
    setoid_rewrite <- (Mmult_assoc _ _ _ _ A B C)                                    
  end.
  Msimpl.
  destruct b; simpl.
  - replace (⟨0| × |1⟩) with (Zero 1 1) by crunch_matrix.
    rewrite kron_0_r, kron_0_l. 
    rewrite Mmult_0_l, Mplus_0_l. (* add to dbs *)
    replace (⟨1| × |1⟩) with ('I_1).
    2: crunch_matrix; bdestruct (S x <? 1); [omega|rewrite andb_false_r; easy].
    Msimpl.
    setoid_rewrite (id_kron (2^i) (2^(m-i))).
    rewrite Nat.mul_1_r.
    replace (2^i * 2^(m-i)) with (2^m) by unify_pows_two. 
    Msimpl.
    rewrite <- Mmult_assoc.
    setoid_rewrite kron_mixed_product.
    Msimpl.
    setoid_rewrite kron_mixed_product.
    Msimpl.
    replace (⟨1| × |1⟩) with ('I_1).
    2: crunch_matrix; bdestruct (S x <? 1); [omega|rewrite andb_false_r; easy].
    rewrite id_kron.
    rewrite Nat.mul_1_r.
    rewrite id_kron.
    unify_pows_two.
    replace (i + (m - i)) with m by omega.    
    rewrite Mmult_1_l by (auto with wf_db).
    reflexivity.
  - replace (⟨0| × |1⟩) with (Zero 1 1) by crunch_matrix.
    rewrite kron_0_r, kron_0_l. 
    repeat rewrite Mmult_0_r. rewrite Mplus_0_r.
    replace (⟨0| × |0⟩) with ('I_1).
    2: crunch_matrix; bdestruct (S x <? 1); [omega|rewrite andb_false_r; easy].
    Msimpl.
    setoid_rewrite (id_kron (2^i) (2^(m-i))).
    rewrite Nat.mul_1_r.
    replace (2^i * 2^(m-i)) with (2^m) by unify_pows_two. 
    Msimpl.
    reflexivity.
Qed.
Open Scope circ_scope.
Lemma init_assert_at_valid : forall b m i W1 (c : Box W1 (S m ⨂ Qubit)), 
    i < S m ->
    valid_ancillae_box' (assert_at b m i · c) ->
    init_at b m i · assert_at b m i · c ≡ c.
Admitted.

(* does equivalence talk only about safe equivalence, or equivalence at either semantics? *)
Lemma valid_ancillae_box'_equiv : forall W1 W2 (b1 b2 : Box W1 W2), b1 ≡ b2 ->
      valid_ancillae_box' b1 <-> valid_ancillae_box' b2.
Admitted.

(* Follows from uniformity of trace *)
Lemma valid_inSeq : forall w1 w2 w3 (c1 : Box w1 w2) (c2 : Box w2 w3),
      Typed_Box c1 -> Typed_Box c2 ->
      valid_ancillae_box' c1 -> valid_ancillae_box' c2 ->
      valid_ancillae_box' (c2 · c1).
Proof.
  intros w1 w2 w3 c1 c2 pf_c1 pf_c2 valid1 valid2. unfold valid_ancillae_box.
  set (H := inSeq_correct _ _ _ c2 c1 pf_c2 pf_c1).
  simpl in H.
  unfold valid_ancillae_box' in *.
  intros ρ M.
  unfold inSeq.
  unfold denote_box.  
Admitted.

(* Similar to "compile_typing" in Oracles.v, move elsewhere *)
Ltac simple_typing lem := 
  repeat match goal with
  | _ => apply inSeq_WT
  | _ => apply inPar_WT
  | _ => apply id_circ_WT
  | _ => apply boxed_gate_WT
  | _ => apply init_at_WT
  | _ => apply assert_at_WT
  | [|- Typed_Box (CNOT_at ?n ?x ?y)] => 
      specialize (CNOT_at_WT n x y); simpl; easy
  | [|- Typed_Box (Toffoli_at ?n ?x ?y ?z )] => 
      specialize (Toffoli_at_WT n x y z); simpl; easy
  | _ => apply TRUE_WT
  | _ => apply FALSE_WT
  | [H : forall (Γ : Ctx), Typed_Box _ |- _]  => apply H
  | [H : Typed_Box _ |- _]  => apply H
  | _ => apply lem 
  end.

Lemma noop_source_inSeq : forall n t c1 c2,
    Typed_Box c1 -> Typed_Box c2 ->
    noop_source n t c1 ->
    noop_source n t c2 ->
    noop_source n t (c2 · c1).
Proof.
  intros n t c1 c2 typed_c1 typed_c2 H_c1 H_c2.
  destruct n as [ | n]; simpl in *; auto. fold (n+t) in *.
  intros x pf_x b.
  set (INIT := init_at b (n+t) x).
  set (ASSERT := assert_at b (n+t) x).
  assert (H' : c1 · INIT ≡ INIT · ASSERT · c1 · INIT).
  { symmetry. apply init_assert_at_valid.
    + omega.
    + apply H_c1; auto.
  }
  apply valid_ancillae_box'_equiv 
    with (b2 := (ASSERT · c2 · INIT) · (ASSERT · c1 · INIT)).
  { repeat rewrite <- inSeq_assoc.
    apply HOAS_Equiv_inSeq; simple_typing False; try easy. 
    apply HOAS_Equiv_inSeq; simple_typing False; try easy. 
  }
  assert (x < S (n+t)) by omega. 
  assert (typed_init : Typed_Box INIT) by simple_typing False.
  assert (typed_assert : Typed_Box ASSERT) by simple_typing False.
  apply valid_inSeq.
    - repeat apply inSeq_WT;  auto. 
    - repeat apply inSeq_WT;  auto. 
    - apply H_c1; auto.
    - apply H_c2; auto.
Qed.



Lemma denote_box_id_circ : forall b w ρ, WF_Matrix _ _ ρ ->
      denote_box b (id_circ : Box w w) ρ = ρ.
Proof.
  intros b w ρ.
  simpl. autounfold with den_db. simpl.
  Search hoas_to_db_pat.
  rewrite hoas_to_db_pat_fresh_empty.
  rewrite denote_pat_fresh_id.
  rewrite pad_nothing.
  apply super_I.
Qed.

Lemma valid_id_circ : forall w, valid_ancillae_box' (id_circ : Box w w).
Proof.
  intros w ρ Hρ.
  rewrite denote_box_id_circ.
  * apply mixed_state_trace_1; auto.
  * apply WF_Mixed; auto.
Qed.

Lemma symmetric_gate_noop_source : forall n t k g c,
    gate_acts_on k g ->
    noop_source n t c ->
    noop_source n t (g · c · g).
Admitted.

(* not sure how to prove this *)
Lemma symmetric_ancilla_noop_source : forall n t k c b,
      k < S n ->
      noop_source (S n) t c ->
      noop_source n t (assert_at b (n+t) k · c · init_at b (n+t) k).
Admitted.


Lemma source_symmetric_noop : forall n t c,
      source_symmetric n t c -> noop_source n t c.
Proof.
  intros n t c pf_c.
  induction pf_c.
  * (* id *) destruct n as [ | n]; simpl; auto; intros x pf_x b. fold plus.
    rewrite inSeq_id_l.
    apply valid_ancillae_box'_equiv with (b2 := id_circ).
    + apply assert_init_at_id. omega.
    + apply valid_id_circ.
  * (* sym_source *)
    assert (Typed_Box g) by (eapply gate_acts_on_WT; eauto).
    assert (Typed_Box c) by (apply source_symmetric_WT; auto).
    apply symmetric_gate_noop_source with (k := k); auto.
  * (* sym_target_l *)
    apply noop_source_inSeq; auto.
    + apply source_symmetric_WT; auto.
    + eapply gate_acts_on_WT; eauto.
    + destruct n as [ | n]; simpl; auto; intros i pf_i. fold plus.
      apply gate_acts_on_noop_at with (k := k); auto. 
      ++ omega.
      ++ omega.
  * (* sym_target_r *)
    apply noop_source_inSeq; auto.
    + eapply gate_acts_on_WT; eauto.
    + apply source_symmetric_WT; auto.
    + destruct n as [ | n]; simpl; auto; intros i pf_i. fold plus.
      apply gate_acts_on_noop_at with (k := k); auto. 
      ++ omega.
      ++ omega.
  * (* sym_ancilla *)
    apply symmetric_ancilla_noop_source; auto.
Qed.

(* The noop property implies actual reversibility *)

Lemma gate_acts_on_reversible : forall m g k (pf_g : @gate_acts_on m k g),
      g · g ≡ id_circ.
Admitted.

(* Version without typing restrictions *)
Lemma HOAS_Equiv_inSeq' :
forall (w1 w2 w3 : WType) (b1 b1' : Box w1 w2) (b2 b2' : Box w2 w3),
  b1 ≡ b1' -> b2 ≡ b2' -> b1;; b2 ≡ b1';; b2'.
Admitted.

Lemma symmetric_reversible : forall n t c (pf_sym : source_symmetric n t c),
      symmetric_reverse n t c pf_sym · c ≡ id_circ.
Proof.
  induction pf_sym; simpl.
  - (* id *) rewrite inSeq_id_l. reflexivity.

  - (* source *)
    transitivity (g · (symmetric_reverse n t c pf_sym · (g · g) · c) · g).
    { repeat rewrite inSeq_assoc; reflexivity. }
    transitivity (g · (symmetric_reverse n t c pf_sym · c) · g).
    { apply HOAS_Equiv_inSeq'; [ | reflexivity].
      apply HOAS_Equiv_inSeq'; [ reflexivity | ].
      apply HOAS_Equiv_inSeq'; [ | reflexivity ].      
      rewrite HOAS_Equiv_inSeq'; [ | reflexivity | eapply gate_acts_on_reversible; eauto].
      rewrite inSeq_id_l; reflexivity.
    }
    transitivity (g · g); [ | eapply gate_acts_on_reversible; eauto].
    apply HOAS_Equiv_inSeq'; [ | reflexivity].
    rewrite HOAS_Equiv_inSeq'; [ | reflexivity | apply IHpf_sym].
    rewrite inSeq_id_l; reflexivity.


  - (* target_l *)
      replace (((symmetric_reverse n t c pf_sym) · g) · g · c)
         with (symmetric_reverse n t c pf_sym · (g · g) · c)
         by (repeat rewrite inSeq_assoc; auto).
      transitivity ((symmetric_reverse n t c pf_sym) · c).
      { apply HOAS_Equiv_inSeq'; [ | reflexivity].
        rewrite HOAS_Equiv_inSeq'; [ | reflexivity |  eapply gate_acts_on_reversible; eauto].  
        rewrite inSeq_id_l.
        reflexivity.
      }
      apply IHpf_sym.
  - (* target_r *) 
    transitivity (g · (symmetric_reverse n t c pf_sym · c) · g).
    { repeat rewrite inSeq_assoc; reflexivity. }
    transitivity (g · g); [ |  eapply gate_acts_on_reversible; eauto]. 
    apply HOAS_Equiv_inSeq'; [ | reflexivity].
    rewrite HOAS_Equiv_inSeq'; [ rewrite inSeq_id_l; reflexivity | reflexivity | ].
    apply IHpf_sym.

  - (* ancilla *)
    set (close := assert_at b (n + t) i).
    set (open := init_at b (n + t) i).
    set (c' := symmetric_reverse (S n) t c pf_sym).
    transitivity (close · (c' · (open · close · c · open))).
    { repeat (rewrite inSeq_assoc); reflexivity. }
    transitivity (close · (c' · c) · open).
    { repeat rewrite <- inSeq_assoc. 
      apply HOAS_Equiv_inSeq'; [ | reflexivity].
      apply HOAS_Equiv_inSeq'; [ | reflexivity ].
      apply init_assert_at_valid.
      { omega. }
      set (H := source_symmetric_noop (S n) t c pf_sym).
      simpl in H.
      apply H; auto.
   }
   transitivity (close · id_circ · open).
   { apply HOAS_Equiv_inSeq'; [ | reflexivity].
     apply HOAS_Equiv_inSeq'; [ reflexivity | ].
     apply IHpf_sym.
   }
   rewrite inSeq_id_l.
   apply assert_init_at_id.
   omega.
Qed.
Close Scope circ_scope.