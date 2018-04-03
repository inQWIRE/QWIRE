Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASLib.
Require Import Denotation.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import Reversible.
Require Import Ancilla.

Require Import List.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.
Delimit Scope matrix_scope with M.

Close Scope matrix_scope.

(**********************)
(* Syntactic Property *)
(**********************)

Close Scope matrix_scope.
Open Scope circ_scope.
Open Scope nat_scope.

Ltac gdep H := (generalize dependent H).

Definition unitary_at1 n (U : Unitary Qubit) (i : Var) (pf : i < n)
        : Box (n ⨂ Qubit) (n ⨂ Qubit).
Proof.
  gdep U. gdep n.
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
  intros n U i pf. gdep U. gdep n.
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
Proof.
  intros.
  omega.
Qed.

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
  gdep n.
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
  gdep n.
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
  gdep n.
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
  gdep n.
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
Proof.
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

Definition Toffoli_at n (i j k : Var) (pf_i : i < n) (pf_j : j < n) (pf_k : k < n)
                                      (pf_i_j : i <> j) (pf_i_k : i <> k) (pf_j_k : j <> k)
         : Box (n ⨂ Qubit) (n ⨂ Qubit).
Admitted.


Lemma Toffoli_at_WT : forall n (i j k : Var) (pf_i : i < n) (pf_j : j < n) (pf_k : k < n)
                             (pf_i_j : i <> j) (pf_i_k : i <> k) (pf_j_k : j <> k),
      Typed_Box (Toffoli_at n i j k pf_i pf_j pf_k pf_i_j pf_i_k pf_j_k).
Admitted.


Definition assert (b : bool) : Gate Qubit One := if b then assert1 else assert0.

Definition assert_at' (b : bool) (n : nat) (i : nat) (pf_i : i < S n) 
         : Box (S n ⨂ Qubit) (n ⨂ Qubit).
Proof.
  gdep n.
  induction i as [ | i]; intros n pf_i.
  * (* i = 0 *)
    refine (box_ q ⇒ let_ (q,qs) ← q; 
                     let_ _ ← assert b $q; 
                     output qs).
  * (* i = S i' *)
    destruct n as [ | n].
    { absurd False; auto. inversion pf_i. subst. inversion H0. }
    simpl.
    refine (box_ q ⇒ let_ (q,qs) ← q; 
                     let_ qs ← IHi n _ $ qs;
                     output (q,qs)). 
    apply lt_S_n; auto.
Defined.

Definition assert_at (b : bool)(n : nat) (i : nat) 
         : Box (S n ⨂ Qubit) (n ⨂ Qubit).
Proof.
  destruct (lt_dec i (S n)) as [ pf_i | pf_i ].
  * (* i < S n *) exact (assert_at' b n i pf_i).
  * (* i >= S n *) simpl. 
     exact (box_ qs' ⇒ let_ (q,qs) ← qs';
                       let_ _ ← assert b $q;
                       output qs). (* ERROR *)
Defined.

Lemma assert_at_S : forall b n i (pf_i : i < S n),
    assert_at b (S n) (S i) = box_ q ⇒ let_ (q,qs) ← q; 
                                       let_ qs ← assert_at b n i $ qs;
                                       output (q,qs).
Proof.
  intros.
  simpl. unfold assert_at. simpl.
  destruct (lt_dec (S i) (S (S n))); [ | omega].
  destruct (lt_dec i (S n)); [ | omega].
  replace (lt_S_n i (S n) l) with l0; auto.
  apply lt_hprop.
Qed.

Lemma assert_at_WT : forall b n i (pf : (i < S n)%nat), 
                            Typed_Box (assert_at b n i).
Proof.
  intros.  
  gdep n.
  induction i as [ | i]; intros n pf_i.
  * (* i = 0 *)
    type_check.
  * (* i = S i' *)
    destruct n as [ | n]; [omega | ].
    assert (pf_i' : i < S n) by omega.
    set (IH := IHi n pf_i').
    rewrite (assert_at_S b _ _ pf_i').
    type_check.
Qed.

Definition init_at' (b : bool) (n : nat) (i : nat) (pf_i : i < S n) 
                  : Box (n ⨂ Qubit) (S n ⨂ Qubit).
  gdep n.
  induction i as [ | i]; intros n pf_i.
  * (* i = 0 *)
    refine (box_ qs ⇒ let_ q ← init b $();
                      output (q,qs)).
  * (* i = S i' *)
    destruct n as [ | n].
    { absurd False; auto. inversion pf_i. subst. inversion H0. }
    simpl.
    refine (box_ q ⇒ let_ (q,qs) ← q; 
                     let_ qs ← IHi n _ $ qs;
                     output (q,qs)). 
    apply lt_S_n; auto.
Defined.

Definition init_at (b : bool) (n : nat) (i : nat) : Box (n ⨂ Qubit) (S n ⨂ Qubit).
Proof.
  destruct (lt_dec i (S n)) as [pf_i | pf_i].
  * (* i < S n *) exact (init_at' b n i pf_i).
  * (* i >= S n *) exact (box_ qs ⇒ let_ q ← init b $();
                                    output (q,qs)). (* ERROR *)
Defined.

Lemma init_at'_S : forall b n i (pf_i : i < S n) (pf_i' : S i < S (S n)),
    init_at' b (S n) (S i) pf_i' = box_ q ⇒ let_ (q,qs) ← q; 
                                           let_ qs ← init_at' b n i pf_i $ qs;
                                           output (q,qs).
Proof.
  intros.
  simpl.
  replace (lt_S_n i (S n) pf_i') with pf_i by apply lt_hprop; auto.
Qed.
Lemma init_at_S : forall b n i, i < S n ->
    init_at b (S n) (S i) = box_ q ⇒ let_ (q,qs) ← q;
                                     let_ qs ← init_at b n i $qs;
                                     output (q,qs).
Proof.
  intros.
  unfold init_at. simpl.
  destruct (lt_dec (S i) (S (S n))); [ | omega].
  destruct (lt_dec i (S n)); [ | omega].
  replace (lt_S_n i (S n) l) with l0 by apply lt_hprop.
  reflexivity.
Qed.

Lemma init_at_WT : forall b n i (pf : (i < S n)%nat), Typed_Box (init_at b n i).
Proof.
  intros.
  gdep n.
  induction i as [ | i]; intros n pf_i.
  * (* i = 0 *)
    type_check.
  * (* i = S i' *)
    destruct n as [ | n]; [omega | ].
    assert (pf_i' : i < S n) by omega.
    set (IH := IHi n pf_i').
    rewrite (init_at_S b _ _ pf_i').
    type_check.
Qed.

Definition in_scope (n t i : nat) := i < n+t.
Definition in_target (n t i : nat) := (n <= i).
Definition in_source (n t i : nat) := i < n.
Lemma in_source_in_scope : forall n t i, in_source n t i -> in_scope n t i.
Proof.
  intros. apply lt_le_trans with (m := n); auto. omega. 
Qed.

Inductive Symmetric_Gate_Target : forall n t, Box ((n+t) ⨂ Qubit) ((n+t) ⨂ Qubit) -> Set :=
| X_target : forall n t i (pf_i : in_scope n t i )
                          (pf_target_i : in_target n t i),
                           Symmetric_Gate_Target n t (X_at (n+t) i pf_i)
| CNOT_target : forall n t i j
                       (pf_i : in_scope n t i) (pf_j : in_scope n t j)
                       (pf_i_j : i <> j)
                       (pf_target_j : in_target n t j),
                       Symmetric_Gate_Target n t (CNOT_at (n+t) i j)
| Toffoli_target : forall n t i j k
                     (pf_i : in_scope n t i) (pf_j : in_scope n t j) (pf_k : in_scope n t k)
                     (pf_i_j : i <> j) (pf_i_k : i <> k) (pf_j_k : j <> k)
                     (pf_target_k : in_target n t k),
                     Symmetric_Gate_Target n t (Toffoli_at _ i j k pf_i pf_j pf_k pf_i_j pf_i_k pf_j_k)
.
Inductive Symmetric_Gate_Source : forall n t, Box ((n+t) ⨂ Qubit) ((n+t) ⨂ Qubit) -> Set :=
| X_source : forall n t i (pf_i : in_scope n t i),
                           Symmetric_Gate_Source n t (X_at (n+t) i pf_i)
| CNOT_source : forall n t i j
                       (pf_i : in_scope n t i) (pf_j : in_scope n t j)
                       (pf_i_j : i <> j),
                       Symmetric_Gate_Source n t (CNOT_at (n+t) i j)
| Toffoli_source : forall n t i j k
                     (pf_i : in_scope n t i) (pf_j : in_scope n t j) (pf_k : in_scope n t k)
                     (pf_i_j : i <> j) (pf_i_k : i <> k) (pf_j_k : j <> k),
                     Symmetric_Gate_Source n t (Toffoli_at _ i j k pf_i pf_j pf_k pf_i_j pf_i_k pf_j_k)
.

Inductive Symmetric_Box : forall n t, Box ((n+t) ⨂ Qubit) ((n+t) ⨂ Qubit) -> Set :=
| sym_id : forall n t, Symmetric_Box n t id_circ
| sym_target_l : forall n t g c, 
                       Symmetric_Gate_Target n t g ->
                       Symmetric_Box n t c ->
                       Symmetric_Box n t (g · c)
| sym_target_r : forall n t g c, 
                       Symmetric_Gate_Target n t g ->
                       Symmetric_Box n t c ->
                       Symmetric_Box n t (c · g)
| sym_source   : forall n t g c, 
                       Symmetric_Gate_Source n t g ->
                       Symmetric_Box n t c ->
                       Symmetric_Box n t (g · c · g)
| sym_ancilla  : forall n t c,
                       Symmetric_Box (S n) t c -> 
                       forall (b : bool) i (pf : in_source (S n) t i),
                       Symmetric_Box n t (assert_at b (n+t) i · c · init_at b (n+t) i)
.
Fixpoint symmetric_reverse  n t c (pf_sym : Symmetric_Box n t c)
                            : Box ((n+t) ⨂ Qubit) ((n+t) ⨂ Qubit) :=
  match pf_sym with
  | sym_id _ _ => id_circ
  | sym_target_l n t g c pf_g pf_c => let c' := symmetric_reverse n t c pf_c in
                                      (c' · g)
  | sym_target_r n t g c pf_g pf_c => let c' := symmetric_reverse n t c pf_c in
                                      (g · c')
  | sym_source   n t g c pf_g pf_c => let c' := symmetric_reverse n t c pf_c in
                                      (g · c' · g)
  | sym_ancilla  n t c pf_c b i pf_i => let c' := symmetric_reverse (S n) t c pf_c in
                                        (assert_at b (n+t) i · c' · init_at b (n+t) i)
  end.

Lemma symmetric_reverse_symmetric : forall n t c (pf_sym : Symmetric_Box n t c),
      Symmetric_Box n t (symmetric_reverse n t c pf_sym).
Proof.
  induction pf_sym.
  - apply sym_id.
  - apply sym_target_r; auto.
  - apply sym_target_l; auto.
  - apply sym_source; auto.
  - apply sym_ancilla; auto.
Defined.

(* Symmetric gates are well-typed *)

Lemma Symmetric_Gate_Target_WT : forall n t c, Symmetric_Gate_Target n t c -> Typed_Box c.
Proof.
  intros n t c pf_c.
  induction pf_c.
  * apply unitary_at1_WT.
  * apply CNOT_at_WT.
  * apply Toffoli_at_WT.
Qed.

Lemma Symmetric_Gate_Source_WT : forall n t c, Symmetric_Gate_Source n t c -> Typed_Box c.
Proof.
  intros n t c pf_c.
  induction pf_c.
  * apply unitary_at1_WT.
  * apply CNOT_at_WT.
  * apply Toffoli_at_WT.
Qed.

Lemma Symmetric_Box_WT : forall n t c, Symmetric_Box n t c -> Typed_Box c.
Proof.
  intros n t c pf_c.
  induction pf_c.
  * type_check.
  * apply inSeq_WT; auto.
    apply Symmetric_Gate_Target_WT; auto.
  * apply inSeq_WT; auto.
    apply Symmetric_Gate_Target_WT; auto.
  * assert (Typed_Box g) by (apply Symmetric_Gate_Source_WT; auto).
    repeat apply inSeq_WT; auto.
  * repeat apply inSeq_WT; auto.
    + apply init_at_WT; auto. unfold in_source in *. omega.
    + apply assert_at_WT; auto. unfold in_source in *. omega.
Qed.

(* Symmetric gates are no-ops on source wires *)

Definition noop_source (n t : nat) : (Square_Box ((n+t) ⨂ Qubit)) -> Prop :=
  match n with
  | 0 => fun _ => True
  | S n' => fun c =>
            forall b i, i < S n' ->
                valid_ancillae_box' (assert_at b (n'+t) i · c · init_at b (n'+t) i)
  end.

Lemma Symmetric_Gate_Target_noop_at : forall n t c,
      Symmetric_Gate_Target n t c -> noop_source n t c.
Proof.
  intros n t c pf_c.
  induction pf_c; destruct n as [ | n]; simpl; auto; intros b x pf_x.
  * (* X *)
    (* we know x <> i, so x is disjoint from the domain of X_at *)
    assert (x <> i) by (unfold in_target in pf_target_i; omega).
    admit.
  * (* CNOT *)
    (* we know x <> j *)
    (* either x = i or CNOT_at does not affect x *)
    destruct (Nat.eq_dec i x).
    + (* i = x *) subst. admit.
    + (* i <> x *) admit.
  * (* Toffoli *) 
    assert (x <> k) by (unfold in_target in pf_target_k; omega).
    destruct (Nat.eq_dec i x).
    + (* i = x *) subst. admit.
    + destruct (Nat.eq_dec j x).
      ++ (* j = x *) subst. admit.
      ++ (* i <> x, j <> x *) admit.
Admitted.


Lemma assert_init_at_id : forall b m i, i < S m ->
    assert_at b m i · init_at b m i  ≡ id_circ.
Admitted.

Lemma init_assert_at_valid : forall b m i W1 (c : Box W1 (S m ⨂ Qubit)), 
    i < S m ->
    valid_ancillae_box' (assert_at b m i · c) ->
    init_at b m i · assert_at b m i · c ≡ c.
Admitted.

(* does equivalence talk only about safe equivalence, or equivalence at either semantics? *)
Lemma valid_ancillae_box'_equiv : forall W1 W2 (b1 b2 : Box W1 W2), b1 ≡ b2 ->
      valid_ancillae_box' b1 <-> valid_ancillae_box' b2.
Admitted.

(* IS THIS TRUE?? *)
Lemma valid_inSeq : forall w1 w2 w3 (c1 : Box w1 w2) (c2 : Box w2 w3),
      Typed_Box c1 -> Typed_Box c2 ->
      valid_ancillae_box' c1 -> valid_ancillae_box' c2 ->
      valid_ancillae_box' (c2 · c1).
Proof.
  intros w1 w2 w3 c1 c2 pf_c1 pf_c2 valid1 valid2. unfold valid_ancillae_box.
  set (H := inSeq_correct _ _ _ c2 c1 pf_c2 pf_c1).
  simpl in H.
Admitted.


Lemma noop_source_inSeq : forall n t c1 c2,
    Typed_Box c1 -> Typed_Box c2 ->
    noop_source n t c1 ->
    noop_source n t c2 ->
    noop_source n t (c2 · c1).
Proof.
  intros n t c1 c2 typed_c1 typed_c2 H_c1 H_c2.
  destruct n as [ | n]; simpl in *; auto.
  intros b x pf_x pf_t.
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
    apply HOAS_Equiv_inSeq; [ | reflexivity].
    apply HOAS_Equiv_inSeq; [ | reflexivity].
    apply H'.
  }
  assert (x < S (n+t)) by omega. 
  assert (typed_init : Typed_Box INIT) by (apply init_at_WT; auto).
  assert (typed_assert : Typed_Box ASSERT) by (apply assert_at_WT; auto).
  apply valid_inSeq.
    - repeat apply inSeq_WT;  auto. 
    - repeat apply inSeq_WT;  auto. 
    - apply H_c1; auto.
    - apply H_c2; auto.
Qed.

Lemma Symmetric_Gate_Source_noop_at : forall n t c g, 
      Symmetric_Box n t c ->
      noop_source n t c ->
      noop_source n t (g · c · g).
Admitted.

Lemma Symmetric_Ancilla_noop_at : forall n t c i b,
    in_source (S n) t i ->
    Symmetric_Box (S n) t c ->
    noop_source (S n) t c ->
    noop_source n t (assert_at b (n+t) i · c · init_at b (n+t) i).
Admitted.


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

Lemma Symmetric_Box_noop_at : forall n t c, Symmetric_Box n t c -> noop_source n t c.
Proof.
  intros n t c pf_c.
  induction pf_c.
  * (* id *) destruct n as [ | n]; simpl; auto; intros b' x pf_x pf_t.
    rewrite inSeq_id_l.
    apply valid_ancillae_box'_equiv with (b2 := id_circ).
    + apply assert_init_at_id. omega.
    + apply valid_id_circ.
  * (* sym_target_l *)
    apply noop_source_inSeq; auto.
    + apply Symmetric_Box_WT; auto.
    + apply Symmetric_Gate_Target_WT; auto.
    + apply Symmetric_Gate_Target_noop_at; auto.
  * (* sym_target_r *) 
    apply noop_source_inSeq; auto.
    + apply Symmetric_Gate_Target_WT; auto.
    + apply Symmetric_Box_WT; auto.
    + apply Symmetric_Gate_Target_noop_at; auto.
  * (* sym_source *)
    assert (Typed_Box g) by (apply Symmetric_Gate_Source_WT; auto).
    assert (Typed_Box c) by (apply Symmetric_Box_WT; auto).
    apply Symmetric_Gate_Source_noop_at; auto.
  * (* sym_ancilla *)
    apply Symmetric_Ancilla_noop_at; auto.
Qed.

(* The noop property implies actual reversibility *)

Lemma symmetric_gate_target_reversible : forall n t g (pf_g : Symmetric_Gate_Target n t g),
      g · g ≡ id_circ.
Proof.
  intros n t g pf_g.
  induction pf_g.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma symmetric_gate_source_reversible : forall n t g (pf_g : Symmetric_Gate_Source n t g),
      g · g ≡ id_circ.
Admitted.


Lemma symmetric_reversible : forall n t c (pf_sym : Symmetric_Box n t c),
      symmetric_reverse n t c pf_sym · c ≡ id_circ.
Proof.
  induction pf_sym; simpl.
  - (* id *) rewrite inSeq_id_l. reflexivity.
  - (* target_l *)
      replace (((symmetric_reverse n t c pf_sym) · g) · g · c)
         with (symmetric_reverse n t c pf_sym · (g · g) · c)
         by (repeat rewrite inSeq_assoc; auto).
      transitivity ((symmetric_reverse n t c pf_sym) · c).
      { apply HOAS_Equiv_inSeq; [ | reflexivity].
        rewrite HOAS_Equiv_inSeq; [ | reflexivity | apply symmetric_gate_target_reversible; auto].  
        rewrite inSeq_id_l.
        reflexivity.
      }
      apply IHpf_sym.
  - (* target_r *) 
    transitivity (g · (symmetric_reverse n t c pf_sym · c) · g).
    { repeat rewrite inSeq_assoc; reflexivity. }
    transitivity (g · g); [ | apply symmetric_gate_target_reversible; auto ]. 
    apply HOAS_Equiv_inSeq; [ | reflexivity].
    rewrite HOAS_Equiv_inSeq; [ rewrite inSeq_id_l; reflexivity | reflexivity | ].
    apply IHpf_sym.

  - (* source *)
    transitivity (g · (symmetric_reverse n t c pf_sym · (g · g) · c) · g).
    { repeat rewrite inSeq_assoc; reflexivity. }
    transitivity (g · (symmetric_reverse n t c pf_sym · c) · g).
    { apply HOAS_Equiv_inSeq; [ | reflexivity].
      apply HOAS_Equiv_inSeq; [ reflexivity | ].
      apply HOAS_Equiv_inSeq; [ | reflexivity ].      
      rewrite HOAS_Equiv_inSeq; [ | reflexivity | apply symmetric_gate_source_reversible; auto].
      rewrite inSeq_id_l; reflexivity.
    }
    transitivity (g · g); [ | apply symmetric_gate_source_reversible; auto].
    apply HOAS_Equiv_inSeq; [ | reflexivity].
    rewrite HOAS_Equiv_inSeq; [ | reflexivity | apply IHpf_sym].
    rewrite inSeq_id_l; reflexivity.
  - (* ancilla *)
    set (close := assert_at b (n + t) i).
    set (open := init_at b (n + t) i).
    set (c' := symmetric_reverse (S n) t c pf_sym).
    transitivity (close · (c' · (open · close · c · open))).
    { repeat (rewrite inSeq_assoc); reflexivity. }
    transitivity (close · (c' · c) · open).
    { repeat rewrite <- inSeq_assoc. 
      apply HOAS_Equiv_inSeq; [ | reflexivity].
      apply HOAS_Equiv_inSeq; [ | reflexivity ].
      apply init_assert_at_valid.
      { unfold in_source in pf. omega. }
      set (H := Symmetric_Box_noop_at (S n) t c pf_sym).
      simpl in H.
      apply H; auto.
   }
   transitivity (close · id_circ · open).
   { apply HOAS_Equiv_inSeq; [ | reflexivity].
     apply HOAS_Equiv_inSeq; [ reflexivity | ].
     apply IHpf_sym.
   }
   rewrite inSeq_id_l.
   apply assert_init_at_id.
   unfold in_source in pf. omega.
Qed.
