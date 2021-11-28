Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASLib.
Require Import Denotation.
Require Import Composition.
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
  * destruct n as [ | n]; [exfalso;lia | ]. simpl.
    refine (box_ q ⇒ let_ (q,qs) ← q; 
                     let_ q ← _X $q; 
                     (q,qs)).
  * destruct n as [ | n]; [exfalso;lia | ]. simpl.
    refine (box_ q ⇒ let_ (q,qs) ← q; 
                     let_ qs ← IHi n _ U $ qs;
                     (q,qs)). 
    lia.
Defined.

Lemma unitary_at1_WT : forall n (U : Unitary Qubit) i (pf : i < n),
    Typed_Box (unitary_at1 n U i pf).
Proof.
  intros n U i pf. gen n U. 
  induction i; intros n pf U.
  * simpl. destruct n as [ | n]; [exfalso;lia | ].
    type_check.
  * simpl. destruct n as [ | n]; [exfalso;lia | ]. simpl.
    type_check.
    apply IHi.
    type_check.
Qed.
Definition X_at n i (pf : i < n) := unitary_at1 n _X i pf.
Lemma X_at_WT : forall n i pf, Typed_Box (X_at n i pf). 
Proof. intros; apply unitary_at1_WT. Qed.

Lemma lt_leS_le : forall i j k,
    i < j -> j <= S k -> i <= k.
Proof. intros. lia. Qed.

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
      ++ exfalso;lia.
    + dependent destruction pf2.
      ++ exfalso;lia.
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

    
(* Precondition:  0 < j < n *)
Definition CNOT_at_i0 (n j : nat) (pf_j : 0 < j) (pf_n : j < n) 
                     : Box (n ⨂ Qubit) (n ⨂ Qubit).
Proof.
  gen n.
  induction j as [ | [ | j']]; intros n pf_n.
  * (* i = 0, j = 0 *) exfalso;lia. 
  * (* i = 0, j = 1 *)
    destruct n as [ | [ | n']]; try (exfalso;lia).
    exact (box_ q ⇒ let_ (q0,(q1,qs)) ← q; 
                     let_ (q0,q1) ← CNOT $(q0,q1);
                     (q0,(q1,qs))).
  * (* i = 0, j = S (S j') *)
    destruct n as [ | [ | n']]; try (exfalso;lia).
    refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q;
                     let_ (q0,qs) ← IHj _ (S n') _ $ (q0,qs);
                     (q0,(q1,qs))).
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
               (q0,(q1,qs)).
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
  * (* i = 0, j = 0 *) exfalso;lia.
  * (* i = 1, j = 0 *)
    destruct n as [ | [ | n']]; try (exfalso;lia).
    exact (box_ q ⇒ let_ (q0,(q1,qs)) ← q; 
                     let_ (q1,q0) ← CNOT $(q1,q0);
                     (q0,(q1,qs))).
  * (* i = S (S i'), j = 0 *)
    destruct n as [ | [ | n']]; try (exfalso;lia).
    refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q;
                     let_ (q0,qs) ← IHi _ (S n') _ $(q0,qs);
                     (q0,(q1,qs))).
       + apply Nat.lt_0_succ.
       + apply lt_S_n. auto.
Defined.


Lemma CNOT_at_j0_WT : forall (n i : nat) (pf_i : 0 < i) (pf_n : i < n),
      Typed_Box (CNOT_at_j0 n i pf_i pf_n).
Proof.
  intros n i pf_i.
  gen n.
  induction i as [ | [ | i']]; intros n pf_n.
  * (* i = 0, j = 0 *) exfalso;lia.
  * (* i = 1, j = 0 *)
    destruct n as [ | [ | n']]; try (exfalso;lia).
    simpl. type_check.
  * (* i = S (S i'), j = 0 *)
    destruct n as [ | [ | n']]; try (exfalso;lia). 
    set (pf_i' := (Nat.lt_0_succ _ : 0 < S i')).
    set (pf_n' := (lt_S_n _ _ pf_n : S i' < S n')).
    specialize (IHi pf_i' _ pf_n').
    type_check.
Qed. 

Lemma CNOT_at_j0_SS : forall n i
                             (pfi : 0 < S (S i)) (pfi' : 0 < S i)
                             (pfn : S (S i) < S (S n)) (pfn' : S i < S n),
      CNOT_at_j0 (S (S n)) (S (S i)) pfi pfn
    = box_ q ⇒ let_ (q0,(q1,qs)) ← q;
               let_ (q0,qs) ← CNOT_at_j0 (S n) (S i) pfi' pfn' $(q0,qs);
               (q0,(q1,qs)).
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
  - (* n = 0 *) exfalso;lia.
  - destruct i as [ | i'], j as [ | j'].
    * (* i = 0, j = 0 *) contradiction.
    * (* i = 0, j = S j' *) refine (CNOT_at_i0 (S n) (S j') _ pf_j).
      + apply Nat.lt_0_succ.
    * (* i = S i', j = 0 *) refine (CNOT_at_j0 (S n) (S i') _ pf_i).
      + apply Nat.lt_0_succ.
    * (* i = S i', j = S j' *)
      refine (box_ q ⇒ let_ (q0,qs) ← q;
                       let_ qs ←  IHn i' j' _ _ _ $qs;
                       (q0,qs)).  
      + apply (lt_S_n _ _ pf_i).
      + apply (lt_S_n _ _ pf_j).
      + apply Nat.succ_inj_wd_neg. apply pf_i_j.
Defined.

(* Alternative, direct definition of CNOT_at' *)
(*
Definition CNOT_at'' (n i j : nat) 
                     (pf_i : i < n) (pf_j : j < n) (pf_i_j : i <> j) 
                     : Box (n ⨂ Qubit) (n ⨂ Qubit).
induction i as [|[|i]]; induction j as [|[|j]]; destruct n as [|[|n]]; try lia.
- (* i = 0, j = 1 *)
  exact (box_ q ⇒ let_ (q0,(q1,qs)) ← q; 
                   let_ (q0,q1) ← CNOT $(q0,q1);
                   (q0,(q1,qs))).
- (* i = 0, j > 1 *)
  refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q;
                   let_ (q1,(q0,qs)) ← IHj _ _ $ (q1,(q0,qs));
                   (q0,(q1,qs))); lia.
- (* i = 1, j = 0 *)
  exact (box_ q ⇒ let_ (q0,(q1,qs)) ← q; 
                  let_ (q1,q0) ← CNOT $(q1,q0);
                  (q0,(q1,qs))).
- (* i = 1, j > 1 *)
    refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q;
                   let_ (q1,(q0,qs)) ← IHi _ _ $ (q1,(q0,qs));
                   (q0,(q1,qs))); lia.
*)

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
               (q0,(q1,qs)).
Proof.
  intros. 
  unfold CNOT_at.
  simpl. 
  destruct (lt_dec (S (S j')) (S (S n'))); [ | lia].
  destruct (lt_dec (S j') (S n')); [ | lia].
  erewrite CNOT_at_i0_SS. reflexivity.
Qed.
  
Lemma CNOT_at_n_SS_0 : forall n' i', i' < n' ->
      CNOT_at (S (S n')) (S (S i')) 0 
    = box_ q ⇒ let_ (q0,(q1,qs)) ← q;
               let_ (q0,qs) ← CNOT_at (S n') (S i') 0 $(q0,qs);
               (q0,(q1,qs)).
Proof.
  intros.
  unfold CNOT_at.
  simpl. 
  destruct (lt_dec (S (S i')) (S (S n'))); [ | lia].
  destruct (lt_dec (S i') (S n')); [ | lia].
  erewrite CNOT_at_j0_SS. reflexivity.
Qed.

Lemma CNOT_at_at' : forall n i j (pfi : i < n) (pfj : j < n) (pf_i_j : i <> j),
      CNOT_at n i j = CNOT_at' n i j pfi pfj pf_i_j.
Proof.
  intros. unfold CNOT_at.
  destruct (lt_dec i n); [ | exfalso;lia].
  destruct (lt_dec j n); [ | exfalso;lia].
  destruct (Nat.eq_dec i j); [exfalso;lia | ].
  replace l with pfi by apply lt_hprop.
  replace l0 with pfj by apply lt_hprop.
  replace n0 with pf_i_j by apply nat_neq_hprop.
  reflexivity.
Qed.
  
Lemma CNOT_at_n_S_S : forall n' i' j',
                      i' < n' -> j' < n' -> i' <> j' ->
      CNOT_at (S n') (S i') (S j')
    = box_ q ⇒ let_ (q0,qs) ← q;
               let_ qs ← CNOT_at n' i' j' $ qs;
               (q0,qs).
Proof.
  intros n' i' j' pf_i pf_j pf_i_j.
  erewrite CNOT_at_at'. 
  simpl.
  erewrite CNOT_at_at'.
  reflexivity.
  Unshelve. all: lia.
Qed.

(* i and j are the controls, k is the target *)
(* i is always assumed to be smaller than j *)
(* i = 0, j = 1 *)
Definition TOF_at_ij01 (n k : nat) (pf_j : 1 < k) (pf_n : k < n) 
  : Box (n ⨂ Qubit) (n ⨂ Qubit).
  gen n.
  induction k as [| [| [|k]]]; intros; try (exfalso;lia).
  - destruct n as [| [| [|n]]]; try (exfalso;lia).
    exact (box_ q ⇒ let_ (q0,(q1,(q2,qs))) ← q; 
                    let_ (q0,(q1,q2)) ← CCNOT $(q0,(q1,q2));
                    (q0,(q1,(q2,qs)))).
  - destruct n as [| [| [|n]]]; try (exfalso;lia).
    refine (box_ q ⇒ let_ (q0,(q1,(q2,qs))) ← q;
                     let_ (q0,(q1,qs)) ← IHk _ (S (S n)) _ $ (q0,(q1,qs));
                     (q0,(q1,(q2,qs)))); auto with arith.
Defined.
Lemma TOF_at_ij01_WT : forall n k pf_j pf_n, Typed_Box (TOF_at_ij01 n k pf_j pf_n).
Proof.
  intros n k. gen n.
  induction k as [| [| [|k]]]; intros; destruct n as [| [| [|n]]]; try (exfalso;lia).
  type_check.
  set( pf_j' := gt_le_S 1 (S (S k)) (lt_n_S 0 (S k) (Nat.lt_0_succ k))).
  set (pf_n' := gt_le_S (S (S k)) (S (S n)) (gt_S_le (S (S (S k))) (S (S n)) pf_n)).
  specialize (IHk _ pf_j' pf_n').
  type_check.
Qed.  
  
(* i = 0, k = 1 *)
Definition TOF_at_ik01 (n j : nat) (pf_j : 1 < j) (pf_n : j < n) 
  : Box (n ⨂ Qubit) (n ⨂ Qubit).
  gen n.
  induction j as [| [| [|j]]]; intros; try (exfalso;lia).
  - destruct n as [| [| [|n]]]; try (exfalso;lia).
    exact (box_ q ⇒ let_ (q0,(q1,(q2,qs))) ← q; 
                    let_ (q0,(q2,q1)) ← CCNOT $(q0,(q2,q1));
                    (q0,(q1,(q2,qs)))).
  - destruct n as [| [| [|n]]]; try (exfalso;lia).
    refine (box_ q ⇒ let_ (q0,(q1,(q2,qs))) ← q;
                     let_ (q0,(q1,qs)) ← IHj _ (S (S n)) _ $ (q0,(q1,qs));
                     (q0,(q1,(q2,qs)))); auto with arith.
Defined.
Lemma TOF_at_ik01_WT : forall n j pf_j pf_n, Typed_Box (TOF_at_ik01 n j pf_j pf_n).
Proof.
  intros n j. gen n.
  induction j as [| [| [|j]]]; intros; destruct n as [| [| [|n]]]; try (exfalso;lia).
  type_check.
  set( pf_j' := gt_le_S 1 (S (S j)) (lt_n_S 0 (S j) (Nat.lt_0_succ j))).
  set (pf_n' := gt_le_S (S (S j)) (S (S n)) (gt_S_le (S (S (S j))) (S (S n)) pf_n)).
  specialize (IHj _ pf_j' pf_n').
  type_check.
Qed.  


(* k = 0, i = 1 *)
Definition TOF_at_ki01 (n j : nat) (pf_j : 1 < j) (pf_n : j < n) 
  : Box (n ⨂ Qubit) (n ⨂ Qubit).
  gen n.
  induction j as [| [| [|j]]]; intros; try (exfalso;lia).
  - destruct n as [| [| [|n]]]; try (exfalso;lia).
    exact (box_ q ⇒ let_ (q0,(q1,(q2,qs))) ← q; 
                    let_ (q1,(q2,q0)) ← CCNOT $(q1,(q2,q0));
                    (q0,(q1,(q2,qs)))).
  - destruct n as [| [| [|n]]]; try (exfalso;lia).
    refine (box_ q ⇒ let_ (q0,(q1,(q2,qs))) ← q;
                     let_ (q0,(q1,qs)) ← IHj _ (S (S n)) _ $ (q0,(q1,qs));
                     (q0,(q1,(q2,qs)))); auto with arith.
Defined.    
Lemma TOF_at_ki01_WT : forall n j pf_j pf_n, Typed_Box (TOF_at_ki01 n j pf_j pf_n).
Proof.
  intros n j. gen n.
  induction j as [| [| [|j]]]; intros; destruct n as [| [| [|n]]]; try (exfalso;lia).
  type_check.
  set( pf_j' := gt_le_S 1 (S (S j)) (lt_n_S 0 (S j) (Nat.lt_0_succ j))).
  set (pf_n' := gt_le_S (S (S j)) (S (S n)) (gt_S_le (S (S (S j))) (S (S n)) pf_n)).
  specialize (IHj _ pf_j' pf_n').
  type_check.
Qed.  

(* i = 0 *)
Definition TOF_at_i0 (n j k : nat) (pf_ij : 0 < j) (pf_ik : 0 < k) (pf_jk : j <> k) (pf_jn : j < n) (pf_kn : k < n)
  : Box (n ⨂ Qubit) (n ⨂ Qubit).
  gen n k. induction j as [| [|j]]; intros; try (exfalso;lia).
  - apply (TOF_at_ij01 n k); lia.
  - gen n. destruct k as [| [|k]]; intros; try (exfalso;lia).
    + apply (TOF_at_ik01 n (S (S j))); try lia.
    + destruct n as [| [| [|n]]]; try (exfalso;lia).
      refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q;
                       let_ (q0,qs) ← IHj _ (S (S n)) _ (S k) _ _ _ $ (q0,qs);
                       (q0,(q1,qs))); auto with arith.
Defined.
Lemma TOF_at_i0_WT : forall n j k pf_ij pf_ik pf_jk pf_jn pf_kn,
    Typed_Box (TOF_at_i0 n j k pf_ij pf_ik pf_jk pf_jn pf_kn).
Proof.
  intros n j. gen n. induction j as [| [|j]]; intros; try (exfalso;lia).
  apply TOF_at_ij01_WT.
  destruct k as [| [|k]]; intros; try (exfalso;lia).
  apply TOF_at_ik01_WT.
  destruct n as [| [| [|n]]]; try (exfalso;lia).
  specialize (IHj (S (S n)) (S k)).
  (* (Nat.lt_0_succ _) (Nat.lt_0_succ _)). *)
  epose (pf_ij' := _ : 0 < S j).
  epose (pf_ik' := _ : 0 < S k).
  epose (pf_jk' := _ : S j <> S k).
  epose (pf_jn' := _ : S j < S (S n)). 
  epose (pf_kn' := _ : S k < S (S n)).   
  Unshelve. all: auto with arith.
  specialize (IHj pf_ij' pf_ik' pf_jk' pf_jn' pf_kn').
  type_check.
Qed.

(* k = 0 *)
Definition TOF_at_k0 (n i j : nat) (pf_ij : i < j) (pf_ik : 0 < i) (pf_jk : 0 < j) (pf_in : i < n) (pf_jn : j < n)
  : Box (n ⨂ Qubit) (n ⨂ Qubit).
  gen n j. induction i as [| [|i]]; intros; try (exfalso;lia).
  - apply (TOF_at_ki01 n j); try lia.
  - destruct j as [|[|j]]; try (exfalso;lia).
    destruct n as [| [| [|n]]]; try (exfalso;lia).
    refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q;
                     let_ (q0,qs) ← IHi _ (S (S n)) _ (S j) _ _ _ $ (q0,qs);
                     (q0,(q1,qs))); auto with arith.
Defined.
Lemma TOF_at_k0_WT  : forall n i j pf_ij pf_ik pf_jk pf_in pf_jn,
  Typed_Box (TOF_at_k0 n i j pf_ij pf_ik pf_jk pf_in pf_jn).
Proof.
  intros n i. gen n. induction i as [| [|i]]; intros; try (exfalso;lia).
  apply TOF_at_ki01_WT.
  destruct j as [| [|j]]; intros; try (exfalso;lia).
  destruct n as [| [| [|n]]]; try (exfalso;lia).
  specialize (IHi (S (S n)) (S j)).
  epose (pf_ij' := _ : S i < S j).
  epose (pf_ik' := _ : 0 < S i).
  epose (pf_jk' := _ : 0 < S j).
  epose (pf_in' := _ : S i < S (S n)).
  epose (pf_jn' := _ : S j < S (S n)).
  Unshelve. all: auto with arith.
  specialize (IHi pf_ij' pf_ik' pf_jk' pf_in' pf_jn').
  type_check.
Qed.

(* lia fails if we call i j and k `Var`s? *)
Definition Toffoli_at' (n : nat) (i j k : nat) (pf_i : i < n) (pf_j : j < n) (pf_k : k < n)
                                      (pf_i_j : i <> j) (pf_i_k : i <> k) (pf_j_k : j <> k) :
    Box (n ⨂ Qubit) (n ⨂ Qubit).
gen i j k.
induction n; intros; try (exfalso;lia).
destruct i; [|destruct j; [|destruct k]]; try (exfalso;lia).
- apply (TOF_at_i0 (S n) j k); lia. 
- apply (TOF_at_i0 (S n) (S i) k); unfold Var in *; lia. 
- destruct (lt_dec i j).
  + apply (TOF_at_k0 (S n) (S i) (S j)); lia.
  + apply (TOF_at_k0 (S n) (S j) (S i)); unfold Var in *; lia.
- refine (box_ q ⇒ let_ (q0,qs) ← q;
                   let_ qs ← IHn i _ j _ _ k _ _ _ $ qs;
                   (q0,qs)); auto with arith.
Defined.
Lemma Toffoli_at'_WT : forall n (i j k : nat) (pf_i : i < n) (pf_j : j < n) (pf_k : k < n)
                             (pf_i_j : i <> j) (pf_i_k : i <> k) (pf_j_k : j <> k),
      Typed_Box (Toffoli_at' n i j k pf_i pf_j pf_k pf_i_j pf_i_k pf_j_k).
Proof.
  induction n; intros; try (exfalso;lia).
  destruct i; [|destruct j; [|destruct k]]; try (exfalso;lia).
  - apply TOF_at_i0_WT.
  - apply TOF_at_i0_WT.
- Opaque TOF_at_k0. simpl. destruct (lt_dec i j).
  + apply (TOF_at_k0_WT (S n) (S i) (S j)).
  + apply (TOF_at_k0_WT (S n) (S j) (S i)).
- epose (pf_i' := _ : i < n).
  epose (pf_j' := _ : j < n).
  epose (pf_k' := _ : k < n).
  epose (pf_i_j' := _ : i <> j).
  epose (pf_i_k' := _ : i <> k).
  epose (pf_j_k' := _ : j <> k).
  Unshelve. all: auto with arith.
  specialize (IHn i j k pf_i' pf_j' pf_k' pf_i_j' pf_i_k' pf_j_k').
  type_check.
Qed.

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
  box (fun p => c $ ((),p)).
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
  rewrite add_fresh_split.
  reflexivity.
Qed.

Definition strip_one_l_out {W W' : WType} (c : Box W (One ⊗ W')) : Box W W' :=
  box_ p ⇒ let_ (_,p') ← unbox c p;  p'.
Lemma strip_one_l_out_WT : forall W W' (c : Box W (One ⊗ W')), 
    Typed_Box c -> Typed_Box (strip_one_l_out c).
Proof. type_check. Qed.
Fact strip_one_l_out_eq : forall W W' (c : Box W (One ⊗ W')) (ρ : Matrix (2^⟦W⟧)%nat (2^⟦W'⟧)%nat),
  denote_box true (strip_one_l_out c) ρ = denote_box true c ρ.
Proof.
  intros.
  unfold strip_one_l_out.
  matrix_denote. 
  unfold unbox. unfold denote_db_box.
  destruct c.
  simpl.
  rewrite add_fresh_split.
  simpl.
Admitted.

Definition strip_one_r_in {W W' : WType} (c : Box (W ⊗ One) W') : Box W W' :=
  box (fun p => c $ (p,())).
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
  rewrite add_fresh_split.
  reflexivity.
Qed.

Definition strip_one_r_out {W W' : WType} (c : Box W (W' ⊗ One)) : Box W W' :=
  box_ p ⇒ let_ (p',_) ← c $ p; p'.
Lemma strip_one_r_out_WT : forall W W' (c : Box W (W' ⊗ One)), 
    Typed_Box c -> Typed_Box (strip_one_r_out c).
Proof. type_check. Qed.
Fact strip_one_r_out_eq : forall W W' (c : Box W (W' ⊗ One)) (ρ : Matrix (2^⟦W⟧)%nat (2^⟦W'⟧)%nat),
  denote_box true (strip_one_r_out c) ρ = denote_box true c ρ.
Proof.
  intros.
  unfold strip_one_r_out.
  matrix_denote. 
  unfold unbox. unfold denote_db_box.
  destruct c.
  simpl.
  rewrite add_fresh_split.
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
  intros. apply lt_le_trans with (m := n); auto. lia. 
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

#[export] Hint Resolve unitary_at1_WT X_at_WT CNOT_at_WT Toffoli_at_WT init_at_WT assert_at_WT : typed_db.

Lemma gate_acts_on_WT : forall m (g : Box (m ⨂ Qubit) (m ⨂ Qubit)) k, 
                        gate_acts_on k g -> Typed_Box g.
Proof.
  intros m g k pf_g.
  destruct pf_g; type_check.
Qed.

Lemma source_symmetric_WT : forall n t c, source_symmetric n t c -> Typed_Box c.
Proof.
  intros n t c H.
  induction H; try solve [type_check].
  - inversion g0; type_check.
  - inversion g0; type_check.
  - inversion g0; type_check.
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

Fact gate_acts_on_noop_at : forall m g k i,
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
Lemma fresh_state_ntensor : forall n (Γ : Ctx), add_fresh_state (n ⨂ Qubit) Γ = 
                                           Γ ++ List.repeat (Some Qubit) n.
Proof.                            
  induction n. 
  - intros. simpl. rewrite app_nil_r; reflexivity.
  - intros. simpl. unfold add_fresh_state in *. simpl. 
    specialize (IHn (Γ ++ [Some Qubit])).
    rewrite add_fresh_split in *. simpl in *.
    rewrite IHn. rewrite <- app_assoc. reflexivity.
Qed.

(* Currently working on these in Oracles.v *)
(* Strong sematics for init and assert *)
Open Scope matrix_scope.

Fact init_at_spec_strong : forall b n i (ρ : Square (2^n)) (safe : bool), 
  i <= n ->
  denote_box safe (init_at b n i) ρ = 
  (I  (2^i) ⊗ bool_to_ket b ⊗ I  (2^ (n-i))) × ρ × 
  (I  (2^i) ⊗ (bool_to_ket b)† ⊗ I  (2^ (n-i))).
Proof.
(*
    rewrite Nat.add_1_r, Nat.mul_1_r.
    rewrite swap_list_n_id.
    rewrite pad_nothing.
    subst.
    rewrite ctx_dom_repeat.
    repeat rewrite subst_var_σ_n by lia.

(* Show that apply_U CNOT [0; n] has desired behavior *)
    remember (S (length l2)) as n.
    remember (I  (2 ^ S n)) as I_m.
    replace (@Datatypes.cons Var O (@Datatypes.cons Var n (@Datatypes.nil Var)))
          with ([0; 0 + length l2 + 1])%nat.
    2: subst; rewrite Nat.add_1_r; reflexivity. 
    assert (CS:
    super (control σx) (bool_to_matrix b ⊗ bool_to_matrix t)
                           = (bool_to_matrix b ⊗ bool_to_matrix (xorb b t)))
    by (vector_denote; destruct b, t; unfold bool_to_ket; simpl; Msimpl; solve_matrix).  
    assert ((0 + length l2 + 0 + 2)%nat = S n)%nat as E. lia.
    
    (* breaks here *)


    specialize (apply_U_spec_2 (S n) O (length l2) O (I 1) (⨂ l2) (I 1) 
                             _ _ _ _ _ E CS). simpl; Msimpl.
    intros H. 
    rewrite H.
    subst.
    unfold super.
    apply WF_big_kron in WF2.
    Msimpl.
    rewrite xorb_comm.
    reflexivity.
  - simpl in *.
    destruct l1. inversion L1.
    simpl.

    repeat (autounfold with den_db; simpl).
    unfold add_fresh_state; simpl.
    unfold get_fresh_var; simpl.
    rewrite fresh_state_ntensor. simpl.
    rewrite size_ntensor. simpl. rewrite Nat.add_1_r, Nat.mul_1_r.
    replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
    rewrite repeat_combine.
    replace (Some Qubit :: repeat (Some Qubit) (n'+1)) with 
        (repeat (Some Qubit) (S (n' + 1))) by reflexivity.
    rewrite Nat.add_1_r.

    
    specialize denote_compose as DC. simpl in DC.
    unfold denote_circuit in DC.
    
    replace (S (S n')) with (⟦(Valid (repeat (Some Qubit) (S (S n'))))⟧).
    2: simpl; rewrite size_repeat_ctx; reflexivity.
    replace (⟦(Valid (repeat (Some Qubit) (S (S n'))))⟧) with (S (S n')) at 2.
    2: simpl; rewrite size_repeat_ctx; reflexivity.
    replace (O) with (⟦∅⟧) by reflexivity.

    specialize (share_to_WT n' k) as WT.
    erewrite DC with (Γ0 := ∅) (Γ1 := Valid [Some Qubit]) (Γ1':= (Valid (repeat (Some Qubit) (S (S n'))))).
    Focus 2. apply WT. simpl. rewrite repeat_length. econstructor.
    Focus 3.
      replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
      apply types_pat_fresh_ntensor. lia.      
    3: constructor; apply singleton_singleton.
    2: reflexivity.
    replace (S n') with (length ((repeat None 1) ++ repeat (Some Qubit) n')).
    rewrite merge_singleton_append. apply valid_valid.    
    rewrite app_length. repeat rewrite repeat_length. lia.
    
    Focus 3.
      constructor. apply valid_valid.
      replace (S n') with (length ((repeat None 1) ++ repeat (Some Qubit) n')).
      rewrite merge_singleton_append.
      unlock_merge. simpl. rewrite repeat_length.   
      replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
      rewrite repeat_combine. rewrite Nat.add_1_r. reflexivity.
      rewrite app_length. repeat rewrite repeat_length. lia.    
    Focus 2.
      intros.
      simpl.
      dependent destruction p0.
      dependent destruction H0.
      unfold wproj.
      econstructor. 
      reflexivity.
      econstructor.
      destruct H; assumption.
      3: apply H0_0.
      Focus 2. econstructor. 
        4: apply H0_.
        3: constructor; apply singleton_singleton; reflexivity.
        2: reflexivity.
        destruct H. type_check.
      destruct H. simpl. rewrite <- merge_assoc. rewrite merge_comm. assumption.

      unfold compose_super. simpl.
      unfold add_fresh_state; simpl.
      unfold get_fresh_var; simpl.
      rewrite fresh_state_ntensor. simpl.
      replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
      rewrite repeat_combine.
      rewrite size_repeat_ctx.      
      unfold denote_pat. simpl.
      rewrite size_ntensor. simpl. rewrite Nat.mul_1_r, Nat.add_1_r.
      rewrite ctx_dom_repeat.      
      repeat rewrite seq_shift.      
      replace (0%nat :: seq 1 (S n')) with (σ_{2+n'}) by reflexivity.
      rewrite repeat_length.
      rewrite subst_var_σ_n by lia.
      rewrite subst_var_σ_n by lia.
      rewrite merge_nil_l.
      replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
      rewrite ntensor_pat_to_list_shifted by lia.
      unfold size_octx. simpl.
      specialize (merge_singleton_append Qubit (repeat (Some Qubit) n')) as MSA.
      simpl in MSA. rewrite repeat_length in MSA. 
      unlock_merge. simpl. rewrite MSA. clear MSA.
      rewrite <- seq_S.
      replace (@Datatypes.cons Var O (seq (S O) (S n'))) with (σ_{2+n'}) by
          reflexivity.
      rewrite swap_list_n_id.
      rewrite pad_nothing.
      remember (I  (2 ^ (2 + n'))) as Im. 
      simpl. 
      replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
      rewrite repeat_combine.
      rewrite size_repeat_ctx.

      specialize (IH k l1 l2).
      specialize (denote_db_unbox (share_to n' k)) as DDU.
      simpl in DDU. rewrite DDU in IH. clear DDU.
      rewrite fresh_state_ntensor in IH. simpl in IH.

      repeat rewrite kron_assoc.
      setoid_rewrite kron_assoc.
      specialize denote_db_pad_left as DDP. unfold denote_circuit in *.
      specialize (DDP [Some Qubit] (repeat (Some Qubit) (n'+1)%nat) 1%nat (n'+1)%nat 
                      (Tensor (NTensor n' Qubit) Qubit)). 
      specialize (DDP (unbox (share_to n' k) (pair (@fresh_pat OCtx OCtx_State 
        (NTensor n' Qubit) (Valid (repeat (Some Qubit) 1))) (qubit (S n'))))).
      match goal with
      | [|- context[?a ⊗ ?b] ] => remember b as ρ2
      end.
      specialize (DDP m ρ2).
      simpl in DDP. rewrite size_repeat_ctx in DDP.
      simpl.
      show_dimensions.
      rewrite Nat.add_1_r in *. simpl in *.
      replace (2 ^ length l1 * (2 ^ length l2 * 2 + (2 ^ length l2 * 2 + 0)))%nat
              with (2 ^ n' + (2 ^ n' + 0))%nat.
      2: clear -L1 L2 Lt; inversion L1; subst; unify_pows_two. 
      unfold apply_box. simpl.
      rewrite DDP by reflexivity.
      hide_dimensions.
      rewrite decr_circuit_pat. simpl.
      rewrite (decr_pat_once_qubit n' []).
      rewrite Nat.sub_0_r.
      rewrite (repeat_combine (option WType) n' 1) in IH.
      rewrite size_repeat_ctx in IH.
      subst.
      rewrite Nat.add_1_r in IH. simpl in IH.
      repeat rewrite kron_assoc in IH.
      assert (k < n')%nat as Lt' by (clear -Lt; lia).
      assert (length l1 = k)%nat as L1' by (clear -L1; lia). clear Lt L1.
      specialize (IH Lt' L1' L2).
      replace (2 ^ length l2 * 2 + (2 ^ length l2 * 2 + 0))%nat with 
          (2 * (2 ^ length l2 * 2))%nat by unify_pows_two.
      unfold add_fresh_state in IH. simpl in IH.
      unfold get_fresh_var in IH. simpl in IH.
      rewrite repeat_length in IH.
      rewrite (repeat_combine (option WType) n' 1) in IH.
      rewrite Nat.add_1_r in IH.
      simpl in IH.
      setoid_rewrite IH; trivial.      
      2: intros i; apply (WF1 (S i)).
      unfold super.
      rewrite size_ntensor. simpl. rewrite Nat.mul_1_r, Nat.add_1_r. simpl.
      apply WF_big_kron in WF2; trivial.
      assert (WF1': WF_Matrix (2 ^ length l1) (2 ^ length l1) (⨂ l1)).
      eapply WF_big_kron. intros j. apply (WF1 (S j)).
      specialize (WF1 O). rename WF1 into WFm. rename WF1' into WF1.
      Msimpl.
      reflexivity.
*)
Admitted.

(* Safe semantics *)
Fact assert_at_spec_safe : forall b n i (ρ : Square (2^n)), 
  i <= n ->
  denote_box true (assert_at b n i) ρ = 
  (I  (2^i) ⊗ ⟨0∣ ⊗ I  (2^ (n-i))) × ρ × (I  (2^i) ⊗ ∣0⟩ ⊗ I  (2^ (n-i))) .+ 
  (I  (2^i) ⊗ ⟨1∣ ⊗ I  (2^ (n-i))) × ρ × (I  (2^i) ⊗ ∣1⟩ ⊗ I  (2^ (n-i))).
Admitted.

(* unsafe semantics *)
Fact assert_at_spec_unsafe : forall b n i (ρ : Square (2^n)), 
  i <= n ->
  denote_box false (assert_at b n i) ρ = 
  (I  (2^i) ⊗ (bool_to_ket b)† ⊗ I  (2^ (n-i))) × ρ × (I  (2^i) ⊗ bool_to_ket b ⊗ I  (2^ (n-i))).
Admitted.


(* Jumping the gun:
   A ∥ B ;; C ∥ D = (A ;; C) ∥ (B ;; D) would make this trivial *)
(*
Proposition valid_init_assert : forall b n i, 
    valid_ancillae_box (assert_at b n i · init_at b n i).
Proof.
  intros b. 
  induction n.
  - intros.
    unfold valid_ancillae_box.
    matrix_denote.
    unfold unbox, init_at, assert_at.
    simpl.
Abort.
*)    


Lemma assert_init_at_id : forall b m i, i < S m ->
    (assert_at b m i · init_at b m i  ≡ id_circ)%qc.
Proof. 
  intros b m i Lt ρ safe M. simpl.
  simpl_rewrite id_circ_spec; auto with wf_db.
  simpl_rewrite inSeq_correct; [ | apply assert_at_WT | apply init_at_WT].
  unfold compose_super.
  rewrite size_ntensor, Nat.mul_1_r in M.
  simpl_rewrite (init_at_spec_strong b m i); [|lia]. 
  destruct safe.
  - (* safe case *)
    simpl_rewrite (assert_at_spec_safe b m i); [|lia].
    gen ρ. rewrite size_ntensor. simpl. rewrite Nat.mul_1_r.
    intros ρ M.
    repeat rewrite Mmult_assoc.
    Msimpl.  
    match goal with
    | [|- @Mmult ?a ?b ?c ?A (@Mmult ?d ?e ?f ?B ?C) .+ _ = _] => 
      setoid_rewrite <- (Mmult_assoc A B C)                                    
    end.
    Msimpl.
    destruct b; simpl.
    + replace (⟨0∣ × ∣1⟩) with (@Zero 1 1) by crunch_matrix.
      rewrite kron_0_r, kron_0_l. 
      rewrite Mmult_0_l, Mplus_0_l. (* add to dbs *)
      replace (⟨1∣ × ∣1⟩) with (I 1).
      2: crunch_matrix; bdestruct (S x <? 1); [lia|rewrite andb_false_r; easy].
      Msimpl.
      rewrite Nat.mul_1_r.
      replace (2^i * 2^(m-i)) with (2^m) by unify_pows_two. 
      Msimpl.
      rewrite <- Mmult_assoc.
      setoid_rewrite kron_mixed_product.
      Msimpl.
      replace (⟨1∣ × ∣1⟩) with (I 1) by solve_matrix.
      rewrite id_kron.
      rewrite Nat.mul_1_r.
      rewrite id_kron.
      unify_pows_two.
      Msimpl.
      reflexivity.
    + replace (⟨0∣ × ∣1⟩) with (@Zero 1 1) by crunch_matrix.
      rewrite kron_0_r, kron_0_l.
      repeat Msimpl. 
      replace (⟨0∣ × ∣0⟩) with (I 1) by solve_matrix.
      repeat rewrite id_kron.
      Msimpl.
      reflexivity.
  - (* unsafe (easy) case *)
    simpl_rewrite (assert_at_spec_unsafe b m i); [|lia].
    gen ρ. rewrite size_ntensor. simpl. rewrite Nat.mul_1_r.
    intros ρ M.
    repeat rewrite Mmult_assoc.
    Msimpl.
    match goal with
    | [|- @Mmult ?a ?b ?c ?A (@Mmult ?d ?e ?f ?B ?C) = _] => 
      setoid_rewrite <- (Mmult_assoc A B C)                                    
    end.
    Msimpl.
    destruct b; simpl.
    + replace (⟨1∣ × ∣1⟩) with (I 1) by solve_matrix.
      repeat rewrite id_kron.
      Msimpl.
      reflexivity.
    + replace (⟨0∣ × ∣0⟩) with (I 1) by solve_matrix.
      repeat rewrite id_kron.
      Msimpl.
      reflexivity.
Qed.

Close Scope matrix_scope.
Open Scope circ_scope.

Fact init_assert_at_valid : forall b m i W1 (c : Box W1 (S m ⨂ Qubit)), 
    i < S m ->
    valid_ancillae_box' (assert_at b m i · c) ->
    init_at b m i · assert_at b m i · c ≡ c.
Admitted.

Fact valid_ancillae_box'_equiv : forall W1 W2 (b1 b2 : Box W1 W2), b1 ≡ b2 ->
      valid_ancillae_box' b1 <-> valid_ancillae_box' b2.
Admitted.

(* Follows from uniformly decreasing trace *)
Fact valid_inSeq : forall w1 w2 w3 (c1 : Box w1 w2) (c2 : Box w2 w3),
      Typed_Box c1 -> Typed_Box c2 ->
      valid_ancillae_box' c1 -> valid_ancillae_box' c2 ->
      valid_ancillae_box' (c2 · c1).
Proof.
  intros w1 w2 w3 c1 c2 pf_c1 pf_c2 valid1 valid2. unfold valid_ancillae_box.
(*
  set (H := inSeq_correct _ _ _ c2 c1 pf_c2 pf_c1).
  simpl in H.
  unfold valid_ancillae_box' in *.
  intros ρ M.
  unfold inSeq.
  unfold denote_box.  *)
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
    + lia.
    + apply H_c1; auto.
  }
  apply valid_ancillae_box'_equiv 
    with (b2 := (ASSERT · c2 · INIT) · (ASSERT · c1 · INIT)).
  { repeat rewrite <- inSeq_assoc.
    apply HOAS_Equiv_inSeq; simple_typing False; try easy. 
    apply HOAS_Equiv_inSeq; simple_typing False; try easy. 
  }
  assert (x < S (n+t)) by lia. 
  assert (typed_init : Typed_Box INIT) by simple_typing False.
  assert (typed_assert : Typed_Box ASSERT) by simple_typing False.
  apply valid_inSeq.
    - repeat apply inSeq_WT;  auto. 
    - repeat apply inSeq_WT;  auto. 
    - apply H_c1; auto.
    - apply H_c2; auto.
Qed.



Lemma denote_box_id_circ : forall b w ρ, WF_Matrix ρ ->
      denote_box b (id_circ : Box w w) ρ = ρ.
Proof.
  intros b w ρ.
  simpl. autounfold with den_db. simpl.
  Search subst_pat.
  rewrite add_fresh_split; simpl.
  rewrite subst_pat_fresh_empty.
  rewrite denote_pat_fresh_id.
  rewrite pad_nothing.
  apply super_I.
Qed.

Lemma valid_id_circ : forall w, valid_ancillae_box' (@id_circ w).
Proof.
  intros w ρ T Hρ.
  rewrite denote_box_id_circ.
  * apply mixed_state_trace_1; auto.
  * apply WF_Mixed; auto.
Qed.

(* unsure how to prove - may need a stronger notion of noop *)
Fact symmetric_gate_noop_source : forall n t k g c,
    gate_acts_on k g ->
    noop_source n t c ->
    noop_source n t (g · c · g).
Proof. Admitted.

Fact init_at_noop : forall b m i j,
    valid_ancillae_box' (assert_at b (S m) i · init_at b (S m) j · init_at b m i).
Proof. Admitted.  

(* not sure how to prove this *)
(* must generalize source_symmetric_noop IH to account for 
   multiple valid ancilla at a time *)

Fact symmetric_ancilla_noop_source : forall n t k c b,
      k < S n ->
      noop_source (S n) t c ->
      noop_source n t (assert_at b (n+t) k · c · init_at b (n+t) k).
Proof. Admitted.


Lemma source_symmetric_noop : forall n t c,
      source_symmetric n t c -> noop_source n t c.
Proof.
  intros n t c pf_c.
  induction pf_c.
  * (* id *) destruct n as [ | n]; simpl; auto; intros x pf_x b. fold plus.
    rewrite inSeq_id_l.
    apply valid_ancillae_box'_equiv with (b2 := id_circ).
    + apply assert_init_at_id. lia.
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
      ++ lia.
      ++ lia.
  * (* sym_target_r *)
    apply noop_source_inSeq; auto.
    + eapply gate_acts_on_WT; eauto.
    + apply source_symmetric_WT; auto.
    + destruct n as [ | n]; simpl; auto; intros i pf_i. fold plus.
      apply gate_acts_on_noop_at with (k := k); auto. 
      ++ lia.
      ++ lia.
  * (* sym_ancilla *)
    apply symmetric_ancilla_noop_source; auto.
Qed.

Ltac show_ancilla_free :=
  repeat match goal with
  | [|- ancilla_free_box _ ] => apply af_box; intros
  | [|- ancilla_free (letpair _ _ ?p _)] => dependent destruction p; simpl
  | [|- ancilla_free (comp _ (output ?p) _)] => dependent destruction p; simpl
  | [|- ancilla_free (gate _ _ _)] => apply af_gate; intros                                                                     
  | [|- ancilla_free (output _)] => apply af_output; intros                                                                     
  | [|- not_assert _] => constructor
  end.

(* obvious lemmas *)
Fact ancilla_free_X_at : forall n i pf_i, ancilla_free_box (X_at n i pf_i).
Proof.
  intros n i. gen n.
  induction i as [ | i]; intros n pf.
  - unfold X_at, unitary_at1; simpl.
    destruct n; try (exfalso;lia).
    show_ancilla_free.
  - destruct n; try (exfalso;lia).
    unshelve epose (pf' := _ : i < n); try lia.
    specialize (IHi n pf'). (* annoying case *)
Admitted.

Fact ancilla_free_CNOT_at : forall n a b, ancilla_free_box (CNOT_at n a b).
Admitted.

Fact ancilla_free_Toffoli_at : forall n a b c, ancilla_free_box (Toffoli_at n a b c).
Admitted.

Fact ancilla_free_seq : forall W W' W'' (c1 : Box W W') (c2 : Box W' W''), 
  ancilla_free_box c1 ->
  ancilla_free_box c2 ->
  ancilla_free_box (c1 ;; c2).
Admitted.


Theorem source_symmetric_valid : forall (n t : nat) (c : Square_Box ((n + t) ⨂ Qubit)),
  source_symmetric n t c -> 
  valid_ancillae_box c.
Proof.
  intros n t c H.
  induction H.
  - apply ancilla_free_box_valid.
    constructor.     
    constructor.
  - inversion g0.
    + unfold valid_ancillae_box. intros TB.
      apply functional_extensionality. intros ρ.
      repeat simpl_rewrite inSeq_correct; try apply inSeq_WT; 
        try apply unitary_at1_WT; try apply source_symmetric_WT; trivial.
      unfold compose_super.
      apply source_symmetric_WT in H.
      rewrite IHsource_symmetric; trivial.
      rewrite ancilla_free_box_valid; [|apply ancilla_free_X_at | type_check  ]. 
      reflexivity.
    + unfold valid_ancillae_box. intros TB.
      apply functional_extensionality. intros ρ.
      repeat simpl_rewrite inSeq_correct; try apply inSeq_WT; try apply CNOT_at_WT;
        try apply source_symmetric_WT; trivial.
      unfold compose_super.
      apply source_symmetric_WT in H.
      rewrite IHsource_symmetric; trivial.
      rewrite ancilla_free_box_valid; [|apply ancilla_free_CNOT_at | type_check]. 
      reflexivity.
    + unfold valid_ancillae_box. intros TB.
      apply functional_extensionality. intros ρ.
      repeat simpl_rewrite inSeq_correct; try apply inSeq_WT; 
        try apply Toffoli_at_WT; try apply source_symmetric_WT; trivial.
      unfold compose_super.
      apply source_symmetric_WT in H.
      rewrite IHsource_symmetric; trivial.
      rewrite ancilla_free_box_valid; [|apply ancilla_free_Toffoli_at | type_check]. 
      reflexivity.
  - inversion g0.
    + unfold valid_ancillae_box. intros TB.
      apply functional_extensionality. intros ρ.
      repeat simpl_rewrite inSeq_correct; try apply inSeq_WT; 
        try apply unitary_at1_WT; try apply source_symmetric_WT; trivial.
      unfold compose_super.
      apply source_symmetric_WT in H.
      rewrite IHsource_symmetric; trivial.
      rewrite ancilla_free_box_valid; [|apply ancilla_free_X_at | type_check  ]. 
      reflexivity.
    + unfold valid_ancillae_box. intros TB.
      apply functional_extensionality. intros ρ.
      repeat simpl_rewrite inSeq_correct; try apply inSeq_WT; try apply CNOT_at_WT;
        try apply source_symmetric_WT; trivial.
      unfold compose_super.
      apply source_symmetric_WT in H.
      rewrite IHsource_symmetric; trivial.
      rewrite ancilla_free_box_valid; [|apply ancilla_free_CNOT_at | type_check]. 
      reflexivity.
    + unfold valid_ancillae_box. intros TB.
      apply functional_extensionality. intros ρ.
      repeat simpl_rewrite inSeq_correct; try apply inSeq_WT; 
        try apply Toffoli_at_WT; try apply source_symmetric_WT; trivial.
      unfold compose_super.
      apply source_symmetric_WT in H.
      rewrite IHsource_symmetric; trivial.
      rewrite ancilla_free_box_valid; [|apply ancilla_free_Toffoli_at | type_check]. 
      reflexivity.
  - inversion g0.
    + unfold valid_ancillae_box. intros TB.
      apply functional_extensionality. intros ρ.
      repeat simpl_rewrite inSeq_correct; try apply inSeq_WT; 
        try apply unitary_at1_WT; try apply source_symmetric_WT; trivial.
      unfold compose_super.
      apply source_symmetric_WT in H.
      rewrite IHsource_symmetric; trivial.
      rewrite ancilla_free_box_valid; [|apply ancilla_free_X_at | type_check  ]. 
      reflexivity.
    + unfold valid_ancillae_box. intros TB.
      apply functional_extensionality. intros ρ.
      repeat simpl_rewrite inSeq_correct; try apply inSeq_WT; try apply CNOT_at_WT;
        try apply source_symmetric_WT; trivial.
      unfold compose_super.
      apply source_symmetric_WT in H.
      rewrite IHsource_symmetric; trivial.
      rewrite ancilla_free_box_valid; [|apply ancilla_free_CNOT_at | type_check]. 
      reflexivity.
    + unfold valid_ancillae_box. intros TB.
      apply functional_extensionality. intros ρ.
      repeat simpl_rewrite inSeq_correct; try apply inSeq_WT; 
        try apply Toffoli_at_WT; try apply source_symmetric_WT; trivial.
      unfold compose_super.
      apply source_symmetric_WT in H.
      rewrite IHsource_symmetric; trivial.
      rewrite ancilla_free_box_valid; [|apply ancilla_free_Toffoli_at | type_check]. 
      reflexivity.
  - (* only interesting case *)
    specialize (source_symmetric_noop (S n) t c) as SSN.
    unfold noop_source in SSN.
    fold plus in SSN.
    unfold noop_on in SSN.
    apply valid_ancillae_box_equal.
    apply SSN; trivial.
    lia.
Qed.

(* The noop property implies actual reversibility *)

Definition reversible {W1 W2} (c : Box W1 W2) : Prop :=
  exists c', c · c' ≡ id_circ.

Definition self_inverse {W} (c : Box W W) : Prop :=
  c · c ≡ id_circ. 

Fact gate_acts_on_reversible : forall m g k (pf_g : @gate_acts_on m k g),
      g · g ≡ id_circ.
Admitted.

(* Version without typing restrictions *)
Fact HOAS_Equiv_inSeq' :
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
      { lia. }
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
   lia.
Qed.
Close Scope circ_scope.
