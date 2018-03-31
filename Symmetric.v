Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASLib.
Require Import Denotation.
Require Import DBCircuits.
Require Import TypeChecking.

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
  
(*
Lemma CNOT_at_n_0_SS : forall n' j', 
      CNOT_at (S (S n')) 0 (S (S j'))
    = box_ q ⇒ let_ (q0,(q1,qs)) ← q;
               let_ (q0,qs) ← CNOT_at (S n') 0 (S j') $ (q0,qs);
               output (q0,(q1,qs)).
Proof.
  intros. compute. reflexivity.

  induction n'.
  intros n' j'.
  unfold CNOT_at at 1. Opaque CNOT_at.
  unfold eq_rec, eq_rect, eq_rec_r, eq_rect_r. simpl.
  unfold eq_rec, eq_rect, eq_rec_r, eq_rect_r. simpl.
  unfold strong_induction, strong_induction'. simpl.
  apply f_equal, functional_extensionality; intros p.
  dependent destruction p. dependent destruction p2. simpl.
  induction n' as [ | n''].
  { (* n' = 0 *) rewrite CNOT_at_1. simpl. reflexivity. }
  destruct j' as [ | j''].
  { (* j' = 0 *) Transparent CNOT_at. compute. reflexivity. }
  simpl.

  apply f_equal.
Admitted.

Lemma CNOT_at_n_SS_0 : forall n' i',
      CNOT_at (S (S n')) (S (S i')) 0 
    = box_ q ⇒ let_ (q0,(q1,qs)) ← q;
               let_ (q0,qs) ← CNOT_at (S n') (S i') 0 $(q0,qs);
               output (q0,(q1,qs)).
Admitted.
  
Lemma CNOT_at_n_S_S : forall n' i' j',
      CNOT_at (S (S n')) (S i') (S j')
    = box_ q ⇒ let_ (q0,qs) ← q;
               let_ qs ← CNOT_at (S n') i' j' $ output qs;
               output (q0,qs).
Proof.
  intros n' i' j'.
  unfold CNOT_at at 1. Opaque CNOT_at.
  compute. 
  apply f_equal.
  apply functional_extensionality.
  intros p.
  dependent destruction p. dependent destruction p2.
  simpl. compute. 
Admitted.
*)


Definition Toffoli_at n (i j k : Var) (pf_i : i < n) (pf_j : j < n) (pf_k : k < n)
                                      (pf_i_j : i <> j) (pf_i_k : i <> k) (pf_j_k : j <> k)
         : Box (n ⨂ Qubit) (n ⨂ Qubit).
Admitted.


Lemma Toffoli_at_WT : forall n (i j k : Var) (pf_i : i < n) (pf_j : j < n) (pf_k : k < n)
                             (pf_i_j : i <> j) (pf_i_k : i <> k) (pf_j_k : j <> k),
      Typed_Box (Toffoli_at n i j k pf_i pf_j pf_k pf_i_j pf_i_k pf_j_k).
Admitted.


Definition assert (b : bool) : Gate Qubit One := if b then assert1 else assert0.

Definition assert_at (b : bool) (n : nat) (i : nat) (pf_i : i < S n) : Box (S n ⨂ Qubit) (n ⨂ Qubit).
Proof.
Admitted.

Lemma assert_at_WT : forall b n i (pf : (i < S n)%nat), Typed_Box (assert_at b n i pf).
Admitted.

Definition init_at (b : bool) (n : nat) (i : nat) (pf_i : i < S n) : Box (n ⨂ Qubit) (S n ⨂ Qubit).
Admitted.

Lemma init_at_WT : forall b n i (pf : (i < S n)%nat), Typed_Box (init_at b n i pf).
Admitted.

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
                       Symmetric_Gate_Target n t (CNOT_at (n+t) i j pf_i pf_j pf_i_j)
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
                       Symmetric_Gate_Source n t (CNOT_at (n+t) i j pf_i pf_j pf_i_j)
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
                       Symmetric_Box n t (assert_at b (n+t) i (in_source_in_scope _ _ _ pf) 
                                      · c · init_at b (n+t) i (in_source_in_scope _ _ _ pf))
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
                                        (assert_at b (n+t) i (in_source_in_scope _ _ _ pf_i) 
                                         · c' · init_at b (n+t) i (in_source_in_scope _ _ _ pf_i))
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


Lemma denote_id_circ : forall w ρ, ⟦@id_circ w⟧ ρ = ρ.
Admitted.

Lemma init_assert : forall b n t i (pf : i < S n), 
    init_at b (n+t) i (in_source_in_scope (S n) t i pf) 
  · assert_at b (n+t) i (in_source_in_scope (S n) t i pf) ≡ id_circ.
Admitted.
Lemma assert_init : forall b n t i (pf : i < S n), 
    assert_at b (n+t) i (in_source_in_scope (S n) t i pf) 
  · init_at b (n+t) i (in_source_in_scope (S n) t i pf) ≡ id_circ.
Admitted.


Lemma symmetric_reversible : forall n t c (pf_sym : Symmetric_Box n t c),
      symmetric_reverse n t c pf_sym · c ≡ id_circ.
Proof.
  induction pf_sym; simpl.
  - (* id *) apply HOAS_Equiv_id_l.
  - (* target_l *)
      replace (((symmetric_reverse n t c pf_sym) · g) · g · c)
         with (symmetric_reverse n t c pf_sym · (g · g) · c)
         by (repeat rewrite inSeq_assoc; auto).
      transitivity ((symmetric_reverse n t c pf_sym) · c).
      { apply HOAS_Equiv_inSeq; [ | reflexivity].
        rewrite HOAS_Equiv_inSeq; [ | reflexivity | apply symmetric_gate_target_reversible; auto].  
        apply HOAS_Equiv_id_l.
      }
      apply IHpf_sym.
  - (* target_r *) 
    transitivity (g · (symmetric_reverse n t c pf_sym · c) · g).
    { repeat rewrite inSeq_assoc; reflexivity. }
    transitivity (g · g); [ | apply symmetric_gate_target_reversible; auto ]. 
    apply HOAS_Equiv_inSeq; [ | reflexivity].
    rewrite HOAS_Equiv_inSeq; [apply HOAS_Equiv_id_l | reflexivity | ].
    apply IHpf_sym.

  - (* source *)
    transitivity (g · (symmetric_reverse n t c pf_sym · (g · g) · c) · g).
    { repeat rewrite inSeq_assoc; reflexivity. }
    transitivity (g · (symmetric_reverse n t c pf_sym · c) · g).
    { apply HOAS_Equiv_inSeq; [ | reflexivity].
      apply HOAS_Equiv_inSeq; [ reflexivity | ].
      apply HOAS_Equiv_inSeq; [ | reflexivity ].      
      rewrite HOAS_Equiv_inSeq; [ | reflexivity | apply symmetric_gate_source_reversible; auto].
      apply HOAS_Equiv_id_l.
    }
    transitivity (g · g); [ | apply symmetric_gate_source_reversible; auto].
    apply HOAS_Equiv_inSeq; [ | reflexivity].
    rewrite HOAS_Equiv_inSeq; [ | reflexivity | apply IHpf_sym].
    apply HOAS_Equiv_id_l.
  - (* ancilla *)
    set (close := assert_at b (n + t) i (in_source_in_scope (S n) t i pf)).
    set (open := init_at b (n + t) i (in_source_in_scope (S n) t i pf)).
    set (c' := symmetric_reverse (S n) t c pf_sym).
    transitivity (close · (c' · (open · close) · c) · open).
    { repeat (rewrite inSeq_assoc); reflexivity. }
    transitivity (close · (c' · c) · open).
    { apply HOAS_Equiv_inSeq; [ | reflexivity].
      apply HOAS_Equiv_inSeq; [ reflexivity | ].
      apply HOAS_Equiv_inSeq; [ | reflexivity].
      rewrite HOAS_Equiv_inSeq; [ apply HOAS_Equiv_id_l | reflexivity | ].
      apply init_assert.
    }
    transitivity (close · open).
    { apply HOAS_Equiv_inSeq; [ | reflexivity].
      rewrite HOAS_Equiv_inSeq; [  | reflexivity | apply IHpf_sym ].
      apply HOAS_Equiv_id_l.
    }
    apply assert_init.
Qed.
