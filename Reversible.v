Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Denotation.
Require Import DBCircuits.
Require Import TypeChecking.

Require Import List.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.
Delimit Scope matrix_scope with M.
Delimit Scope circ_scope with qc.

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

Theorem strong_induction:
forall P : nat -> Type,
(forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
forall n : nat, P n.
Proof.
  intros P H n.
  apply H. intros k Hk.
Admitted.
    
Definition CNOT_at n (i j : Var) (pf_i : i < n) (pf_j : j < n) (pf_i_j : i <> j)
         : Box (n ⨂ Qubit) (n ⨂ Qubit).
Proof.
  remember (i+j) as x eqn:Hx.
  gdep n. gdep j. gdep i.
  set (P x := forall i j, i <> j -> x = i + j ->    
              forall n, i < n -> j < n -> Box (n ⨂ Qubit) (n ⨂ Qubit)).
  change (P x).
  induction x using strong_induction. rename H into CNOT_at. unfold P in *. clear P.
  intros i j pf_i_j Hx n pf_i pf_j.
    destruct n as [ | [ | n]]; try omega.
    destruct i as [ | i']; [ destruct j as [ | [ | j']] | destruct j as [ | j']]; simpl.
    - (* i = 0, j = 0 *)  omega.
    - (* i = 0, j = 1 *)
      refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q; 
                       let_ (q0,q1) ← CNOT $(q0,q1);
                       output (q0,(q1,qs))).
    - (* i = 0, j = S (S j') *) 
      refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q;
                       let_ (q0,qs) ← CNOT_at _ _ 0 (S j') _ _ (S n) _ _ $ output (q0,qs);
                        output (q0,(q1,qs))); [ | omega | reflexivity | omega | omega]. omega.
    - destruct i' as [ | i'].
      -- (* i = 1, j = 0 *)  
        refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q; 
                         let_ (q1,q0) ← CNOT $(q1,q0);
                         output (q0,(q1,qs))).
      -- (* i = S (S i'), j = 0 *) 
        refine (box_ q ⇒ let_ (q0,(q1,qs)) ← q;
                         let_ (q0,qs) ← CNOT_at _ _ (S i') 0 _ _ (S n) _ _ $ output (q0,qs);
                         output (q0,(q1,qs))); [ | omega | reflexivity | omega | omega]; omega.
    - (* i = S i', j = S j' *)
        refine (box_ q ⇒ let_ (q0,qs) ← q;
                         let_ q ← CNOT_at _ _ i' j' _ _ (S n) _ _ $ output qs;
                         output (q0,qs)); [ | omega | reflexivity | omega | omega]; omega.
Defined.

Lemma CNOT_at_WT n i j pf_i pf_j pf_i_j :
      Typed_Box (CNOT_at n i j pf_i pf_j pf_i_j).
Proof.
  remember (i+j) as x eqn:Hx.
  gdep n. gdep j. gdep i.
  set (P x := forall i j (pf_i_j : i <> j),
              x = i + j ->
              forall n (pf_i : i < n) (pf_j : j < n), Typed_Box (CNOT_at n i j pf_i pf_j pf_i_j)).
  change (P x).
  induction x using strong_induction. rename H into IH. unfold P in *. clear P.
  intros i j pf_i_j Hx n pf_i pf_j.
    destruct n as [ | [ | n]];  
      [omega | destruct i; try omega; destruct j; try omega; contradiction | ].
    destruct i as [ | i']; [ destruct j as [ | [ | j']] | destruct j as [ | j']].
    - (* i = 0, j = 0 *)  omega.
    - (* i = 0, j = 1 *) admit.
    - (* i = 0, j > 1 *) 
Admitted.

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
                                         · c · init_at b (n+t) i (in_source_in_scope _ _ _ pf_i))
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
  - (* target_r *) admit (* same as target_r *).
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
Admitted.


    
(*
Fixpoint make_reversible {W} (c : Circuit W) (r : reversible c)
  (stack : list ({ W' : WType & Unitary W' & Pat W' })) : Circuit W.
  induction r eqn:Er.
  - induction stack eqn:Es.
    + exact (output p).
    + destruct a as [W' u p']. 
      exact (gate_ p'' ← u @p';
             make_reversible W (output p) r l).
  - exact (let stack' := ((existT2 _ _ Qubit X p1) :: stack) in stack').
    pose stack'.

  :=
  match r with 
  | rev_output p => match stack with 
                   | (exist _ W' (u,p')%core :: stack' => gate_ p'' ← u @p';
                                            make_reversible (rev_output p) r stack'
  | rev_not p c r' => gate_ p' ← X @p;
                     make_reversible c r' stack';
                  
                  
               
 Circuit W. 


Fixpoint reverse {W} (c : Circuit W) (R : reversible c): Circuit W := 
  match R with
  | rev_output p => output p
  | rev_not p1 c => reverse c; 
                   gate_ p ← X 
  | rev_cnot   : forall p1 c, reversible c -> reversible (gate_ p2 ←  CNOT @p1; c)
  | rev_ccnot  : forall p1 c, reversible c -> reversible (gate_ p2 ← CCNOT @p1; c).


Fixpoint reverse {W} (c : Circuit W) (R : reversible c): Circuit W := 
  match R with
  | rev_output p => 
  | rev_not    : forall p1 c, reversible c -> reversible (gate_ p2 ←  X @p1; c)
  | rev_cnot   : forall p1 c, reversible c -> reversible (gate_ p2 ←  CNOT @p1; c)
  | rev_ccnot  : forall p1 c, reversible c -> reversible (gate_ p2 ← CCNOT @p1; c).
  
*)

