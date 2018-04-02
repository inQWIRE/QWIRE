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

Open Scope nat_scope.

Lemma size_ntensor : forall n W, size_wtype (n ⨂ W) = (n * size_wtype W)%nat.
Proof.
  intros n W.
  induction n; trivial.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Definition Square_Box W := Box W W.

(* Temporary - just so Oracles.v compiles until made to work with symmetric *)
Parameter CNOT_at : forall (n : nat) (i j : Var), i < n -> j < n -> i <> j -> Square_Box (n ⨂ Qubit)%qc.

Parameter CNOT_at_WT :
forall (n : nat) (i j : Var) (pf_i : i < n) (pf_j : j < n) (pf_i_j : i <> j),
Typed_Box (CNOT_at n i j pf_i pf_j pf_i_j).

Parameter Toffoli_at : forall (n : nat) (i j k : Var),
i < n -> j < n -> k < n -> i <> j -> i <> k -> j <> k -> Square_Box (n ⨂ Qubit)%qc.

Parameter Toffoli_at_WT :
forall (n : nat) (i j k : Var) (pf_i : i < n) (pf_j : j < n) 
  (pf_k : k < n) (pf_i_j : i <> j) (pf_i_k : i <> k) (pf_j_k : j <> k),
Typed_Box (Toffoli_at n i j k pf_i pf_j pf_k pf_i_j pf_i_k pf_j_k).


