Require Export Prelim.
Require Import IndexContext.

Open Scope list_scope.

(*** Context Definitions ***)

(** Types **)
Inductive WType := Qubit | Bit | One | Tensor : WType -> WType -> WType.
Notation " W1 ⊗ W2 " := (Tensor W1 W2) (at level 40, left associativity)
                     : circ_scope.

Open Scope circ_scope.
Fixpoint size_wtype (W : WType) : nat := 
  match W with
  | One => 0
  | Qubit => 1
  | Bit => 1
  | W1 ⊗ W2 => size_wtype W1 + size_wtype W2
  end.

(* Coq interpretations of wire types *)
Fixpoint interpret (w:WType) : Set :=
  match w with
    | Qubit => bool
    | Bit   => bool 
    | One   => unit
    | w1 ⊗ w2 => (interpret w1) * (interpret w2)
  end.

(* Large tensor product. Right associative with a trailing One  *)
Fixpoint NTensor (n : nat) (W : WType) := 
  match n with 
  | 0    => One
  | S n' => W ⊗ NTensor n' W
  end.

Infix "⨂" := NTensor (at level 30) : circ_scope.

Lemma size_ntensor : forall n W, size_wtype (n ⨂ W) = (n * size_wtype W)%nat.
Proof.
  intros n W.
  induction n; trivial.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Close Scope circ_scope.


(** Variables **)
Definition Var := nat.

Inductive VType :=
| BIT
| QUBIT.

Notation Ctx := (IdxMap VType).

Notation "∅" := (@nil VType).
Notation "Γ == Γ1 ⋓ Γ2" := (Merge Γ1 Γ2 Γ) (at level 20).


(**********************)
(* Patterns and Gates *)
(**********************)

Open Scope circ_scope.
Inductive Pat : WType ->  Set :=
| unit  : Pat One
| qubit : Var -> Pat Qubit
| bit   : Var -> Pat Bit
| pair  : forall {W1 W2}, Pat W1 -> Pat W2 -> Pat (W1 ⊗ W2).

Fixpoint pat_to_list {w} (p : Pat w) : list Var :=
  match p with
  | unit => []
  | qubit x => [x]
  | bit x => [x]
  | pair p1 p2 => pat_to_list p1 ++ pat_to_list p2
  end.

Fixpoint pat_map {w} (f : Var -> Var) (p : Pat w) : Pat w :=
  match p with
  | unit => unit
  | qubit x => qubit (f x)
  | bit x => bit (f x)
  | pair p1 p2 => pair (pat_map f p1) (pat_map f p2)
  end.

Reserved Notation "Γ ⊢ p ':Pat'" (at level 30).

Require Export TypingContext.
Require Export Monoid.

Inductive Types_Pat : Ctx -> forall {W : WType}, Pat W -> Type :=
| types_unit  : [] ⊢ unit :Pat
| types_qubit : forall x, singleton' x QUBIT ⊢ qubit x :Pat
| types_bit   : forall x, singleton' x BIT ⊢ bit x :Pat
| types_pair : forall Γ1 Γ2 Γ w1 w2 (p1 : Pat w1) (p2 : Pat w2),
        Γ == Γ1 ⋓ Γ2
      -> Γ1 ⊢ p1 :Pat
      -> Γ2 ⊢ p2 :Pat
      -> Γ  ⊢ pair p1 p2 :Pat
where "Γ ⊢ p ':Pat'" := (@Types_Pat Γ _ p).

Open Scope circ_scope.
Inductive Unitary : WType -> Set := 
  | H         : Unitary Qubit 
  | X         : Unitary Qubit
  | Y         : Unitary Qubit
  | Z         : Unitary Qubit
(*  | R         : C -> Unitary Qubit (* may add. see also T and S *) *)
  | ctrl      : forall {W} (U : Unitary W), Unitary (Qubit ⊗ W) 
  | bit_ctrl  : forall {W} (U : Unitary W), Unitary (Bit ⊗ W) 
  | transpose : forall {W} (U : Unitary W), Unitary W.

(* NOT, CNOT and Tofolli notation *)
Notation CNOT := (ctrl X).
Notation CCNOT := (ctrl (ctrl X)).

Inductive Gate : WType -> WType -> Set := 
  | U : forall {W} (u : Unitary W), Gate W W
  | BNOT     : Gate Bit Bit
  | init0   : Gate One Qubit
  | init1   : Gate One Qubit
  | new0    : Gate One Bit
  | new1    : Gate One Bit
  | meas    : Gate Qubit Bit
  | discard : Gate Bit One
  | assert0 : Gate Qubit One
  | assert1 : Gate Qubit One.

Coercion U : Unitary >-> Gate.
Close Scope circ_scope.

