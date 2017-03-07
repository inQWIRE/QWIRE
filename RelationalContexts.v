Require Import Arith.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require Import Program.

Inductive WType := Qubit | Bit | One | Tensor : WType -> WType -> WType.

Notation "W1 ⊗ W2" := (Tensor W1 W2) (at level 1, left associativity): circ_scope. 

Open Scope circ_scope.

(* Coq interpretations of wire types *)
Fixpoint interpret (w:WType) : Set :=
  match w with
    | Qubit => bool
    | Bit => bool 
    | One => Datatypes.unit
    | Tensor w1 w2 => (interpret w1) * (interpret w2)
  end.



(*
Inductive NCtx := 
  End : WType -> NCtx
| Cons : option WType -> NCtx -> NCtx.
Inductive Ctx := Empty | NEmpty : NCtx -> Ctx.
*)
Definition Var := nat.
Definition Ctx := list (option WType).

Fixpoint index {A}(ls : list (option A)) (i : nat) : option A :=
  match ls with
  | [] => None
  | h :: t => match i with
              | O => h
              | S i => index t i
              end
  end.
Fixpoint to_list (len : nat) {A} (f : nat -> A) : list A :=
  match len with
  | O => []
  | S len => f O :: to_list len (fun i => f (S i))
  end.


(* Padding with nones is dangerous! Trying alternative.
Inductive EmptyCtx : Ctx -> Set :=
| EmptyNil : EmptyCtx []
| EmptyCons : forall ctx, EmptyCtx ctx -> EmptyCtx (None :: ctx)
.

Inductive SingletonCtx : Var -> WType -> Ctx -> Set :=
| SingletonHere : forall w ctx, EmptyCtx ctx -> SingletonCtx 0 w (Some w :: ctx)
| SingletonLater : forall x w ctx, SingletonCtx x w ctx -> SingletonCtx (S x) w (None :: ctx)
.
*)

(* Temporarily leaving this. If it works, can delete. *)
Inductive EmptyCtx : Ctx -> Set := EmptyNil : EmptyCtx [].

Inductive SingletonCtx : Var -> WType -> Ctx -> Set :=
| SingletonHere : forall w, SingletonCtx 0 w [Some w]
| SingletonLater : forall x w ctx, SingletonCtx x w ctx -> SingletonCtx (S x) w (None :: ctx).

Lemma singletonF (x : Var) (W : WType) : { Γ : Ctx & SingletonCtx x W Γ}.
Proof.
  induction x.
  - eexists. econstructor.
  - destruct IHx.  eexists. econstructor. eauto.
Defined.
  

(* Dead Code? 
Inductive AddCtx : Var -> WType -> Ctx -> Ctx -> Set :=
| AddHere : forall w ctx, AddCtx 0 w (None :: ctx) (Some w :: ctx)
| AddLater : forall x w ctx ctx' m, AddCtx x w ctx ctx' -> AddCtx (S x) w (m :: ctx) (m :: ctx')
.
*)

Inductive MergeOption : option WType -> option WType -> option WType -> Set :=
| MergeNone : MergeOption None None None
| MergeLeft : forall a, MergeOption (Some a) None (Some a)
| MergeRight : forall a, MergeOption None (Some a) (Some a)
.

Inductive MergeCtx : Ctx -> Ctx -> Ctx -> Set :=
| MergeNilL : forall ctx, MergeCtx [] ctx ctx
| MergeNilR : forall ctx, MergeCtx ctx [] ctx
| MergeCons : forall o1 o2 o g1 g2 g, 
              MergeOption o1 o2 o -> MergeCtx g1 g2 g -> MergeCtx (o1 :: g1) (o2 :: g2) (o :: g)
.

Fixpoint mergeF Γ1 Γ2 : option {Γ : Ctx & MergeCtx Γ1 Γ2 Γ}.
Admitted.
Definition flatten_to_list (len : nat) {A} (f : nat -> list A) : list A.
Admitted.


