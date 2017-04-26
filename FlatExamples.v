Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import Contexts.
Require Import HOASCircuits.
Require Import FlatCircuits.
(* Import TC. *)
Import ListNotations.
Open Scope list_scope.

(** Projecting out elements of tensors **)

Inductive sigT23 (A:Type) (P Q R : A -> A -> Type) : Type :=
    existT23 : forall (x y : A), P x y -> Q x y -> R x y -> sigT23 A P Q R.

Arguments existT23 {A} {P Q R} x y p1 p2 M.

Program Definition wproj {Γ W1 W2} (p : Pat Γ (Tensor W1 W2)) : 
  sigT23 OCtx (fun x y => Pat x W1) (fun x y => Pat y W2) (fun x y => Γ = x ⋓ y) :=
  match p with 
  | unit => _
  | qubit _ _ _ => _
  | bit _ _ _ => _
  | pair Γ1 Γ2 Γ W1 W2 v M p1 p2 => existT23 Γ1 Γ2 p1 p2 M  
  end.

(*** Typechecking Tactic ***)

Open Scope circ_scope.
Opaque wproj.


(* Prevent compute from unfolding important fixpoints *)
Opaque merge.
Opaque Ctx.
Opaque is_valid.

Ltac goal_has_evars := 
  match goal with 
  [|- ?G ] => has_evars G
  end.

Ltac type_check_once := 
  intros;
  repeat match goal with 
  | [ p : Pat _ One |- _ ]         => inversion p; subst; clear p
  | [ H : Disjoint ?Γ1 ?Γ2 |- _ ]  => apply disjoint_valid in H; trivial
  end; 
  compute in *; 
  subst; 
  (* Runs monoid iff a single evar appears in context *)
  match goal with 
  | [|- is_valid ?Γ] => tryif (has_evar Γ)   
                        then (idtac (*"can't validate"; print_goal*))
                        else (idtac (*"validate"; print_goal*); validate)
  | [|- ?G ]         => tryif (has_evars G)  
                        then (idtac (*"can't monoid"; print_goal*))
                        else (idtac (*"monoid"; print_goal*); monoid)
  end.

(* Useful for debugging *)
Ltac type_check_num := 
  let pre := numgoals in idtac "Goals before: " pre "";
  [> type_check_once..];
  let post := numgoals in idtac "Goals after: " post "";
  tryif (guard post < pre) then type_check_num else idtac "done".

(* Easiest solution *)

Ltac type_check := let n := numgoals in do n [> type_check_once..].

(*** Paper Examples ***)

Set Printing Coercions.

Tactic Notation (at level 0) "make_circ" uconstr(C) := refine C; type_check.
Tactic Notation (at level 0) "box_f" uconstr(p) uconstr(C) := 
  refine (flat_box p C); type_check.

Ltac new_pat p W Γ := 
    let Γ' := fresh "Γ" in
    let v1 := fresh "v" in
    let v2 := fresh "v" in 
    let v3 := fresh "v" in 
(*    let Eq := fresh "Eq" in *)
    set (p := fresh_pat Γ W);
    set (Γ' := fresh_ctx Γ W);
    generalize (fresh_ctx_valid W Γ); intros v1;
    try (assert (v2 : is_valid Γ) by validate;
         generalize (fresh_ctx_merge_valid W Γ v2); intros v3).

(*    set (v' := fresh_ctx_valid W Γ v);
    set (v'' := fresh_ctx_merge_valid W Γ v). *)
(*    apply disjoint_valid in v''; trivial; try apply valid_empty.*)
Print flat_gate.
Notation gate g p1 p2 C := (flat_gate g p1 p2 C).
Notation output_f p := (flat_output p).


Notation "'gate_f' p' ← g @ p ; C" := (gate g p p' C) 
                                          (at level 10, right associativity). 


Notation "()" := unit : circ_scope.
Notation "( x , y , .. , z )" := (pair _ _ _ _ _ _ _ .. (pair _ _ _ _ _ _ _ x y) .. z) (at level 0) : circ_scope.



Definition id_circ {W} : Flat_Box W W.
  new_pat p W ∅.
  box_f p (output_f p).
Defined.

Definition boxed_gate {W1 W2} (g : Gate W1 W2) : Flat_Box W1 W2.
  new_pat p W1 ∅.
  new_pat p' W2 ∅.
  box_f p (
    gate_f p' ← g @p;
    output_f p'). 
Defined.

Definition new_discard : Flat_Box One One.
  new_pat p Bit ∅.
  box_f unit (
    gate_f p    ← new0 @(); 
    gate_f unit ← discard @p;
    output_f () ).
Defined.

Definition init_discard : Flat_Box One One.
  new_pat q Qubit ∅.
  new_pat b Bit ∅.
  box_f () ( 
    gate_f q    ← init0 @();
    gate_f b    ← meas @q;
    gate_f unit ← discard @b;
    output_f () ). 
Defined.

Definition hadamard_measure : Flat_Box Qubit Bit.
  new_pat q Qubit ∅.
  new_pat b Bit ∅.
  box_f q ( 
    gate_f q ← H @q;
    gate_f b ← meas @q;
    output_f b).
Defined.

(*
Definition lift_deutsch (U_f : Gate (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)) : Box One Qubit.
  destruct (fresh_pat ∅ Qubit valid_empty) as [Γx [[Vx _] x]].
  destruct (fresh_pat Γx Qubit Vx) as [Γy [[Vy Dxy] y]].
  box (fun _ =>
    x     ← gate init0 on ();
    x     ← gate H on x;
    y     ← gate init1 on ();
    y     ← gate H on y;
    (x,y) ← gate U_f on (x,y);
    _     ← x;
    output y).
Defined.
*)

Definition deutsch (U_f : Gate (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)) : Flat_Box One Qubit.
  new_pat x Qubit ∅.
  new_pat y Qubit Γ.
  new_pat b Bit (Γ ⋓ Γ0).
  box_f () (
    gate_f x     ← init0 @();
    gate_f x     ← H @x;
    gate_f y     ← init1 @();
    gate_f y     ← H @y;
    gate_f (x,y) ← U_f @(x,y);
    gate_f b     ← meas @x;
    gate_f ()    ← discard @b;
    output_f y).
Defined.

Definition init (b : bool) : Flat_Box One Qubit :=
  if b then boxed_gate init1 else boxed_gate init0.

Eval simpl in (init true).
Eval compute in (init true).

Definition coin_flip : Flat_Box One Bit .
  new_pat x Qubit ∅.
  new_pat y Bit ∅.
  box_f () (
    gate_f x ← init0 @();
    gate_f x ← H @x;
    gate_f y ← meas @x;
    output_f y).
Defined.

Definition U_U_trans {W} (U : Unitary W) : Flat_Box W W.
  new_pat p W ∅.
  box_f p (
    gate_f p ← U @p;
    gate_f p ← transpose U @p;
    output_f p
  ).
Defined.


(* *)
