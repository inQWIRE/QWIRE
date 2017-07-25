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

Module F.

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

Ltac print_goal :=
  match goal with 
  | [|- ?G ] => idtac G
  end.

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
  end; try solve [vm_compute; eauto].

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

Notation gate g p1 p2 C := (flat_gate g p1 p2 C).
Notation output_f p := (flat_output p).


Notation "'gate_f' p' ← g @ p ; C" := (gate g p p' C) 
                                          (at level 10, right associativity). 


Notation "()" := unit : circ_scope.
Notation "( x , y , .. , z )" := (pair _ _ _ _ _ _ _ .. (pair _ _ _ _ _ _ _ x y) .. z) (at level 0) : circ_scope.

(****************
Non-Concrete examples 
*****************)

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

Definition unitary_transpose {W} (U : Unitary W) : Flat_Box W W.
  new_pat p W ∅.
  box_f p (
    gate_f p ← U @p;
    gate_f p ← transpose U @p;
    output_f p
  ).
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

Definition coin_flip : Flat_Box One Bit .
  new_pat x Qubit ∅.
  new_pat y Bit ∅.
  box_f () (
    gate_f x ← init0 @();
    gate_f x ← H @x;
    gate_f y ← meas @x;
    output_f y).
Defined.

Definition bell00 : Flat_Box One (Qubit ⊗ Qubit).
  new_pat a Qubit ∅.
  new_pat b Qubit Γ.
  new_pat z (Qubit ⊗ Qubit) ∅.  
  box_f () (  
    gate_f a ← init0 @();
    gate_f b ← init0 @();
    gate_f a ← H @a;
    gate_f z ← CNOT @(a,b);
    output_f z).
Defined.


Definition teleport_direct : Flat_Box Qubit Qubit.
  new_pat q Qubit ∅.
  new_pat a Qubit Γ.          
  new_pat b Qubit (Γ ⋓ Γ0).          
  new_pat x Bit ∅.
  new_pat y Bit Γ2.

  box_f q (  
  (* bell00 *)
    gate_f a     ← init0 @();
    gate_f b     ← init0 @();
    gate_f a     ← H @a;
    gate_f (a,b) ← CNOT @(a,b);

  (* alice *)
    gate_f (q,a) ← CNOT @(q,a);
    gate_f q     ← H @q;
    gate_f x     ← meas @q;
    gate_f y     ← meas @a;

  (* bob *)
    gate_f (y,b)  ← bit_ctrl σx @(y,b);
    gate_f (x,b)  ← bit_ctrl σz @(x,b);
    gate_f ()     ← discard @y;   
    gate_f ()     ← discard @x;
    output_f b).
Defined.

(* A different approach to effecient typechecking of concrete circuits *)

(*

(****************
Concrete examples 
*****************)

Transparent merge.

Ltac new_concrete_pat p W Γ := 
    let Γ' := fresh "Γ" in
    set (p := fresh_pat Γ W);
    set (Γ' := fresh_ctx Γ W);
    compute in Γ';
    compute in p.


Ltac monoidc :=
  try match goal with
      | |- ?Γ1 = ?Γ2 => has_evar Γ1; symmetry
      end;
   repeat
   print_goal;
    match goal with
    | |- context [ ?Γ1 ⋓ ?Γ2 ⋓ ?Γ3 ] => rewrite <- (merge_assoc Γ1 Γ2 Γ3)
    | |- ?Γ = ?Γ => reflexivity
    | |- ?Γ1 = ?Γ2 => is_evar Γ2; reflexivity
    | |- ?Γ1 = Valid ?Γ2 => is_evar Γ2; reflexivity
    | |- context [ ?Γ ⋓ ∅ ] => rewrite (merge_nil_r Γ)
    | |- context [ ∅ ⋓ ?Γ ] => rewrite (merge_nil_l Γ)
    | |- _ = ?Γ ⋓ ?Γ' => is_evar Γ; rewrite (merge_comm Γ Γ')
    | |- _ = Valid ?Γ ⋓ ?Γ' => is_evar Γ; rewrite (merge_comm Γ Γ')
    | |- ?Γ = ?Γ ⋓ _ => rewrite merge_nil_r; reflexivity
    | |- ?Γ ⋓ _ = ?Γ ⋓ _ => apply merge_cancel_l
    | |- ?Γ1 ⋓ ?Γ1' = ?Γ ⋓ _ => rewrite (merge_comm Γ1 Γ1')
    end.

Ltac type_check_concrete_once := 
  (* Runs monoid iff a single evar appears in context *)
  repeat match goal with 
  | [|- is_valid ?Γ ] => apply valid_valid
  | [|- _ = match ?Γ with
           | Invalid => Invalid
           | Valid _ => Valid _
           end ]    => instantiate (Γ := Valid _); auto 
  | [|- ?G ]         => tryif (has_evars G)  
                        then (idtac (*"can't monoid"; print_goal*))
                        else monoidc
  end.

Ltac type_check_concrete := let n := numgoals in do n [> type_check_concrete_once..].


Tactic Notation (at level 0) "box_c" uconstr(p) uconstr(C) := 
  refine (flat_box p C); type_check_concrete. 

Definition new_discard_c : Flat_Box One One.
  new_concrete_pat p Bit ∅.
  box_c unit (
    gate_f p    ← new0 @(); 
    gate_f unit ← discard @p;
    output_f () ).
Defined.

Definition init_discard_c : Flat_Box One One.
  new_concrete_pat q Qubit ∅.
  new_concrete_pat b Bit ∅.
  box_c () ( 
    gate_f q    ← init0 @();
    gate_f b    ← meas @q;
    gate_f unit ← discard @b;
    output_f () ). 
Defined.

Definition hadamard_measure_c : Flat_Box Qubit Bit.
  new_concrete_pat q Qubit ∅.
  new_concrete_pat b Bit ∅.
  box_c q ( 
    gate_f q ← H @q;
    gate_f b ← meas @q;
    output_f b).
Defined.

Search (Valid _ = Valid _).

Ltac type_check_concrete_new := 
  simpl;
  try instantiate (1 := Valid _);
  simpl; 
  repeat match goal with 
  | [|- is_valid ?Γ ] => apply valid_valid
  | [|- Valid _ = Valid _ ] => reflexivity
  | [|- ?Γ = Valid _ ] => is_evar Γ; reflexivity
  | [|- Valid _ = ?Γ ] => is_evar Γ; reflexivity
  | [|- Valid _ = match ?Γ with
           | Invalid => Invalid
           | Valid _ => Valid _
           end ]    => instantiate (1 := Valid _); simpl (* prefer Γ := Valid _ *)
  end.

Definition deutsch_c (U_f : Gate (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)) : Flat_Box One Qubit.
  new_concrete_pat x Qubit ∅.
  new_concrete_pat y Qubit Γ.
  new_concrete_pat b Bit (Γ ⋓ Γ0).

(*
  box_c () (
    gate_f x     ← init0 @();
    gate_f x     ← H @x;
    gate_f y     ← init1 @();
    gate_f y     ← H @y;
    gate_f (x,y) ← U_f @(x,y);
    gate_f b     ← meas @x;
    gate_f ()    ← discard @b;
    output_f y).
*)

refine( flat_box () (
    gate_f x     ← init0 @();
    gate_f x     ← H @x;
    gate_f y     ← init1 @();
    gate_f y     ← H @y;
    gate_f (x,y) ← U_f @(x,y);
    gate_f b     ← meas @x;
    gate_f ()    ← discard @b;
    output_f y)).


Defined.

Definition init (b : bool) : Flat_Box One Qubit :=
  if b then boxed_gate init1 else boxed_gate init0.

Definition coin_flip : Flat_Box One Bit .
  new_concrete_pat x Qubit ∅.
  new_concrete_pat y Bit ∅.
  box_c () (
    gate_f x ← init0 @();
    gate_f x ← H @x;
    gate_f y ← meas @x;
    output_f y).
Defined.

(* teleport *)
Definition bell00 : Flat_Box One (Qubit ⊗ Qubit).
  new_concrete_pat a Qubit ∅.
  new_concrete_pat b Qubit Γ.
  new_concrete_pat z (Qubit ⊗ Qubit) ∅.  
  box_c () (  
    gate_f a ← init0 @();
    gate_f b ← init0 @();
    gate_f a ← H @a;
    gate_f z ← CNOT @(a,b);
    output_f z).
Defined.

Print bell00.

Definition alice : Flat_Box (Qubit⊗Qubit) (Bit⊗Bit).
  new_concrete_pat q Qubit ∅. 
  new_concrete_pat a Qubit Γ.
  new_concrete_pat x Bit ∅. 
  new_concrete_pat y Bit Γ.
  new_concrete_pat qa (Qubit ⊗ Qubit) ∅.
  box_c qa ( 
    gate_f (q,a) ← CNOT @qa;
    gate_f q     ← H @q;
    gate_f x     ← meas @q;
    gate_f y     ← meas @a;
    output_f (x,y)); vm_compute; eauto. (* Modify type_check for flat circs? *)
Defined.


Definition teleport_direct : Flat_Box Qubit (Qubit ⊗ Bit ⊗ Bit).
  new_concrete_pat q Qubit ∅.
  new_concrete_pat a Qubit Γ.          
  new_concrete_pat b Qubit (Γ ⋓ Γ0).          
  new_concrete_pat x Bit ∅.
  new_concrete_pat y Bit Γ2.

  simpl in Γ, Γ0, Γ1.
  compute in q, a, b.
  unfold FlatCircuits.fresh_pat_obligation_1 in q.
  simpl in q.

  box_c q (  
  (* bell00 *)
    gate_f a     ← init0 @();
    gate_f b     ← init0 @();
    gate_f a     ← H @a;
    gate_f (a,b) ← CNOT @(a,b);

  (* alice *)
    gate_f (q,a) ← CNOT @(q,a);
    gate_f q     ← H @q;
    gate_f x     ← meas @q;
    gate_f y     ← meas @a;

  (* bob *)
    gate_f (y,b)  ← bit_ctrl σx @(y,b);
    gate_f (x,b)  ← bit_ctrl σz @(x,b);
    gate_f ()     ← discard @y;   
    gate_f ()     ← discard @x;
    output_f b).
Defined.


(*
Definition bob' : Box (Bit ⊗ (Bit ⊗ Qubit)) Qubit.
  box_ (xyb ⇒
    let_  (x,yb)  ← output xyb;
    gate_ (y,b)   ← bit_ctrl σx @yb;
    gate_ (x,b)   ← bit_ctrl σx @(x,b);
    gate_ ()      ← discard @y;
    gate_ ()      ← discard @x;
    output b).
Defined.

Definition bob : Box (Bit⊗Bit⊗Qubit) Qubit.
  box_ xyb ⇒ 
    let_ ((x,y),b) ← output xyb ; 
    gate_ (y,b)  ← bit_ctrl σx @(y,b);
    gate_ (x,b)  ← bit_ctrl σz @(x,b);
    gate_ ()     ← discard @y ;   
    gate_ ()     ← discard @x ;
    output b.
Defined.

Definition teleport' : Box Qubit Qubit.
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    unbox bob' (x,(y,b)).
Defined.

Definition teleport : Box Qubit Qubit.
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    unbox bob (x,y,b).
Defined.
*)

*)

End F.

(* *)
