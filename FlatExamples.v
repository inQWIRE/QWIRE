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
Open Scope circ_scope.
Definition wproj {w1 w2} (p : Pat (w1 ⊗ w2)) : Pat w1 * Pat w2 :=
  match p with
  | unit => (unit, unit)
  | qubit n => (unit, unit)
  | bit n => (unit, unit)
  | pair p1 p2 => (p1, p2)  
  end.

(*** Typechecking Tactic ***)

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

Notation gate g p1 p2 C := (flat_gate g p1 p2 C).
Notation output_f p := (flat_output p).
Notation box_f p C  := (flat_box p C).
Notation "'gate_f' p' ← g @ p ; C" := (gate g p p' C) 
                                          (at level 10, right associativity). 

About pair.
Notation "()" := unit : circ_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) (at level 0) : circ_scope.

(****************
Examples 
*****************)

Definition id_circ (W : WType) : Flat_Box W W :=
  let (p,n) := fresh_pat W 0 in
  box_f p (output_f p).

Definition boxed_gate {W1 W2} (g : Gate W1 W2) : Flat_Box W1 W2 :=
  let (p,n) := fresh_pat W1 0 in
  let (p',n') := fresh_pat W2 n in
  box_f p (
    gate_f p' ← g @p;
    output_f p'). 

Definition unitary_transpose {W} (U : Unitary W) : Flat_Box W W :=
  let (p,_) := fresh_pat W 0 in
  box_f p (
    gate_f p ← U @p;
    gate_f p ← transpose U @p;
    output_f p
  ).

Definition new_discard : Flat_Box One One :=
  let (p,_) := fresh_pat Bit 0 in
  box_f unit (
    gate_f p    ← new0 @(); 
    gate_f unit ← discard @p;
    output_f () ).

Ltac new_pat q W n :=
  let n' := fresh "n" in
  set (q := fst (fresh_pat W n));
  set (n' := snd (fresh_pat W n));
  simpl in q, n'.

Definition init_discard : Flat_Box One One :=
  let (q,_) := fresh_pat Qubit 0 in
  let (b,_) := fresh_pat Bit 0 in
  box_f () ( 
    gate_f q    ← init0 @();
    gate_f b    ← meas @q;
    gate_f unit ← discard @b;
    output_f () ).

Definition hadamard_measure : Flat_Box Qubit Bit :=
  let (q,_) := fresh_pat Qubit 0 in
  let (b,_) := fresh_pat Bit 0 in
  box_f q ( 
    gate_f q ← H @q;
    gate_f b ← meas @q;
    output_f b).

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

Definition deutsch (U_f : Gate (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)) 
                 : Flat_Box One Qubit :=
  let (x,n) := fresh_pat Qubit 0 in
  let (y,n') := fresh_pat Qubit n in
  let (b,_) := fresh_pat Bit n' in
  box_f () (
    gate_f x     ← init0 @();
    gate_f x     ← H @x;
    gate_f y     ← init1 @();
    gate_f y     ← H @y;
    gate_f (x,y) ← U_f @(x,y);
    gate_f b     ← meas @x;
    gate_f ()    ← discard @b;
    output_f y).

Definition init (b : bool) : Flat_Box One Qubit :=
  if b then boxed_gate init1 else boxed_gate init0.

Definition coin_flip : Flat_Box One Bit :=
  let (x,_) := fresh_pat Qubit 0 in
  let (y,_) := fresh_pat Bit 0 in
  box_f () (
    gate_f x ← init0 @();
    gate_f x ← H @x;
    gate_f y ← meas @x;
    output_f y).

Definition bell00 : Flat_Box One (Qubit ⊗ Qubit) :=
  let (a,n) := fresh_pat Qubit 0 in
  let (b,n') := fresh_pat Qubit n in
  let (z,_) := fresh_pat (Qubit ⊗ Qubit) 0 in
  box_f () (  
    gate_f a ← init0 @();
    gate_f b ← init0 @();
    gate_f a ← H @a;
    gate_f z ← CNOT @(a,b);
    output_f z).


Definition teleport_direct : Flat_Box Qubit Qubit :=
  let (q,n0) := fresh_pat Qubit 0 in
  let (a,n1) := fresh_pat Qubit n0 in
  let (b,n2) := fresh_pat Qubit n1 in
  let (x,n3) := fresh_pat Bit 0 in
  let (y,_)  := fresh_pat Bit n3 in
(*
  new_pat q Qubit ∅.
  new_pat a Qubit Γ.          
  new_pat b Qubit (Γ ⋓ Γ0).          
  new_pat x Bit ∅.
  new_pat y Bit Γ2.
*)
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
