Require Import Datatypes.
Require Export TypeChecking.
Require Import HOASLib.
Import ListNotations.
Open Scope list_scope.

(*******************)
(** Teleportation **)
(*******************)

Notation H := (U _H).
Notation X := (U _X).
Notation Y := (U _Y).
Notation Z := (U _Z).
Notation CNOT := (U CNOT).
Variable _I : (forall {n : nat}, Unitary 1 (Qubit n)).
Notation I := (U _I).

Definition bell00 : Box One (Qubit 2 ⊗ Qubit 2) :=
  box_ _ ⇒  
    gate_ a     ← init0 @();
    gate_ b     ← init0 @();
    gate_ a     ← H @a;
    gate_ (a,b) ← CNOT @(a,,b); 
    (a,b).

(* Type inference works, but isn't giving as simple of an expression as we'd like? *)
Definition bell00' : Box One (Qubit _ ⊗ Qubit _) :=
  box_ _ ⇒  
    gate_ a     ← init0 @();
    gate_ b     ← init0 @();
    gate_ a     ← H @a;
    gate_ (a,b) ← CNOT @(a,,b); 
    (a,b).
Print bell00'. 

Definition alice : Box (Qubit 0 ⊗ Qubit 2) (Bit ⊗ Bit) :=
  box_ qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← H   @q;
    gate_ x     ← meas @q;
    gate_ y     ← meas @a;
    (x,y).

Definition bob : Box (Bit ⊗ Bit ⊗ Qubit 2) (Qubit 4) :=
  box_ (x,y,b) ⇒ 
    gate_ (y,b)    ← U (bit_ctrl _X) @(y,,b);
    gate_ (x,b)    ← U (bit_ctrl _Z) @(x,,b);
    discard_ (x,y) ;  
    output b.

Definition teleport : Box (Qubit 0) (Qubit 4) :=
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,,a) ;
    unbox bob (x,,y,,b).

Definition bob_distant {n} (u v : bool) : Box (Qubit n) (Qubit (2 + n)) :=
  box_ b ⇒
    gate_ b ← (if v then X else I) @b;
    gate_ b ← (if u then Z else I) @b;
    output b.

Definition teleport_distant : Box (Qubit 0) (Qubit 4) :=
  box_ q ⇒
    let_ (a,b)  ← unbox bell00 ();
    let_ (x,y)  ← unbox alice (q,,a);
    lift_ (u,v) ← (x,y);
    unbox (bob_distant u v) b.

Check teleport_distant.

(* Now with error correction! *)

Definition bell_EC : Box One (Qubit 2 ⊗ Qubit 2) :=
  box_ () ⇒  
    gate_ a ← init0 @();
    gate_ b ← init0 @();
    gate_ a ← H @a;
    gate_ (a,b) ← CNOT @(a,,b); 
    output (a,,b).

Definition alice_EC : Box (Qubit 0 ⊗ Qubit 2) (Bit ⊗ Bit) :=
  box_ qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← EC   @q;
    gate_ q     ← H    @q;
    gate_ x     ← meas @q;
    gate_ y     ← meas @a;
    output (x,,y).

Definition bob_EC : Box (Bit ⊗ Bit ⊗ Qubit 2) (Qubit 1) :=
  box_ (x,y,b) ⇒ 
    gate_ (y,b)    ← U (bit_ctrl _X) @(y,,b);
    gate_ b        ← EC              @b;
    gate_ (x,b)    ← U (bit_ctrl _Z) @(x,,b);
    discard_ (x,y) ;  
    output b.

Definition teleport_EC : Box (Qubit 0) (Qubit 1) :=
  box_ q ⇒
    let_ (a,b) ← unbox bell_EC () ;
    let_ (x,y) ← unbox alice_EC (q,,a) ;
    unbox bob_EC (x,,y,,b).

Lemma teleport_EC_WT : Typed_Box teleport_EC 3.
Proof. type_check; lia. Qed.
