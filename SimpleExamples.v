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
Variable _I : Unitary 1 Qubit.
Notation I := (U _I).

(* Can have 0 input error type if desired: Use () instead of _ at start. *)
Definition bell00 {n} : Box n One 2 (Qubit ⊗ Qubit) :=
  box_ _ ⇒  
    gate_ a     ← init0 @();
    gate_ b     ← init0 @();
    gate_ a     ← H @a;
    gate_ (a,b) ← CNOT @(a,,b); 
    (a,b).

Definition alice {n} : Box n (Qubit ⊗ Qubit) 0 (Bit ⊗ Bit) :=
  box_ qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← H   @q;
    gate_ x     ← meas @q;
    gate_ y     ← meas @a;
    (x,y).

Program Definition bob {n} : Box n (Bit ⊗ Bit ⊗ Qubit) (2 + n) Qubit :=
  box_ (x,y,b) ⇒ 
    gate_ (y,b)    ← U (bit_ctrl _X) @(y,,b);
    gate_ (x,b)    ← U (bit_ctrl _Z) @(x,,b);
    discard_ (x,y) ;  
    output b.
Next Obligation. rewrite Nat.max_id. rewrite Nat.max_r; omega. Defined.

Definition teleport {n} : Box n Qubit 4 Qubit :=
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,,a) ;
    unbox bob (x,,y,,b).

Definition bob_distant {n} (u v : bool) : Box n Qubit (2 + n) Qubit :=
  box_ b ⇒
    gate_ b ← (if v then X else I) @b;
    gate_ b ← (if u then Z else I) @b;
    output b.

Definition teleport_distant {n} : Box n Qubit 4 Qubit :=
  box_ q ⇒
    let_ (a,b)  ← unbox bell00 ();
    let_ (x,y)  ← unbox alice (q,,a);
    lift_ (u,v) ← (x,y);
    unbox (bob_distant u v) b.

Check teleport_distant.

(* Now with error correction! *)

Definition bell_EC : Box 0 One 2 (Qubit ⊗ Qubit) :=
  box_ () ⇒  
    gate_ a ← init0 @();
    gate_ b ← init0 @();
    gate_ a ← H @a;
    gate_ (a,b) ← CNOT @(a,,b); 
    output (a,,b).

Definition alice_EC {n} : Box n (Qubit ⊗ Qubit) 0 (Bit ⊗ Bit) :=
  box_ qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← EC   @q;
    gate_ q     ← H    @q;
    gate_ x     ← meas @q;
    gate_ y     ← meas @a;
    output (x,,y).

(* Doesn't work! Even after error correction on b, (x,m) has 2 errors! *)
Fail Definition bob_EC : Box 2 (Bit ⊗ Bit ⊗ Qubit) 1 Qubit :=
  box_ (x,y,b) ⇒ 
    gate_ (y,b)    ← U (bit_ctrl _X) @(y,,b);
    gate_ b        ← EC              @b;
    gate_ (x,b)    ← U (bit_ctrl _Z) @(x,,b);
    discard_ (x,y) ;  
    output b.

Definition bob_distant_EC (u v : bool) : Box 2 Qubit 1 Qubit :=
  box_ b ⇒
    gate_ b ← (if v then X else I) @b;
    gate_ b ← EC                   @b;
    gate_ b ← (if u then Z else I) @b;
    output b.

Definition teleport_distant_EC {n} : Box n Qubit 1 Qubit :=
  box_ q ⇒
    let_ (a,b)  ← unbox bell_EC ();
    let_ (x,y)  ← unbox alice_EC (q,,a);
    lift_ (u,v) ← (x,y);
    unbox (bob_distant_EC u v) b.
