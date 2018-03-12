Require Import String.
Require Export TypeChecking.
Require Import DBCircuits.
Require Import QASM.
Require Import QASMPrinter.

Open Scope circ_scope.

(* Example1 - Teleport *)

Definition bell00 : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒  
    gate_ a ← init0 @();
    gate_ b ← init0 @();
    gate_ a ← H @a;
    gate_ z ← CNOT @(a,b);
    output z.

Definition alice : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← H @q;
    gate_ x     ← measQ @q;
    gate_ y     ← measQ @a;
    output (x,y).

Definition bob : Box (Qubit ⊗ Qubit ⊗ Qubit) (Qubit) :=
  box_ xyb ⇒ 
    let_ ((x,y),b) ← output xyb ; 
    gate_ (y,b)  ← ctrl X @(y,b);
    gate_ (x,b)  ← ctrl Z @(x,b);
    gate_ x' ← meas @x;
    gate_ y' ← meas @y;
    gate_ _ ← discard @x';
    gate_ _ ← discard @y';
    output b.

Definition teleport : Box One Bit :=
  box_ () ⇒
    gate_ q    ← init0 @();
    gate_ q    ← H @q;
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    let_ p     ← unbox bob (x,y,b) ;
    gate_ po   ← meas @p ;
    output po.

Definition teleport_db := Eval compute in hoas_to_db_box teleport.
Definition teleport_qasm := Eval compute in db_to_qasm_box teleport_db.
Definition teleport_string := Eval compute in printer teleport_qasm.
Print teleport_string.

(* Example2 - n-adder *)

Require Import ReversibleExample.

Definition adder_1_circ := n_adder_circ 1.
Definition adder_1_example : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒
    gate_ cin  ← init1 @() ;
    gate_ x0   ← init1 @() ;
    gate_ y0   ← init1 @() ;
    gate_ z0   ← init0 @() ;
    gate_ cout ← init0 @() ;
    let_ res   ← unbox adder_1_circ
         (pair cout (pair z0 (pair y0 (pair x0 (pair cin unit))))) ;
    let_ (cout', (z0', rem))
         ← output res ;
    output (cout', z0').

Definition adder_1_example_db := Eval compute in hoas_to_db_box adder_1_example.
Definition adder_1_example_qasm := Eval compute in db_to_qasm_box adder_1_example_db.
Definition adder_1_example_string := Eval compute in printer adder_1_example_qasm.
Print adder_1_example_string.

Close Scope circ_scope.
