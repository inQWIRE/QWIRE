Require Export TypeChecking.
Require Import DBCircuits.
Require Import QASM.
Require Import QASMPrinter.

Open Scope circ_scope.

Definition bell00 : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒  
    gate_ a ← init0 @();
    gate_ b ← init0 @();
    gate_ a ← H @a;
    gate_ z ← CNOT @(a,b);
    output z.

Definition alice_for_qasm : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← H @q;
    gate_ x     ← measQ @q;
    gate_ y     ← measQ @a;
    output (x,y).

Definition bob_for_qasm : Box (Qubit ⊗ Qubit ⊗ Qubit) (Qubit) :=
  box_ xyb ⇒ 
    let_ ((x,y),b) ← output xyb ; 
    gate_ (y,b)  ← ctrl X @(y,b);
    gate_ (x,b)  ← ctrl Z @(x,b);
    gate_ x' ← meas @x;
    gate_ y' ← meas @y;
    gate_ _ ← discard @x';
    gate_ _ ← discard @y';
    output b.

Definition main : Box One Bit :=
  box_ () ⇒
    gate_ q    ← init0 @();
    gate_ q    ← H @q;
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice_for_qasm (q,a) ;
    let_ p     ← unbox bob_for_qasm (x,y,b) ;
    gate_ po   ← meas @p ;
    output po.

Eval compute in hoas_to_db_box main.
Eval compute in db_to_qasm_box (hoas_to_db_box main).
Eval compute in printer (db_to_qasm_box (hoas_to_db_box main)).

Close Scope circ_scope.
