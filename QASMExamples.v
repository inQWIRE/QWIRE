Require Import String.
Require Export TypeChecking.
Require Import DBCircuits.
Require Export HOASLib.
Require Import QASM.
Require Import QASMPrinter.

Open Scope circ_scope.

(* Example1 - Teleport *)
Locate "()".
Definition bell00 : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒  
    gate_ a ← init0 @();
    gate_ b ← init0 @();
    gate_ a ← H @a;
    CNOT $(a,b).

Definition alice : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← H @q;
    gate_ x     ← measQ @q;
    gate_ y     ← measQ @a;
    (x,y).

Definition bob : Box (Qubit ⊗ Qubit ⊗ Qubit) (Qubit) :=
  box_ xyb ⇒ 
    let_ ((x,y),b) ← output xyb ; 
    let_ (y,b)  ← ctrl X $(y,b);
    let_ (x,b)  ← ctrl Z $(x,b);
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
    let_ (x,y) ← alice $(q,a) ;
    let_ p     ← bob $(x,y,b) ;
    gate_ po   ← meas @p ;
    output po.

Definition teleport_db := Eval compute in hoas_to_db_box teleport.
Definition teleport_qasm := Eval compute in db_to_qasm_box teleport_db.
Definition teleport_string := Eval compute in printer teleport_qasm.
Print teleport_string.

(* Example2 - n-adder *)

Require Import Arithmetic.

Definition adder_1_circ := adder_circ_n 1.
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
    (cout', z0').

Definition adder_1_example_db := Eval compute in hoas_to_db_box adder_1_example.
Definition adder_1_example_qasm := Eval compute in db_to_qasm_box adder_1_example_db.
Definition adder_1_example_string := Eval compute in printer adder_1_example_qasm.
Print adder_1_example_string.

Require Import Oracles.
Require Import Symmetric.

Ltac compute_compile :=
  repeat (try unfold compile; simpl;
          try unfold inPar; try unfold inSeq;
          try unfold id_circ; try unfold init_at; try unfold assert_at;
          try unfold Symmetric.CNOT_at).

Require Coq.derive.Derive.
Derive p SuchThat (adder_1_example = p) As h.
Proof.
  unfold adder_1_example. unfold adder_1_circ. unfold adder_circ_n.
  compute_compile. simpl_eq.
  compute_compile.

Close Scope circ_scope.
