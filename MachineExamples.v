Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import Contexts.
Require Import HOASCircuits.
Require Import MachineCircuits.
Require Import Omega.
Import ListNotations.
Open Scope list_scope.


(*** Paper Examples ***)

(* Infix "↦" := m_box (at level 12, left associativity). *)
Notation "'gate' g 'on' l ; C" := (m_gate l g C) (at level 10, right associativity).
Notation "# l " := (length l) (at level 0).

Notation out l := (m_output l). 
Open Scope circ_scope.


(* Basic Circuits *)

Definition id_circ l : Machine_Circuit #l #l := out l.

Definition new_discard : Machine_Circuit 0 0 := 
  gate new0 on [];
  gate discard on [0];
  out [].

Definition init_discard : Machine_Circuit 0 0 :=
  gate init0 on [];
  gate meas on [0];
  gate discard on [0];
  out [].

Definition hadamard_measure : Machine_Circuit 1 1 :=
  gate H on [0];
  gate meas on [0];
  out [0].


(* Repeated Unitaries *)

Definition repeat_hadamard : Machine_Circuit 1 1 :=
  gate H on [0];
  gate H on [0];
  out [0].

Definition U_U_trans_qubit (U : Unitary Qubit): Machine_Circuit 1 1 :=
  gate U on [0];
  gate (transpose U) on [0];
  out [0].

Definition U_U_trans {W} (U : Unitary W): Machine_Circuit (size_WType W) (size_WType W) :=
  let l := seq 0 (size_WType W) in  
  gate U on l;
  gate (transpose U) on l;
  out l.


(* Deutsch's Algorithm *)

Parameter U_f : Unitary (Qubit ⊗ Qubit).
Definition deutsch : Machine_Circuit 0 1 :=
  gate init0 on [];
  gate H on [0];
  gate init1 on [];
  gate H on [1];
  gate U_f on [0;1];
  gate meas on [0];
  gate discard on [0];
  out [1].


(* Teleport *)

Definition init (b : bool) : Machine_Circuit 0 1:=
  if b then (gate init1 on []; out [0]) 
       else (gate init0 on []; out [0]).

(** Teleport **)

Definition bell00 : Machine_Circuit 0 2 :=
  gate init0 on [];
  gate init0 on [];
  gate H on [0];
  gate CNOT on [0;1];
  out [0;1].

Definition alice : Machine_Circuit 2 2 :=
  gate CNOT on [0;1];
  gate H on [0];
  gate meas on [0];
  gate meas on [1];
  out [0;1].

Definition bob : Machine_Circuit 3 1 :=
  gate (bit_ctrl σx) on [1;2];
  gate (bit_ctrl σz) on [0;2];
  gate discard on [1];
  gate discard on [0]; 
  out [2].

Definition teleport : Machine_Circuit 1 1 :=
  (* bell00 *) (* shifted from above *)
  gate init0 on [];
  gate init0 on [];
  gate H on [1];
  gate CNOT on [1;2];
  
  (* alice *)
  gate CNOT on [0;1];
  gate H on [0];
  gate meas on [0];
  gate meas on [1];

  (* bob *)  
  gate (bit_ctrl σx) on [1;2];
  gate (bit_ctrl σz) on [0;2];
  gate discard on [1];
  gate discard on [0]; 
  out [0].


(* Coin Flip *)

Definition coin_flip : Machine_Circuit 0 1 :=
  gate init0 on [];
  gate H on [0];
  gate meas on [0];
  out [0].


(* Old teleport for IO-less circuits.
Definition teleport : Machine_Circuit := bell00 ↦ alice ↦ bob.

Print teleport.
Eval compute in teleport.
*)

Close Scope circ_scope.

(* *)
