Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import Contexts.
Require Import TypedCircuits.
Require Import MachineCircuits.
Import ListNotations.
Open Scope list_scope.


(*** Paper Examples ***)

Infix "↦" := m_input (at level 12, left associativity). 
Notation "'gate' g 'on' l ; C" := (m_gate l _ g C) (at level 10, right associativity).
Notation "# l " := (length l) (at level 0).

Notation In l c := (m_input l c). 
Notation out l := (m_output l). 


(* Basic Circuits *)

Definition id_circ l : Machine_Circuit #l #l := l ↦ out l.

Program Definition new_discard : Machine_Circuit 0 0 := 
  [] ↦ 
  gate new0 on [];
  gate discard on [0];
  out [].

Program Definition init_discard : Machine_Circuit 0 0 :=
  [] ↦ 
  gate init0 on [];
  gate meas on [0];
  gate discard on [0];
  out [].

Program Definition hadamard_measure : Machine_Circuit 1 1 :=
  [0] ↦
  gate H on [0];
  gate meas on [0];
  out [0].


(* Repeated Unitaries *)

Program Definition repeat_hadamard : Machine_Circuit 1 1 :=
  [0] ↦
  gate H on [0];
  gate H on [0];
  out [0].

Program Definition U_U_trans_qubit (U : Unitary Qubit): Machine_Circuit 1 1 :=
  [0] ↦
  gate U on [0];
  gate (transpose U) on [0];
  out [0].

Program Definition U_U_trans {W} (U : Unitary W): 
  Machine_Circuit (num_wires W) (num_wires W) :=
  let l := seq 0 (num_wires W) in  
  l ↦
  gate U on l;
  gate (transpose U) on l;
  out l.
Next Obligation. apply seq_length. Defined.
Next Obligation. apply seq_length. Defined.
Next Obligation. apply seq_length. Defined.
Next Obligation. apply seq_length. Defined.


(* Deutch's Algorithm *)

Parameter U_f : Unitary (Qubit ⊗ Qubit).
Program Definition deutsch : Machine_Circuit 0 1 :=
  [] ↦ 
  gate init0 on [];
  gate H on [0];
  gate init1 on [];
  gate H on [1];
  gate U_f on [0;1];
  gate meas on [0];
  gate discard on [0];
  out [1].


(* Teleport *)

Program Definition init (b : bool) : Machine_Circuit 0 1:=
  if b then ([] ↦ gate init1 on []; out [0]) 
       else ([] ↦ gate init0 on []; out [0]).

(** Teleport **)

Program Definition bell00 : Machine_Circuit 0 2 :=
  [] ↦ 
  gate init0 on [];
  gate init0 on [];
  gate H on [1];
  gate CNOT on [1;2];
  out [1;2].

Program Definition alice : Machine_Circuit 2 2 :=
  [0;1] ↦ 
  gate CNOT on [0;1];
  gate H on [0];
  gate meas on [0];
  gate meas on [1];
  out [0;1].

Program Definition bob : Machine_Circuit 3 1 :=
  [0;1;2] ↦
  gate (bit_control σx) on [1;2];
  gate (bit_control σz) on [0;2];
  gate discard on [1];
  gate discard on [0]; 
  out [2].

Program Definition teleport : Machine_Circuit 1 1 :=
  [0] ↦
  (* bell00 *)
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
  gate (bit_control σx) on [1;2];
  gate (bit_control σz) on [0;2];
  gate discard on [1];
  gate discard on [0]; 
  out [2].


(* Coin Flip *)

Program Definition coin_flip : Machine_Circuit 0 1 :=
  [] ↦
  gate init0 on [];
  gate H on [0];
  gate meas on [0];
  out [0].


(* Old teleport for IO-less circuits.
Definition teleport : Machine_Circuit := bell00 ↦ alice ↦ bob.

Print teleport.
Eval compute in teleport.
*)

(* *)
