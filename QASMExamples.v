Require Import Reals.
Require Import String.
Require Import Ascii.
Require Import List.
Require Import QASM.
Require Import QASMFunctionsToString.
Require Import QASMPrinter.

(* QASMExamples.v - Examples of QASM circuits *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* naming function for qregs *)
Definition qname : nat -> id := fun x => String (ascii_of_nat 113) (string_of_nat x).
(* naming function for cregs *)
Definition cname : nat -> id := fun x => String (ascii_of_nat 99) (string_of_nat x).
(* naming function for gates *)
Definition gname : nat -> id := fun x => String (ascii_of_nat 103) (string_of_nat x).

(* name of Hadamard gate *)
Definition Hname : id := "gH"%string.

(* Hadamard gate *)
Example h_decl : program := [s_gatedecl Hname (None) ([qname 1])
        ([g_uop (u_U [e_binop e_pi div (e_real 2); e_real 0; e_pi] (a_id (qname 1)))])].
Print h_decl.

(* coin_flip *)
Example coin_flip : program := app h_decl
                               [s_decl (creg (cname 1) 1); s_decl (qreg (qname 1) 1);
                               s_qop (q_uop (u_app Hname ([a_id (qname 1)])));
                               s_qop (q_meas (a_id (qname 1)) (a_id (cname 1)))].
Eval compute in coin_flip.

Eval compute in printer coin_flip.