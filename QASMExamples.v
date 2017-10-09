Require Import QASM.

(* QASMExamples.v - Examples of QASM circuits *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* naming function for qregs *)
Definition qname : nat -> nat := fun x => 3*x.
(* naming function for cregs *)
Definition cname : nat -> nat := fun x => 3*x - 1.
(* naming function for gates *)
Definition gname : nat -> nat := fun x => 3*x - 2.

(* Hadamard gate *)
Example h : program := [s_gatedecl (gname 1) (Some [qname 1]) ([])
        ([g_uop (u_U [e_binop e_pi div (e_real 2); e_real 0; e_pi] (a_id (qname 1)))])].

(* coin_flip *)
Example coin_flip : program := [s_decl (creg (cname 1) 1); s_decl (qreg (qname 1) 1);
                               s_gatedecl (gname 1) (Some [qname 1]) ([])
               ([g_uop (u_U [e_binop e_pi div (e_real 2); e_real 0; e_pi] (a_id (qname 1)))]);
                               s_qop (q_uop (u_app (gname 1) ([a_id (qname 1)])));
                               s_qop (q_meas (a_id (qname 1)) (a_id (cname 1)))].
