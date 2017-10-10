Require Import QASM.
Require Import String.
Require Import Ascii.

(* QASMExamples.v - Examples of QASM circuits *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* auxiliary recursive function for successor of string representing nat *)
Fixpoint string_rS (s : string) : prod nat string :=
  match s with
  | EmptyString => (1, EmptyString)
  | String a ns => 
    match (nat_of_ascii a) with
    | 57 => let (c, ns_S) := (string_rS ns) in
                           match c with
                           | 1 => pair 1 (String (ascii_of_nat 48) ns_S)
                           | _ => pair 0 (String (ascii_of_nat ((nat_of_ascii a) + c)) ns_S)
                           end
    | _ => let (c, ns_S) := (string_rS ns) in
           pair 0 (String (ascii_of_nat ((nat_of_ascii a) + c)) ns_S)
    end
  end.
Example string_rS_test := string_rS EmptyString.
Eval compute in string_rS_test.
Example string_rS_test2 := string_rS (String (ascii_of_nat 57) EmptyString).
Eval compute in string_rS_test2.
(* successor function for string representing nat *)
Fixpoint string_S (s : string) : string :=
  let ns_S := (string_rS s) in match ns_S with
                                | (1, s') => String (ascii_of_nat 49) s'
                                | (_, s') => s'
                                end.
Example string_S_test := string_S EmptyString.
Eval compute in string_S_test.
Example string_S_test2 := string_S (String (ascii_of_nat 57) EmptyString).
Eval compute in string_S_test2.
(* conversion function from nat to string *)
Fixpoint string_of_nat (n : nat) : string :=
  match n with
  | 0 => String (ascii_of_nat 48) EmptyString
  | S n' => string_S (string_of_nat n')
  end.
Example string_of_3 := string_of_nat 3.
Eval compute in string_of_3.
Example string_of_9 := string_of_nat 9.
Eval compute in string_of_9.
Example string_of_10 := string_of_nat 10.
Eval compute in string_of_10.
Example string_of_11 := string_of_nat 11.
Eval compute in string_of_11.
(* naming function for qregs *)
Definition qname : nat -> id := fun x => String (ascii_of_nat 113) (string_of_nat x).
(* naming function for cregs *)
Definition cname : nat -> id := fun x => String (ascii_of_nat 99) (string_of_nat x).
(* naming function for gates *)
Definition gname : nat -> id := fun x => String (ascii_of_nat 103) (string_of_nat x).

(* name of Hadamard gate *)
Definition Hname : id := "gH"%string.

(* Hadamard gate *)
Example h : program := [s_gatedecl (gname 1) (Some [qname 1]) ([])
        ([g_uop (u_U [e_binop e_pi div (e_real 2); e_real 0; e_pi] (a_id (qname 1)))])].

(* coin_flip *)
Example coin_flip : program := [s_decl (creg (cname 1) 1); s_decl (qreg (qname 1) 1);
                               s_gatedecl (gname 1) (Some [qname 1]) ([])
               ([g_uop (u_U [e_binop e_pi div (e_real 2); e_real 0; e_pi] (a_id (qname 1)))]);
                               s_qop (q_uop (u_app (gname 1) ([a_id (qname 1)])));
                               s_qop (q_meas (a_id (qname 1)) (a_id (cname 1)))].
