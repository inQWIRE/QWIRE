Require Import String.
Require Import Ascii.
Require Import QASM.

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
Example h_decl : program := [s_gatedecl Hname (None) ([qname 1])
        ([g_uop (u_U [e_binop e_pi div (e_real 2); e_real 0; e_pi] (a_id (qname 1)))])].
Print h_decl.

(* coin_flip *)
Example coin_flip : program := app h_decl
                               [s_decl (creg (cname 1) 1); s_decl (qreg (qname 1) 1);
                               s_qop (q_uop (u_app Hname ([a_id (qname 1)])));
                               s_qop (q_meas (a_id (qname 1)) (a_id (cname 1)))].
Eval compute in coin_flip.

(* Print function from program to QASM code *)
Definition newline := String (Ascii.ascii_of_N 10) EmptyString.
Definition print_binop (b : binop) : string :=
  match b with
  | plus => "+"
  | minus => "-"
  | times => "*"
  | div => "/"
  | pow => "^"
  end.
Definition print_unaryop (u : unaryop) : string :=
  match u with
  | sin => "sin"
  | cos => "cos"
  | tan => "tan"
  | e_to => "exp"
  | ln => "ln"
  | sqrt => "sqrt"
  | neg => "-"
  end.
Fixpoint print_exp (e : exp) : string :=
  match e with
  | e_real r => "" (* To implement *)
  | e_nat n => string_of_nat n
  | e_pi => "pi"
  | e_id name => name
  | e_binop e1 b e2 => " ( " ++ print_exp e1 ++ " " ++ print_binop b
                             ++ " " ++ print_exp e2 ++ " ) "
  | e_unop u e => " ( " ++ print_unaryop u ++ " " ++ print_exp e ++ " ) "
  end.

Definition print_argument (a : argument) : string :=
  match a with
  | a_id n => n
  | a_idx n i => n ++ " [ " ++ string_of_nat i ++ " ] "
  end.

Fixpoint print_idlist (args : idlist) : string :=
  match args with
  | nil => ""
  | h :: nil => h
  | h :: t => h ++ ", " ++ print_idlist t
  end.
Fixpoint print_explist (exps : explist) : string :=
  match exps with
  | nil => ""
  | h :: nil => print_exp h
  | h :: t => print_exp h ++ ", " ++ print_explist t
  end.
Fixpoint print_anylist (args : anylist) : string :=
  match args with
  | nil => ""
  | h :: nil => print_argument h
  | h :: t => print_argument h ++ ", " ++ print_anylist t
  end.

Definition print_args (args : option idlist) : string :=
  match args with
  | None => ""
  | Some arglist => print_idlist arglist
  end.

Definition print_uop (op : uop) : string :=
  match op with
  | u_U l a => "U ( " ++ print_explist l ++ " ) " ++ print_argument a ++ " ;" ++ newline
  | u_CX a1 a2 => "CX " ++ print_argument a1 ++ ", " ++ print_argument a2 ++ " ;" ++ newline
  | u_app i l => i ++ " ( ) " ++ print_anylist l ++ " ;" ++ newline
  | u_call i es l => i ++ " ( " ++ print_explist es ++ " ) "
                       ++ print_anylist l ++ " ;" ++ newline
  end.
Definition print_qop (op : qop) : string :=
  match op with
  | q_uop u => print_uop u
  | q_meas ain aout => "measure " ++ print_argument ain ++ " - > "
                                  ++ print_argument aout ++ " ;" ++ newline
  | q_reset a => "reset " ++ print_argument a ++ " ;" ++ newline
  end.
Definition print_gop (op : gop) : string :=
  match op with
  | g_uop u => print_uop u
  | g_barrier ids => "barrier " ++ print_idlist ids ++ " ;" ++ newline
  end.
Fixpoint print_goplist (gops : goplist) : string :=
  match gops with
  | nil => ""
  | h :: nil => print_gop h
  | h :: t => print_gop h ++ print_goplist t
  end.

Definition print_decl (d : decl) : string :=
  match d with
  | qreg name size => "qreg " ++ name ++ " [ " ++ string_of_nat size ++ " ] ;" ++ newline
  | creg name size => "creg " ++ name ++ " [ " ++ string_of_nat size ++ " ] ;" ++ newline
  end.
Definition print_gatedecl (name:id) (args:option idlist) (names:idlist) (body:goplist)
  : string := "gate " ++ name ++ " ( " ++ print_args args ++ " ) " ++ print_idlist names
                     ++ " { " ++ newline
                     ++ print_goplist body
                     ++ " } " ++ newline.

Fixpoint print_statement (s : statement) : string :=
  match s with
  | s_decl d => print_decl d
  | s_gatedecl name args names body => print_gatedecl name args names body
  | s_opaque name args names => "opaque " ++ name ++ " ( " ++ print_args args ++ " ) "
                                          ++ print_idlist names ++ " ;" ++ newline
  | s_qop q => print_qop q
  | s_if x n q => "if ( " ++ x ++ " == " ++ string_of_nat n ++ " ) " ++ print_qop q
  | s_barrier args => "barrier " ++ print_anylist args ++ " ;" ++ newline
  end.

Fixpoint printer (p : program) : string :=
  match p with
  | nil => ""
  | st :: p' => print_statement st ++ printer p'
  end.

Eval compute in printer coin_flip.