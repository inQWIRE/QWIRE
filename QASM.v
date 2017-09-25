Require Import Reals.

(* QASM.v - representation of QASM circuits *)

Definition id := nat.

Inductive binop : Set :=
| plus | minus 
| times | div
| pow
.
    
Inductive unaryop : Set :=
| sin
| cos
| tan | e_to | ln | sqrt
| neg
.

Inductive exp : Set :=
| e_real (r:R)
| e_nat (n:nat)
| e_pi
| e_id (name:id)
| e_binop (e1:exp) (b:binop) (e2:exp)
| e_unop (u:unaryop) (e:exp)
.         

Inductive argument : Set :=
| a_id (n:id)
| a_idx (n:id) (i:nat)
.

Definition idlist := list id.
Definition anylist := list argument.
Definition explist := list exp.

Inductive uop : Set :=
| u_U (l:explist) (a:argument)
| u_CX (a1 a2:argument)
| u_app (i:id) (l:anylist)
| u_call (i:id) (es:explist) (l:anylist)
.

Inductive qop : Set :=
| q_uop (u:uop)
| q_meas (ain: argument) (aout: argument)
| q_reset (a:argument)
.          

Inductive gop : Set :=
| g_uop (u:uop)
| g_barrier (ids:idlist)
.

Definition goplist := list gop.  (* Nonempty? *)

Inductive decl : Set :=
| qreg (name:id) (size:nat)
| creg (name:id) (size:nat)
.

(*
gatedecl 
gate FOO ( ... ) <...> { ... } 
*)
Inductive statement : Set :=
| s_decl (d:decl)  
  (* TODO: what is the difference between args and names? are those the right terminology? *)
| s_gatedecl (name:id) (args:option idlist) (names:idlist) (body:goplist)
| s_opaque (name:id) (args:option idlist) (names:idlist)
| s_qop (q:qop)
| s_if (x:id) (n:nat) (q:qop)
| s_barrier (args:anylist)
.            

Definition program := list statement.


