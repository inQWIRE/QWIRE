Require Import Reals.
Require Import String.
Require Import FlatCircuits.

(* QASM.v - representation of QASM circuits *)

Definition id := string.

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
| s_output (args:anylist)
.            

Definition program := list statement.

(** Convert from Minimal Circuits to QASM **)
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import FlatCircuits.
Require Import Contexts.
Require Import List.
Require Import Arith.
Require Import Reals.

Open Scope circ_scope.
Open Scope R_scope.

(*
// 1-parameter 0-pulse single qubit gate
gate u1(lambda) q { U(0,0,lambda) q; }
// controlled-U
gate cu3(theta,phi,lambda) c, t
{
  // implements controlled-U(theta,phi,lambda) with  target t and control c
  u1((lambda-phi)/2) t;
  cx c,t;
  u3(-theta/2,0,-(phi+lambda)/2) t;
  cx c,t;
  u3(theta/2,phi,0) t;
}

// 1-parameter 0-pulse single qubit gate
gate u1(lambda) q { U(0,0,lambda) q; }
// C3 gate: sqrt(S) phase gate
gate t a { u1(pi/4) a; }
// C3 gate: conjugate of sqrt(S)
gate tdg a { u1(-pi/4) a; }
// C3 gate: Toffoli
gate ccx a,b,c
{
  h c;
  cx b,c; tdg c;
  cx a,c; t c;
  cx b,c; tdg c;
  cx a,c; t b;
  t c; h c;
  cx a,b; t a; 
  tdg b;
  cx a,b;
}
*)
Fixpoint control_unitary_gate_circuit (cp : Pat) (C : Min_Circuit) : Min_Circuit :=
  match C with
  | min_gate g p C' =>
    match g with
    | (U u) =>
      match u with
      | ROT3 th ph la =>
        match cp with
        | c =>
          match p with
          | t =>
            min_gate (U (ROT3 0 0 ((la-ph)/2))) t
            (min_gate (U CNOT) (pair c t)
            (min_gate (U (ROT3 (-th/2) 0 (-(ph+la)/2))) t
            (min_gate (U CNOT) (pair c t)
            (min_gate (U (ROT3 (th/2) ph 0)) t
            (control_unitary_gate_circuit cp C')))))
          end
        end
      | CNOT => match p with
                | pair b c =>
                  match cp with
                  | a =>
                  min_gate (U (ROT3 (PI/2) 0 PI)) c
                  (min_gate (U CNOT) (pair b c) (min_gate (U (ROT3 0 0 (-PI/4))) c
                  (min_gate (U CNOT) (pair a c) (min_gate (U (ROT3 0 0 (PI/4))) c
                  (min_gate (U CNOT) (pair b c) (min_gate (U (ROT3 0 0 (-PI/4))) c
                  (min_gate (U CNOT) (pair a c) (min_gate (U (ROT3 0 0 (PI/4))) b
                  (min_gate (U (ROT3 0 0 (PI/4))) c (min_gate (U (ROT3 (PI/2) 0 PI)) c
                  (min_gate (U CNOT) (pair a b) (min_gate (U (ROT3 0 0 (PI/4))) a
                  (min_gate (U (ROT3 0 0 (-PI/4))) b
                  (min_gate (U CNOT) (pair a b)
                  (control_unitary_gate_circuit cp C')))))))))))))))
                  end
                | _ => (control_unitary_gate_circuit cp C')
                end
      | _ => (control_unitary_gate_circuit cp C')
      end
    | _ => (control_unitary_gate_circuit cp C')
    end
  | min_output p => min_output p
  | min_lift p f =>
    min_lift p (fun b => match b with
                         | true => (control_unitary_gate_circuit cp (f true))
                         | flase => (control_unitary_gate_circuit cp (f false))
                         end)
  end.

Fixpoint append_gate_last {W} (nu : Unitary W) (np : Pat) (c : Min_Circuit) : Min_Circuit :=
  match c with
  | min_output p => min_gate (U nu) np (min_output p)
  | min_gate g p c' => min_gate g p (append_gate_last nu np c')
  | min_lift p f =>
    min_lift p (fun b => match b with
                         | true => (append_gate_last nu np (f true))
                         | flase => (append_gate_last nu np (f false))
                         end)
  end.

Fixpoint transpose_unitary_gate_circuit (c : Min_Circuit) : Min_Circuit :=
  match c with
  | min_output p => min_output p
  | min_gate g p c' =>
    match g with
      | U u =>
        match u with
        | ROT3 th ph la =>
          append_gate_last (ROT3 (-th) (-ph) (-la)) p (transpose_unitary_gate_circuit c')
        | CNOT =>
          append_gate_last (CNOT) p (transpose_unitary_gate_circuit c')
        | _ => (transpose_unitary_gate_circuit c')
        end
      | _ => (transpose_unitary_gate_circuit c')
    end
  | min_lift p f =>
    min_lift p (fun b => match b with
                         | true => (transpose_unitary_gate_circuit (f true))
                         | false => (transpose_unitary_gate_circuit (f false))
                         end)
  end.

Fixpoint unitary_gate_translation {W} (u : Unitary W) (p po : Pat) : Min_Circuit :=
  match u with
    | H => min_gate (U (ROT3 (PI/2) 0 PI)) p (min_output po)
    | σx => min_gate (U (ROT3 PI 0 PI)) p (min_output po)
    | σy => min_gate (U (ROT3 PI (PI/2) (PI/2))) p (min_output po)
    | σz => min_gate (U (ROT3 0 0 PI)) p (min_output po)
    | CNOT => min_gate (U CNOT) p (min_output po)
    | ROT3 th ph la => min_gate (U (ROT3 th ph la)) p (min_output po)
    | ctrl u' =>
      match p with
      | pair p1 p2 =>
        control_unitary_gate_circuit p1 (unitary_gate_translation u' p2 po)
      | _ => unitary_gate_translation u' p po
      end
    | bit_ctrl u' => (min_output po)
    | transpose u' => transpose_unitary_gate_circuit (unitary_gate_translation u' p po)
  end.

(* Merge c1 into c2 *)
Fixpoint min_circuit_merge (c1 c2 : Min_Circuit) : Min_Circuit :=
  match c1 with
  | min_output p => c2
  | min_gate g p c' => min_gate g p (min_circuit_merge c' c2)
  | min_lift p f =>
    min_lift p (fun b => match b with
                         | true => (min_circuit_merge (f true) c2)
                         | false => (min_circuit_merge (f false) c2)
                         end)
  end.

Fixpoint min_circuit_translation_helper (c : Min_Circuit) : Min_Circuit :=
  match c with
  | min_output p => min_output p
  | min_gate g p c' =>
    match g with
    | U u =>
      min_circuit_merge (unitary_gate_translation u p p) (min_circuit_translation_helper c')
    | _   => min_gate g p (min_circuit_translation_helper c')
    end
  | min_lift p f =>
    min_lift p (fun b => match b with
                         | true => (min_circuit_translation_helper (f true))
                         | false => (min_circuit_translation_helper (f false))
                         end)
  end.

(* Min Circuit Translation Helper Examples *)

Eval simpl in (match (hoas_to_min_box bell00 One) with
               | min_box W C => min_circuit_translation_helper C
               end).
Eval simpl in (match (hoas_to_min_box alice (Qubit ⊗ Qubit)) with
               | min_box W C => min_circuit_translation_helper C
               end).
Eval simpl in (match (hoas_to_min_box bob (Bit ⊗ Bit ⊗ Qubit)) with
               | min_box W C => min_circuit_translation_helper C
               end).
Eval simpl in (match (hoas_to_min_box teleport Qubit) with
               | min_box W C => min_circuit_translation_helper C
               end).

Close Scope circ_scope.
