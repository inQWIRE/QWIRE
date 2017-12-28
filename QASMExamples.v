Require Import QASM.
Require Import QASMPrinter.

(* QASMExamples.v - Examples of QASM circuits *)

(* Hadamard gate *)
Example h_decl : program := [s_gatedecl Hname (None) ([qname 1])
        ([g_uop (u_U [e_binop e_pi div (e_nat 2); e_nat 0; e_pi] (a_id (qname 1)))])].
Print h_decl.

(* coin_flip *)
Example coin_flip : program := app h_decl
                               [s_decl (creg (cname 1) 1); s_decl (qreg (qname 1) 1);
                               s_qop (q_uop (u_app Hname ([a_id (qname 1)])));
                               s_qop (q_meas (a_id (qname 1)) (a_id (cname 1)))].
Eval compute in coin_flip.

Eval compute in printer coin_flip.

Check app h_decl
      [s_decl (creg (cname 1) 1); s_decl (qreg (qname 1) 1);
         s_qop (q_uop (u_app Hname ([a_id (qname 1)])));
         s_qop (q_meas (a_id (qname 1)) (a_id (cname 1)))].

(* Min to QASM Examples *)
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import FlatCircuits.
Require Import Contexts.
Open Scope circ_scope.
Eval compute in fresh_pat (Bit ⊗ Bit ⊗ Qubit) 0.
Eval compute in fresh_pat ((Qubit ⊗ One) ⊗ (Bit ⊗ Qubit)) 0.
(* 1. Unitary example *)
Definition min_to_qasm_ex1_hoas : Box :=
  box_ () ⇒
    gate_ x    ← init0 @();
    gate_ x    ← H @x;
    gate_ y    ← init1 @();
    gate_ y    ← H @y;
    output (x, y).
Definition min_to_qasm_ex1_flat := hoas_to_flat_box min_to_qasm_ex1_hoas One.
Definition min_to_qasm_ex1_min := hoas_to_min_box min_to_qasm_ex1_hoas One.
(* Definition min_to_qasm_ex1_qasm := min_to_qasm_box min_to_qasm_ex1_min. *)
Eval compute in min_to_qasm_ex1_flat.
Eval compute in min_to_qasm_ex1_min.
(* Eval compute in printer (min_to_qasm (min_to_qasm_ex1_min) [] 0). *)
(* 2. Init example *)
Definition min_to_qasm_ex2_hoas : Box :=
  box_ () ⇒
    gate_ x    ← init0 @();
    gate_ y    ← init1 @();
    output ().
Definition min_to_qasm_ex2_flat := hoas_to_flat_box min_to_qasm_ex2_hoas One.
Definition min_to_qasm_ex2_min := hoas_to_min_box min_to_qasm_ex2_hoas One.
Eval compute in min_to_qasm_ex2_flat.
Eval compute in min_to_qasm_ex2_min.
(* 3. New example *)
Definition min_to_qasm_ex3_hoas : Box :=
  box_ () ⇒
    gate_ x    ← new0 @();
    gate_ y    ← new1 @();
    output ().
Definition min_to_qasm_ex3_flat := hoas_to_flat_box min_to_qasm_ex3_hoas One.
Definition min_to_qasm_ex3_min := hoas_to_min_box min_to_qasm_ex3_hoas One.
Eval compute in min_to_qasm_ex3_flat.
Eval compute in min_to_qasm_ex3_min.
(* 4. Measure example *)
Definition min_to_qasm_ex4_hoas : Box :=
  box_ () ⇒
    gate_ x ← init0 @();
    gate_ x ← H @x;
    gate_ y ← init1 @();
    gate_ y ← H @y;
    gate_ y ← meas @y;
    gate_ x ← meas @x;
    output (x, y).
Definition min_to_qasm_ex4_flat := hoas_to_flat_box min_to_qasm_ex4_hoas One.
Definition min_to_qasm_ex4_min := hoas_to_min_box min_to_qasm_ex4_hoas One.
Eval compute in min_to_qasm_ex4_flat.
Eval compute in min_to_qasm_ex4_min.
(* 5. Discard example *)
Definition min_to_qasm_ex5_hoas : Box :=
  box_ () ⇒
    gate_ x ← init0 @();
    gate_ x ← H @x;
    gate_ y ← init1 @();
    gate_ y ← H @y;
    gate_ () ← discard @y;
    gate_ x ← meas @x;
    output x.
Definition min_to_qasm_ex5_flat := hoas_to_flat_box min_to_qasm_ex5_hoas One.
Definition min_to_qasm_ex5_min := hoas_to_min_box min_to_qasm_ex5_hoas One.
Eval compute in min_to_qasm_ex5_flat.
Eval compute in min_to_qasm_ex5_min.
Definition min_to_qasm_ex5'_hoas : Box :=
  box_ () ⇒
    gate_ x ← init0 @();
    gate_ x ← H @x;
    gate_ y ← init1 @();
    gate_ y ← H @y;
    gate_ () ← discard @x;
    gate_ y ← meas @y;
    output y.
Definition min_to_qasm_ex5'_flat := hoas_to_flat_box min_to_qasm_ex5'_hoas One.
Definition min_to_qasm_ex5'_min := hoas_to_min_box min_to_qasm_ex5'_hoas One.
Eval compute in min_to_qasm_ex5'_flat.
Eval compute in min_to_qasm_ex5'_min.
(* 6. Lift example *)
Definition min_to_qasm_ex6_hoas : Box :=
  box_ () ⇒
    gate_ x    ← init0 @();
    gate_ x    ← H @x;
    gate_ y    ← init1 @();
    gate_ y    ← H @y;
    lift_ _    ← y;
    gate_ x    ← meas @x;
    output (x, y).
Definition min_to_qasm_ex6_flat := hoas_to_flat_box min_to_qasm_ex6_hoas One.
Definition min_to_qasm_ex6_min := hoas_to_min_box min_to_qasm_ex6_hoas One.
Eval compute in min_to_qasm_ex6_flat.
Eval compute in min_to_qasm_ex6_min.
Definition min_to_qasm_ex6'_hoas : Box :=
  box_ xyb ⇒
    let_ (xy, b) ← output xyb; 
    lift_ (u,v)  ← xy;
    gate_ b      ← (if v then σx else id_gate) @b;
    gate_ b      ← (if u then σz else id_gate) @b;
    output b.
Definition min_to_qasm_ex6'_flat := hoas_to_flat_box min_to_qasm_ex6'_hoas (Bit ⊗ Bit ⊗ Qubit).
Definition min_to_qasm_ex6'_min := hoas_to_min_box min_to_qasm_ex6'_hoas (Bit ⊗ Bit ⊗ Qubit).
Eval compute in min_to_qasm_ex6'_flat.
Eval compute in min_to_qasm_ex6'_min.
Close Scope circ_scope.
