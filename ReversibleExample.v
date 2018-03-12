Require Import HOASExamples.
Require Import TypeChecking.
Require Import Reversible.

Open Scope circ_scope.

(*
Input : var 0 : cin
        var 1 : x
        var 2 : y
Output : cout = cin(x \xor y) \xor xy
         z = cin \xor (x \xor y)
 *)
Definition adder_cout_rbexp : rbexp :=
  rb_xor (rb_and (rb_var 0%nat) (rb_xor (rb_var 1%nat) (rb_var 2%nat))) (rb_and (rb_var 1%nat) (rb_var 2%nat)).

Definition adder_z_rbexp : rbexp :=
  rb_xor (rb_var 0%nat) (rb_xor (rb_var 1%nat) (rb_var 2%nat)).

Fixpoint list_of_Qubits (n : nat) : Ctx :=
  match n with
  | 0 => []
  | S n' => (Some Qubit) :: (list_of_Qubits n')
  end.

Definition adder_cout_circ :=
  compile adder_cout_rbexp (list_of_Qubits 3).

Definition adder_z_circ :=
  compile adder_z_rbexp (list_of_Qubits 3).

(*
Eval compute in (S (⟦ list_of_Qubits 3 ⟧) ⨂ Qubit).
Check (qubit 0%nat, (qubit 1%nat, (qubit 2%nat, (qubit 3%nat, unit)))).
Eval simple in (adder_cout_circ (qubit 0%nat, (qubit 1%nat, (qubit 2%nat, qubit 3%nat)))).
*)

(* n_adder_circ : returns a boxed circuit that adds two n-bit inputs
   example : (n_adder_circ 3) (y3, (y2, (y1, (x3, (x2, (x1, cin)))))) returns
             (cout, (z3, (z2, z1))) where (y3y2y1) + (x3x2x1) = (z3z2z1) in base 2.
 *)
Locate "⨂".
Definition zn := qubit 3%nat.
Definition yn := qubit 2%nat.
Definition xn := qubit 1%nat.
Definition cin := qubit 0%nat.
Check pair zn (pair yn (pair xn (pair cin unit))).
Definition adder_circ_1 : Box (5 ⨂ Qubit) (5 ⨂ Qubit) :=
  box_ inp ⇒
    let_ (coutn, (zn, inp')) ← output inp;
    let_ (yn, (xn, inp'')) ← output inp';
    let_ out'' ← unbox (id_circ) inp'';
    let_ (coutn', out''') ← output out'';
    let_ (zn', zout) ← unbox adder_z_circ (pair zn (pair yn (pair xn (pair coutn' unit))));
    let_ (coutn', (yn', tmp)) ← unbox adder_cout_circ (coutn, zout);
    let_ (xn', (coutn'', dummy)) ← tmp;
    output (pair coutn' (pair zn' (pair yn' (pair xn' (pair coutn'' out'''))))).
Check adder_circ_1.
Print adder_circ_1.

Definition adder_circ_2 : Box (9 ⨂ Qubit) (9 ⨂ Qubit) :=
  box_ inp ⇒
    let_ (coutn, (zn, inp')) ← output inp;
    let_ (yn, (xn, inp'')) ← output inp';
    let_ out'' ← unbox (adder_circ_1) inp'';
    let_ (coutn', out''') ← output out'';
    let_ (zn', zout) ← unbox adder_z_circ (pair zn (pair yn (pair xn (pair coutn' unit))));
    let_ (coutn', (yn', tmp)) ← unbox adder_cout_circ (coutn, zout);
    let_ (xn', (coutn'', dummy)) ← tmp;
    output (pair coutn' (pair zn' (pair yn' (pair xn' (pair coutn'' out'''))))).
Check adder_circ_2.
Print adder_circ_2.

Definition adder_circ_3 : Box (13 ⨂ Qubit) (13 ⨂ Qubit) :=
  box_ inp ⇒
    let_ (coutn, (zn, inp')) ← output inp;
    let_ (yn, (xn, inp'')) ← output inp';
    let_ out'' ← unbox (adder_circ_2) inp'';
    let_ (coutn', out''') ← output out'';
    let_ (zn', zout) ← unbox adder_z_circ (pair zn (pair yn (pair xn (pair coutn' unit))));
    let_ (coutn', (yn', tmp)) ← unbox adder_cout_circ (coutn, zout);
    let_ (xn', (coutn'', dummy)) ← tmp;
    output (pair coutn' (pair zn' (pair yn' (pair xn' (pair coutn'' out'''))))).
Check adder_circ_3.
Eval compute in adder_circ_3.

Program Fixpoint n_adder_circ (n : nat) : Box ((1+n+n+n+n) ⨂ Qubit) ((1+n+n+n+n) ⨂ Qubit) :=
  match n with
  | 0 => box_ inp ⇒ (output inp)
  | S n' => box_ inp ⇒
           let_ (coutn, (zn, inp')) ← output inp;
           let_ (yn, (xn, inp'')) ← output inp';
           let_ out'' ← unbox (n_adder_circ n') inp'';
           let_ (coutn', out''') ← output out'';
           let_ (zn', zout) ← unbox adder_z_circ (pair zn (pair yn (pair xn (pair coutn' unit))));
           let_ (coutn', (yn', tmp)) ← unbox adder_cout_circ (coutn, zout);
           let_ (xn', (coutn'', dummy)) ← tmp;
           output (pair coutn' (pair zn' (pair yn' (pair xn' (pair coutn'' out''')))))
  end.
Next Obligation.
  fold NTensor.
  fold Init.Nat.add.
  replace (n' + S n' + S n' + S n')%nat with
      (S (S (S (n' + n' + n' + n')%nat))) by omega.
  reflexivity.
Defined.
Next Obligation.
  fold NTensor.
  fold Init.Nat.add.
  replace (n' + S n' + S n' + S n')%nat with
      (S (S (S (n' + n' + n' + n')%nat))) by omega.
  reflexivity.
Defined.

Eval simpl in (n_adder_circ 1).
Eval simpl in (n_adder_circ 2).
Eval simpl in (n_adder_circ 3).
Eval compute in n_adder_circ 1.