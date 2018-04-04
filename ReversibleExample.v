Require Import HOASExamples.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import Reversible.
Require Import Matrix.
Require Import Denotation.
Require Import Monad.

Require Import List.
Import ListNotations.

Open Scope circ_scope.

(*
Input : var 0 : cin
        var 1 : x
        var 2 : y
Output : cout = cin(x ⊕ y) ⊕ xy
         z = cin ⊕ (x ⊕ y)
 *)
Open Scope rbexp_scope.
Definition adder_cout_rbexp : rbexp :=
  rb_xor (rb_and (rb_var 0%nat) (rb_xor (rb_var 1%nat) (rb_var 2%nat))) (rb_and (rb_var 1%nat) (rb_var 2%nat)).

Definition adder_z_rbexp : rbexp :=
  rb_xor (rb_var 0%nat) (rb_xor (rb_var 1%nat) (rb_var 2%nat)).

Definition xor_rbexp : rbexp :=
  rb_xor (rb_var 0%nat) (rb_var 1%nat).

Definition list_to_function {A} (l : list A) (d : A) := 
  fun (n : nat) => nth n l d.

Lemma test_adder_cout_rbexp_000 : 
⌈ adder_cout_rbexp | list_to_function [false; false; false] false ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_rbexp_001 : 
⌈ adder_cout_rbexp | list_to_function [false; false; true] false ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_rbexp_010 : 
⌈ adder_cout_rbexp | list_to_function [false; true; false] false ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_rbexp_011 : 
⌈ adder_cout_rbexp | list_to_function [false; true; true] false ⌉ = true.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_rbexp_100 : 
⌈ adder_cout_rbexp | list_to_function [true; false; false] false ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_rbexp_101 : 
⌈ adder_cout_rbexp | list_to_function [true; false; true] false ⌉ = true.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_rbexp_110 : 
⌈ adder_cout_rbexp | list_to_function [true; true; false] false ⌉ = true.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_rbexp_111 : 
⌈ adder_cout_rbexp | list_to_function [true; true; true] false ⌉ = true.
Proof. simpl. reflexivity. Qed.

Lemma test_adder_z_rbexp_000 : 
⌈ adder_z_rbexp | list_to_function [false; false; false] false ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_rbexp_001 : 
⌈ adder_z_rbexp | list_to_function [false; false; true] false ⌉ = true.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_rbexp_010 : 
⌈ adder_z_rbexp | list_to_function [false; true; false] false ⌉ = true.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_rbexp_011 : 
⌈ adder_z_rbexp | list_to_function [false; true; true] false ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_rbexp_100 : 
⌈ adder_z_rbexp | list_to_function [true; false; false] false ⌉ = true.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_rbexp_101 : 
⌈ adder_z_rbexp | list_to_function [true; false; true] false ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_rbexp_110 : 
⌈ adder_z_rbexp | list_to_function [true; true; false] false ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_rbexp_111 : 
⌈ adder_z_rbexp | list_to_function [true; true; true] false ⌉ = true.
Proof. simpl. reflexivity. Qed.
Close Scope rbexp_scope.


Fixpoint list_of_Qubits (n : nat) : Ctx :=
  match n with
  | 0 => []
  | S n' => (Some Qubit) :: (list_of_Qubits n')
  end.

Definition adder_cout_circ :=
  compile adder_cout_rbexp [Some Qubit; Some Qubit; Some Qubit].
Eval compute in adder_cout_circ.

Definition adder_z_circ :=
  compile adder_z_rbexp [Some Qubit; Some Qubit; Some Qubit].

Definition xor_circ :=
  compile xor_rbexp (list_of_Qubits 2).

Open Scope matrix_scope.
Lemma adder_cout_circ_spec : forall (x y z r : bool),
⟦adder_cout_circ⟧ ((ctx_to_matrix [Some Qubit; Some Qubit; Some Qubit] (list_to_function [x; y; z] false)) ⊗ (bool_to_matrix r))
= (ctx_to_matrix [Some Qubit; Some Qubit; Some Qubit] (list_to_function [x; y; z] false)) ⊗ 
(bool_to_matrix (r ⊕ ⌈ adder_cout_rbexp | list_to_function [x; y; z] false ⌉)).
Proof.
intros.
apply (compile_correct adder_cout_rbexp [Some Qubit; Some Qubit; Some Qubit] (list_to_function [x; y; z] false) r).
apply (sub_some Qubit [Some Qubit; Some Qubit]).
Qed.

Lemma adder_z_circ_spec : forall (x y z r : bool),
⟦adder_z_circ⟧ ((ctx_to_matrix [Some Qubit; Some Qubit; Some Qubit] (list_to_function [x; y; z] false)) ⊗ (bool_to_matrix r))
= (ctx_to_matrix [Some Qubit; Some Qubit; Some Qubit] (list_to_function [x; y; z] false)) ⊗ 
(bool_to_matrix (r ⊕ ⌈ adder_z_rbexp | list_to_function [x; y; z] false ⌉)).
Proof.
intros.
apply (compile_correct adder_z_rbexp [Some Qubit; Some Qubit; Some Qubit] (list_to_function [x; y; z] false) r).
apply (sub_some Qubit [Some Qubit; Some Qubit]).
Qed.

Lemma xor_circ_spec : forall (x y r : bool),
⟦xor_circ⟧ ((ctx_to_matrix [Some Qubit; Some Qubit] (list_to_function [x; y] false)) ⊗ (bool_to_matrix r))
= (ctx_to_matrix [Some Qubit; Some Qubit] (list_to_function [x; y] false)) ⊗ 
(bool_to_matrix (r ⊕ ⌈ xor_rbexp | list_to_function [x; y] false ⌉)).
Proof.
intros.
apply (compile_correct xor_rbexp [Some Qubit; Some Qubit] (list_to_function [x; y] false) r).
apply (sub_some Qubit [Some Qubit]).
Qed.

(* Proof of specification using matrix_denote : failed
Lemma xor_circ_spec_matrix : forall (x y z : bool),
  ⟦xor_circ⟧ ((bool_to_matrix x) ⊗ (bool_to_matrix y) ⊗ (bool_to_matrix z))
  = ((bool_to_matrix x) ⊗ (bool_to_matrix y) ⊗ (bool_to_matrix (x ⊕ y ⊕ z))).
Proof.
  matrix_denote. Msimpl.
  destruct x, y, z; unfold bool_to_ket; simpl; Msimpl; solve_matrix. 
Qed.
*)
Close Scope matrix_scope.

Check adder_cout_circ.
Lemma type_adder_cout_circ : Typed_Box adder_cout_circ.
Proof. type_check. Qed.
Lemma type_adder_z_circ : Typed_Box adder_z_circ.
Proof. type_check. Qed.
Lemma type_xor_circ : Typed_Box xor_circ.
Proof. type_check. Qed.

Definition adder_circ_1 : Box (5 ⨂ Qubit) (5 ⨂ Qubit) :=
  box_ inp ⇒
    let_ (cout_1, (z_1, (y_1, (x_1, (cin_1, dum1))))) ← output inp;
    let_ (out_z, z_2) ← unbox adder_z_circ ((y_1, (pair x_1 (pair cin_1 unit))), z_1);
    let_ (out_cout, cout_2) ← unbox adder_cout_circ (out_z, cout_1);
    output (pair cout_2 (pair z_2 out_cout)).
Check adder_circ_1.
Print adder_circ_1.
(*
Lemma type_adder_circ_1 : Typed_Box adder_circ_1.
Proof. type_check. Qed.
*)

Open Scope matrix_scope.
Lemma adder_circ_1_spec : forall (cin x y z cout : bool),
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (list_to_function [cout; z; y; x; cin] false))
  = (ctx_to_matrix 
      (list_of_Qubits 5) 
      (list_to_function [cout ⊕ ⌈ adder_cout_rbexp | list_to_function [y; x; cin] false ⌉; 
                         z ⊕ ⌈ adder_z_rbexp | list_to_function [y; x; cin] false ⌉; y; x; cin] false)).
Proof.
intros.
rewrite denote_db_unbox.
unfold adder_circ_1.
unfold unbox at 1.
unfold compose at 1.
Eval compute in (fresh_pat (5 ⨂ Qubit)%qc []).
Check (fresh_pat (5 ⨂ Qubit)%qc []).
Eval simpl in (fresh_pat (5 ⨂ Qubit)%qc []).
assert (H : (fresh_pat (5 ⨂ Qubit)%qc []) = (qubit 0%nat, (qubit 1%nat, (qubit 2%nat, (qubit 3%nat, (qubit 4%nat, ())))))).
{ simpl. reflexivity. }
Set Printing All.
replace (@fresh_pat (list Var) substitution_Gate_State
         (NTensor (S (S (S (S (S O))))) Qubit) (@Datatypes.nil Var)) 
        with ((qubit 0%nat, (qubit 1%nat, (qubit 2%nat, (qubit 3%nat, (qubit 4%nat, ())))))) by H.
unfold wproj at 1.
simpl.
rewrite H.

Locate "return".
rewrite H.
Locate "⨂".
rewrite H.
unfold denote_circuit.

rewrite H.
Check fresh_state.
Check 5 ⨂ Qubit.
Check [].
Print fresh_state.
Print get_fresh.
Print State.
unfold wproj at 1.
unfold fresh_pat at 1.


replace (fresh_state (5 ⨂ Qubit) []) with ([0%nat; 1%nat; 2%nat; 3%nat; 4%nat]) by auto.
rewrite <- denote_db_unbox.
unfold wproj at 1.
unfold letpair at 1.
rewrite denote_compose with (Γ:=Valid [Some Qubit; Some Qubit; Some Qubit; Some Qubit]) (Γ1:=Valid []).
unfold db_
apply (compile_correct xor_rbexp [Some Qubit; Some Qubit] (list_to_function [x; y] false) r).
apply (sub_some Qubit [Some Qubit]).
Qed.
Close Scope matrix_scope.




Definition 1_adder : Box 

Definition adder_z_circ_test_000 : Box One Qubit :=
  box_ inp ⇒
    gate_ cin ← init0 @() ;
    gate_ x   ← init0 @() ;
    gate_ y   ← init0 @() ;
    gate_ z   ← init0 @() ;
    let_ res  ← unbox adder_z_circ (pair (pair cin (pair x (pair y unit))) z);
    let_ ((y', res'), z') ← output res;
    let_ (x', (cin', t)) ← output res';
    gate_ ()  ← assert0 @cin' ;
    gate_ ()  ← assert0 @x' ;
    gate_ ()  ← assert0 @y' ;
    output z'.
Open Scope matrix_scope.
Lemma denote_adder_z_circ_test_000_correct : ⟦adder_z_circ_test_000⟧ (Id 1)= (bool_to_matrix false).
Proof.
  rewrite denote_db_unbox.
  unfold fresh_state.
  unfold fresh_pat.
  unfold adder_z_circ_test_000.
  unfold unbox at 1.
  rewrite denote_gate_circuit with (Γ1:=Valid []) (Γ2:=Valid []).
  - admit.
  - monoid. has_evars (Valid [] == Valid [] ∙ Valid []). Locate "∙". Check valid_merge. Check valid_merge. Print valid_merge.
    unfold valid_merge.
    reflexivity.
    unfold Build_valid_merge.
    unfold pf_valid. unfold valid_merge. auto.
  - rewrite denote_gate_circuit with (Γ1:=Valid []) (Γ2:=Valid [Some Qubit]).
    + rewrite denote_gate_circuit with (Γ1:=Valid []) (Γ2:=Valid [Some Qubit; Some Qubit]).
      * rewrite denote_gate_circuit with (Γ1:=Valid []) (Γ2:=Valid [Some Qubit; Some Qubit; Some Qubit]).
        { rewrite denote_compose with (Γ:=Valid [Some Qubit; Some Qubit; Some Qubit; Some Qubit]) (Γ1:=Valid []).
          - Check denote_db_unbox. 
            Locate "⋓". Check merge. Print OCtx.
            replace (Valid [] ⋓ Valid []) with (Valid []) by auto.
            rewrite <- (denote_db_unbox adder_z_circ).
            replace ([Some Qubit; Some Qubit; Some Qubit; Some Qubit]) 
with (fresh_pat ⟦[Some Qubit; Some Qubit; Some Qubit; Some Qubit]⟧) by auto.
            unfold compose_super. rewrite denote_compose with (Γ:=Valid [Some Qubit; Some Qubit; Some Qubit; Some Qubit]) (Γ1:=Valid []).
  - Admitted.
  - 
  unfold denote. unfold Denote_Box.
  unfold denote_box. unfold hoas_to_db_box.
  unfold denote_db_box.
  unfold Denote_Pat.
  Check fresh_state.
  Print fresh_state.
  Print get_fresh.
  Check Gate_State.
  Print Gate_State.
  Print Monad.State.
  unfold hoas_to_db at 1. fold compose.
  rewrite comp x1 res'.
  unfold comp.
  unfold hoas_to_db.
  replace (gate_ cin ← init0 @ ();
         gate_ x ← init0 @ ();
         gate_ y ← init0 @ ();
         gate_ z ← init0 @ ();
         comp res (unbox adder_z_circ (cin, (x, (y, ())), z))
           (comp x0 res
              (letpair y0 z' x0
                 (letpair y' res' y0
                    (comp x1 res'
                       (letpair x' y1 x1
                          (let (cin', _) := wproj y1 in
                           gate_ () ← assert0 @ cin';
                           gate_ () ← assert0 @ x';
                           gate_ () ← assert0 @ y'; z'))))))) with c.
  unfold hoas_to_db.
  unfold denote_db_box.
Check denote_gate_circuit.
  apply denote_gate_circuit.
  repeat (autounfold with den_db; simpl).
  unfold state_0.
  solve_matrix.
Qed.
Close Scope matrix_scope.

(*
Eval simpl in adder_z_circ.
Eval compute in adder_z_circ.

Lemma adder_z_circ_type : Typed_Box adder_z_circ.
Proof. type_check. Qed.

Print adder_cout_circ.

Eval simpl in adder_cout_circ.
Eval compute in adder_cout_circ.

Lemma adder_cout_circ_type : Typed_Box adder_cout_circ.
Proof. type_check. Qed.
*)

(*
Eval compute in (S (⟦ list_of_Qubits 3 ⟧) ⨂ Qubit).
Check (qubit 0%nat, (qubit 1%nat, (qubit 2%nat, (qubit 3%nat, unit)))).
Eval simple in (adder_cout_circ (qubit 0%nat, (qubit 1%nat, (qubit 2%nat, qubit 3%nat)))).
*)

(* n_adder_circ : returns a boxed circuit that adds two n-bit inputs
   example : (n_adder_circ 2) (cout2, (z2, (y2, (x2, (cout1, (z1, (y1, (x1, cin))))))))
             returns (cout2', (z2', (y2, (x2, (cout1', (z1', (y1, (x1, cin)))))))) where 
             z1' and cout1' are the first sum and carry, respectively, and
             z2' and cout2' are the second sum and carry.
 *)
Locate "⨂".
Definition adder_circ_1 : Box (5 ⨂ Qubit) (5 ⨂ Qubit) :=
  box_ inp ⇒
    let_ (coutn, (zn, inp')) ← output inp;
    let_ (yn, (xn, inp'')) ← output inp';
    let_ (coutn', dummy1) ← output inp'';
    let_ (out_z, zn') ← unbox adder_z_circ ((pair yn (pair xn (pair coutn' unit))), zn);
    let_ ((yn', tmp), coutn') ← unbox adder_cout_circ (out_z, coutn);
    let_ (xn', (coutn'', dummy2)) ← tmp;
    output (pair coutn' (pair zn' (pair yn' (pair xn' (pair coutn'' unit))))).
Check adder_circ_1.
Print adder_circ_1.

(*
Lemma type_adder_circ_1 : Typed_Box adder_circ_1.
Proof. type_check. Qed.
*)

Definition adder_circ_2 : Box (9 ⨂ Qubit) (9 ⨂ Qubit) :=
  box_ inp ⇒
    let_ (coutn, (zn, inp')) ← output inp;
    let_ (yn, (xn, inp'')) ← output inp';
    let_ out'' ← unbox (adder_circ_1) inp'';
    let_ (coutn', out''') ← output out'';
    let_ (out_z, zn') ← unbox adder_z_circ (pair (pair yn (pair xn (pair coutn' unit))) zn);
    let_ ((yn', tmp), coutn') ← unbox adder_cout_circ (out_z, coutn);
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
    let_ (out_z, zn') ← unbox adder_z_circ (pair (pair yn (pair xn (pair coutn' unit))) zn);
    let_ ((yn', tmp), coutn') ← unbox adder_cout_circ (out_z, coutn);
    let_ (xn', (coutn'', dummy)) ← tmp;
    output (pair coutn' (pair zn' (pair yn' (pair xn' (pair coutn'' out'''))))).
Check adder_circ_3.
Eval compute in adder_circ_3.

Program Fixpoint n_adder_circ (n : nat) 
: Box (Qubit ⊗ (((n ⨂ Qubit) ⊗ (n ⨂ Qubit)) ⊗ (Qubit ⊗ (n ⨂ Qubit))))
      (Qubit ⊗ (((n ⨂ Qubit) ⊗ (n ⨂ Qubit)) ⊗ (Qubit ⊗ (n ⨂ Qubit)))) :=
  match n with
  | 0 => box_ inp ⇒
         let_ (cin, (xy, cz)) ← output inp;
         let_ (c, z) ← output cz;
         let_ (c', (cin'))
(output inp)
  | S n' => box_ state_in ⇒
           let_ (cin, (xy, cz)) ← output state_in;
           let_ ((x0, x'), (y0, y')) ← output xy;
           let_ ((z0, z'), (c0, c')) ← output zc;
           let_ (xy', zc') ← ((x', y'), (z', c'));
           let_ temp_inp ← (cin, (xy', zc'));
           let_ temp_out ← unbox (n_adder_circ n') temp_inp;
           let_ (cin, (xy'_out, zc'_out)) ← output temp_out;
           let_ ((x'_out, y'_out), (z'_out, c'_out)) ← output (xy'_out, zc'_out);
           
           let_ (yn, (xn, inp'')) ← output inp';
           let_ out'' ← unbox (n_adder_circ n') inp'';
           let_ (coutn', out''') ← output out'';
           let_ (out_z, zn') ← unbox adder_z_circ (pair (pair yn (pair xn (pair coutn' unit))) zn);
           let_ ((yn', tmp), coutn') ← unbox adder_cout_circ (out_z, coutn);
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
(*
Program Fixpoint n_adder_circ (n : nat) : Box ((1+n+n+n+n) ⨂ Qubit) ((1+n+n+n+n) ⨂ Qubit) :=
  match n with
  | 0 => box_ inp ⇒ (output inp)
  | S n' => box_ inp ⇒
           let_ (coutn, (zn, inp')) ← output inp;
           let_ (yn, (xn, inp'')) ← output inp';
           let_ out'' ← unbox (n_adder_circ n') inp'';
           let_ (coutn', out''') ← output out'';
           let_ (out_z, zn') ← unbox adder_z_circ (pair (pair yn (pair xn (pair coutn' unit))) zn);
           let_ ((yn', tmp), coutn') ← unbox adder_cout_circ (out_z, coutn);
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
*)
Close Scope circ_scope.

(* Correctness of the adder circuit *)

Open Scope circ_scope.

Definition adder_0_circ := n_adder_circ 0.
Definition adder_1_circ := n_adder_circ 1.
Definition adder_2_circ := n_adder_circ 2.
Definition adder_3_circ := n_adder_circ 3.

Check adder_0_circ.
Lemma type_adder_0_circ : Typed_Box adder_0_circ.
Proof. type_check. Qed.

Check adder_1_circ.
Lemma type_adder_1_circ : Typed_Box adder_1_circ.
Proof.
  unfold Typed_Box.
  unfold unbox.
  unfold adder_1_circ.
  unfold n_adder_circ.
  intros.
  Locate "⊢".
  Locate type_check.
  unfold Types_Circuit.
  repeat (autounfold with den_db; simpl).
unfold type_check. simpl.
Check n_adder_circ_obligation_1 0.
replace (0 + 0)%nat with (0)%nat by omega.
simpl.
type_check.
unfold n_adder_circ_obligation_1.
unfold n_adder_circ_obligation_2.
replace (0 + 0)%nat with (0)%nat by omega.
Csimpl.
Check inj_neq (S (S (S (0 + 0 + 0 + 0)))).
Check eq_rect.
Check eq_ind.
Check eq_refl.
replace (0 + 1)%nat with 1%nat by omega.
replace (0 + 1 + 1 + 1)%nat with 3%nat by omega.
replace (0 + 0)%C with (0)%C.
Check 0 + 0.
Qed.


(* Some tests on type check and denotation 

Definition test_code_1 : Box Qubit Qubit :=
  box_ x ⇒ (gate_ y  ← init0 @() ; gate_ () ← assert0 @y ; output x).
Check Typed_Box test_code_1.
Lemma test_lemma_1 : Typed_Box test_code_1.
Proof.
  type_check.
Qed.
Definition denote_test_1 := ⟦test_code_1⟧.
Open Scope matrix_scope.
Definition state_0 : Matrix 2 2 := (|0⟩)×(⟨0|).
Lemma denote_test_1_correct : (denote_test_1 (state_0))= state_0.
Proof.
  unfold denote_test_1.
  repeat (autounfold with den_db; simpl).
  unfold state_0.
  autounfold with M_db.
  Msimpl.
  solve_matrix.
Qed.
Close Scope matrix_scope.

Definition test_code_2 : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒
    gate_ cin  ← init0 @() ;
    gate_ x0   ← init0 @() ;
    gate_ y0   ← init0 @() ;
    gate_ z0   ← init0 @() ;
    gate_ cout ← init0 @() ;
    gate_ ()   ← assert0 @cin ;
    gate_ ()   ← assert0 @x0 ;
    gate_ ()   ← assert0 @y0 ;
    output (cout, z0).
Check Typed_Box test_code_2.
Lemma test_lemma_2 : Typed_Box test_code_2.
Proof.
  type_check.
Qed.
Definition denote_test_2 := ⟦test_code_2⟧.
Open Scope matrix_scope.
Definition state_00 : Matrix 4 4 := (|0⟩⊗|0⟩)×(⟨0|⊗⟨0|).
Lemma denote_test_2_correct : (denote_test_2 (Id 1)) = state_00.
Proof.
  unfold denote_test_2.
  repeat (autounfold with den_db; simpl).
  unfold state_00.
  solve_matrix.
Qed.
Close Scope matrix_scope.

Definition test_code_3 : Box One (Qubit ⊗ (Qubit ⊗ (Qubit ⊗ (Qubit ⊗ One)))) :=
  box_ () ⇒
    gate_ cin  ← init0 @() ;
    gate_ x0   ← init0 @() ;
    gate_ y0   ← init0 @() ;
    gate_ z0   ← init0 @() ;
    let_ (res, z0')   ← unbox adder_z_circ (pair (pair y0 (pair x0 (pair cin unit))) z0) ;
    output (z0', res).
Check Typed_Box test_code_3.
Lemma test_lemma_3 : Typed_Box test_code_3.
Proof.
  type_check.
Qed.
Definition denote_test_3 := ⟦test_code_3⟧.
Open Scope matrix_scope.
Definition state_0000 : Matrix 16 16 := (|0⟩⊗|0⟩⊗|0⟩⊗|0⟩)×(⟨0|⊗⟨0|⊗⟨0|⊗⟨0|).
Lemma denote_test_3_correct : (denote_test_3 (Id 1)) = state_0000.
Proof.
  unfold denote_test_3.
  repeat (autounfold with den_db; simpl).
  unfold state_0000.
  solve_matrix.
Qed.
Close Scope matrix_scope.

Definition test_code_4 : Box One (Qubit ⊗ (Qubit ⊗ (Qubit ⊗ One))) :=
  box_ () ⇒
    gate_ cin  ← init0 @() ;
    gate_ x0   ← init0 @() ;
    gate_ y0   ← init0 @() ;
    gate_ z0   ← init0 @() ;
    let_ (res', z0')  ← unbox adder_z_circ (pair (pair y0 (pair x0 (pair cin unit))) z0) ;
    gate_ ()   ← assert0 @z0' ;
    output res'.
Check Typed_Box test_code_4.
Lemma test_lemma_4 : Typed_Box test_code_4.
Proof.
  type_check.
Qed.

Definition test_code_5 : Box One (Qubit ⊗ (Qubit ⊗ (Qubit ⊗ One))) :=
  box_ () ⇒
    gate_ cin  ← init0 @() ;
    gate_ x0   ← init0 @() ;
    gate_ y0   ← init0 @() ;
    gate_ z0   ← init0 @() ;
    let_ res   ← unbox adder_z_circ (pair (pair y0 (pair x0 (pair cin unit))) z0) ;
    let_ ((y0', res'), z0') ← output res ;
    gate_ ()   ← assert0 @y0' ;
    output (z0', res').
Check Typed_Box test_code_5.
Lemma test_lemma_5 : Typed_Box test_code_5.
Proof.
  type_check.
Qed.
Definition denote_test_5 := ⟦test_code_5⟧.
Eval simpl in denote_test_5.
Eval compute in denote_test_5.
Open Scope matrix_scope.
Definition state_000 : Matrix 8 8 := (|0⟩⊗|0⟩⊗|0⟩)×(⟨0|⊗⟨0|⊗⟨0|).
Lemma denote_test_5_correct : (denote_test_5 (Id 1))= state_000.
Close Scope matrix_scope.
*)

Definition circuit_0_plus_0 : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒
    gate_ cin  ← init0 @() ;
    gate_ x0   ← init0 @() ;
    gate_ y0   ← init0 @() ;
    gate_ z0   ← init0 @() ;
    gate_ cout ← init0 @() ;
    let_ res   ← unbox adder_1_circ
         (pair cout (pair z0 (pair y0 (pair x0 (pair cin unit))))) ;
    let_ (cout', (z0', rem1))
         ← output res ;
    let_ (y0', (x0', rem2))
         ← output rem1 ;
    let_ (cin', dummy)
         ← output rem2 ;
    gate_ ()   ← assert0 @cin' ;
    gate_ ()   ← assert0 @x0' ;
    gate_ ()   ← assert0 @y0' ;
    output (cout', z0').

Print circuit_0_plus_0.
Lemma type_circuit_0_plus_0 : Typed_Box circuit_0_plus_0.
Proof. type_check. Qed.

Definition denote_circuit_0_plus_0 := ⟦circuit_0_plus_0⟧.
Check denote_circuit_0_plus_0.
Check Superoperator 1 4.
Eval compute in ⟦One⟧.
Eval compute in ⟦Qubit ⊗ Qubit⟧.
Check Matrix 1 1.
Check Matrix 4 4.
Check Square 4.
Check Square 1.

Open Scope matrix_scope.
Definition state_00 : Matrix 4 4 := (|0⟩⊗|0⟩)×(⟨0|⊗⟨0|).
Hint Unfold DBCircuits.add_fresh_state : den_db.
                                               
Check Superoperator 1 1.
Print Superoperator.
Locate Superoperator.
Check Id 1.
Locate super.
Eval compute in super (Id 1) (Id 1) 1%nat 1%nat.

Lemma type_circuit_0_plus_0 : Typed_Box circuit_0_plus_0.
Proof. type_check. Qed.

Lemma denote_circuit_0_plus_0_correct : (denote_circuit_0_plus_0 (Id 1)) = state_00.
Proof.
  unfold denote_circuit_0_plus_0.
  unfold denote. unfold Denote_Box.
  unfold denote_box. unfold circuit_0_plus_0.
  unfold adder_1_circ.
  autounfold with den_db; simpl.
  autounfold with den_db; simpl.
  unfold wproj. simpl.
  autounfold with den_db; simpl.
  repeat (autounfold with den_db; simpl).
  unfold n_adder_circ_obligation_1. simpl.
  Check inj_neq.
  Check Nat2Z.inj_succ.
  unfold ex_ind. simpl.
  unfold eq_ind_r. simpl.
  unfold eq_sym. simpl.
  
  
  unfold n_adder_circ_obligation_1. simpl.
  unfold dec_eq_nat. simpl.
  Locate letpair.
  Print Zne.
  Locate comp.
  unfold compose. simpl.
  Locate lift_pat.
  unfold eq_rect. simpl.
  unfold wproj. simpl.
  unfold n_adder_circ_obligation_2. simpl.
  unfold eq_ind. simpl.
  unfold dec_eq_nat. simpl.
  Locate Decidable.dec_not_not.
  unfold eq_ind_r. simpl.
  unfold eq_ind. simpl.
  unfold eq_sym. simpl.
  Check Nat2Z.inj_succ.
  unfold Zne. simpl.
  Locate eq_refl.
  Check Z.succ.
  Print Z.succ.
  Locate plus_comm.
  rewrite (y + 1) with (1 + y).
  rewrite Z.plus_comm.
  Locate or_introl.
  unfold lift. simpl.
  Print Decidable.dec_not_not.
  Check comp.
  replace (Nat2Z.inj_succ 0) with (1%Z).
  unfold Nat2Z.inj_succ .
  Check Zne.
  unfold eq_refl. 
  Print eq_rect.
  Check eq_rect.
  Check or_introl.
  Check Decidable.dec_not_not.
  Print Decidable.decidable.
  simpl.
  unfold DBCircuits.add_fresh_state. simpl.
  unfold DBCircuits.hoas_to_db.
  rewrite denote_compose.
  rewrite process_gate_denote.
  simpl.
  apply process_gate_denote.
  prep_matrix_equality.
  simpl.
  unfold DBCircuits.add_fresh_state.
  unfold DBCircuits.get_fresh.
  simpl.
  autounfold with M_db.
  destruct_m_eq.
  ; clra.
  autounfold.

  unfold circuit_0_plus_0.
  unfold adder_1_circ. unfold n_adder_circ.

  unfold denote. unfold Denote_Box.
  unfold denote_box. unfold denote_db_box. unfold denote_db_circuit.
  unfold DBCircuits.hoas_to_db_box. unfold 
  unfold denote_db_circuit.
    fold_denote.
simpl.
  unfold DBCircuits.hoas_to_db.
  unfold denote_gate.
  unfold Id.
  unfold state_00. unfold conj_transpose. unfold Cconj. unfold kron. unfold Mmult.
  destruct x, y.
  -  simpl.
  unfold ket0. simpl.
  - simpl.
  
   destruct x.
  destruct y. simpl.
 . simpl. omega. plus_comm. omega.
Close Scope matrix_scope.

Check state_00.
Check One.
Print One.
Check Id 1.
Check (denote_circuit_0_plus_0 (Id 1)).

Definition denote_adder_1_circ := ⟦adder_1_circ⟧.
Check denote_adder_1_circ.
Eval compute in denote_adder_1_circ.
Definition circuit_101_plus_010 : 
Lemma adder1 : [n_adder_circ 1]

Definition zn := qubit 3%nat.
Definition yn := qubit 2%nat.
Definition xn := qubit 1%nat.
Definition cin := qubit 0%nat.
Check pair zn (pair yn (pair xn (pair cin unit))).

Close Scope circ_scope.

(*
Eval simpl in (n_adder_circ 1).
Eval simpl in (n_adder_circ 2).
Eval simpl in (n_adder_circ 3).
 *)
