Require Import HOASExamples.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import SemanticLib.
Require Import Symmetric.
Require Import Oracles.
Require Import Matrix.
Require Import Denotation.
Require Import Monad.
Require Import Program.

Require Import List.
Import ListNotations.

Open Scope circ_scope.
Open Scope nat_scope.
Open Scope bexp_scope.

Infix "⊻" := b_xor (at level 40).
Infix "∧" := b_and (at level 40).

Definition nat_to_var (n : nat) : Var := n. 
Coercion b_var : Var >-> bexp. 
Coercion nat_to_var : nat >-> Var.

(*
Input : var 1 : y
        var 2 : x
        var 3 : cin
Output : cout = cin(x ⊕ y) ⊕ xy
*)
Definition adder_cout_bexp : bexp := (3 ∧ (2 ⊻ 1)) ⊻ (2 ∧ 1).

(*
Input : var 0 : y
        var 1 : x
        var 2 : cin
Output : z = cin ⊕ (x ⊕ y)
 *)
Definition adder_z_bexp : bexp := 2 ⊻ (1 ⊻ 0).

(*
Input : var 0 : x
        var 1 : y
Output : z = x ⊕ y
*)
Definition xor_bexp : bexp := 0 ⊻ 1.

(*
Input : var 0 : x
Output : z = x
*)
Definition id_bexp : bexp := 0.

Definition list_to_function {A} (l : list A) (d : A) := fun (n : nat) => nth n l d.
Definition fun_of_bools (l : list bool) := fun n => nth n l false.

Definition bools_to_matrix (l : list bool) : Square (2^(length l)) := 
  big_kron (map bool_to_matrix l).

(*
Fixpoint bools_to_matrix (l : list bool) : Square (2^(length l)) := 
  match l with
  | []      => Id 1
  | b :: bs => (bool_to_matrix b ⊗ bools_to_matrix bs)%M
  end.
*)

Lemma test_adder_cout_bexp_000 : 
⌈ adder_cout_bexp | fun_of_bools [false; false; false; false]⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_bexp_001 : 
⌈ adder_cout_bexp | fun_of_bools [false; false; false; true] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_bexp_010 : 
⌈ adder_cout_bexp | fun_of_bools [false; false; true; false] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_bexp_011 : 
⌈ adder_cout_bexp | fun_of_bools [false; false; true; true] ⌉ = true.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_bexp_100 : 
⌈ adder_cout_bexp | fun_of_bools [false; true; false; false] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_bexp_101 : 
⌈ adder_cout_bexp | fun_of_bools [false; true; false; true] ⌉ = true.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_bexp_110 : 
⌈ adder_cout_bexp | fun_of_bools [false; true; true; false] ⌉ = true.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_cout_bexp_111 : 
⌈ adder_cout_bexp | fun_of_bools [false; true; true; true] ⌉ = true.
Proof. simpl. reflexivity. Qed.

Lemma test_adder_z_bexp_000 : 
⌈ adder_z_bexp | fun_of_bools [false; false; false] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_bexp_001 : 
⌈ adder_z_bexp | fun_of_bools [false; false; true] ⌉ = true.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_bexp_010 : 
⌈ adder_z_bexp | fun_of_bools [false; true; false] ⌉ = true.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_bexp_011 : 
⌈ adder_z_bexp | fun_of_bools [false; true; true] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_bexp_100 : 
⌈ adder_z_bexp | fun_of_bools [true; false; false] ⌉ = true.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_bexp_101 : 
⌈ adder_z_bexp | fun_of_bools [true; false; true] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_bexp_110 : 
⌈ adder_z_bexp | fun_of_bools [true; true; false] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Lemma test_adder_z_bexp_111 : 
⌈ adder_z_bexp | fun_of_bools [true; true; true] ⌉ = true.
Proof. simpl. reflexivity. Qed.

Close Scope bexp_scope.


Definition list_of_Qubits (n : nat) : Ctx := repeat (Some Qubit) n.

Definition adder_cout_circ :=
  compile adder_cout_bexp (list_of_Qubits 4).
Eval compute in adder_cout_circ.

Definition adder_z_circ := compile adder_z_bexp (list_of_Qubits 3).

(* adder_cout circuit with pads, input type is ((4+n) ⨂ Qubit), Box ((5+n) ⨂ Qubit) ((5+n) ⨂ Qubit) *)
Definition adder_cout_circ_with_pads (n : nat) :=
  compile adder_cout_bexp (list_of_Qubits (4+n)).

(* adder_z circuit with pads, input type is ((3+n) ⨂ Qubit), Box ((4+n) ⨂ Qubit) ((4+n) ⨂ Qubit) *)
Definition adder_z_circ_with_pads (n : nat) :=
  compile adder_z_bexp (list_of_Qubits (3+n)).

Definition calc_xor_circ :=
  compile xor_bexp (list_of_Qubits 2).

Definition calc_id_circ := compile id_bexp (list_of_Qubits 1).

Definition calc_id_circ_with_pads (n : nat) := compile id_bexp (list_of_Qubits (1+n)).

Lemma adder_cout_circ_WT : Typed_Box adder_cout_circ.
Proof. apply compile_WT. Qed.
Lemma adder_z_circ_WT : Typed_Box adder_z_circ.
Proof. apply compile_WT. Qed.
Lemma adder_cout_circ_with_pads_WT : forall n,
  Typed_Box (adder_cout_circ_with_pads n).
Proof. intros. apply compile_WT. Qed.
Lemma adder_z_circ_with_pads_WT : forall n,
  Typed_Box (adder_z_circ_with_pads n).
Proof. intros. apply compile_WT. Qed.
Lemma calc_xor_circ_WT : Typed_Box calc_xor_circ.
Proof. apply compile_WT. Qed.
Lemma calc_id_circ_WT : Typed_Box calc_id_circ.
Proof. apply compile_WT. Qed.
Lemma calc_id_circ_with_pads_WT : forall n,
  Typed_Box (calc_id_circ_with_pads n).
Proof. intros. apply compile_WT. Qed.

Open Scope matrix_scope.

Lemma adder_cout_circ_spec : forall (cout z y x cin : bool),
⟦adder_cout_circ⟧ (bool_to_matrix cout ⊗ bools_to_matrix [z; y; x; cin])
= bools_to_matrix ((cout ⊕ ⌈ adder_cout_bexp | fun_of_bools [z; y; x; cin] ⌉) :: [z; y; x; cin]).
Proof.
intros.
apply (compile_correct adder_cout_bexp (list_of_Qubits 4) 
  (fun_of_bools [z; y; x; cin]) cout).
repeat constructor.
Qed.

Lemma adder_z_circ_spec : forall (z y x cin : bool),
⟦adder_z_circ⟧ (bool_to_matrix z ⊗ bools_to_matrix [y; x; cin])
= bool_to_matrix (z ⊕ ⌈ adder_z_bexp | fun_of_bools [y; x; cin]⌉) ⊗ 
  bools_to_matrix [y; x; cin].
Proof.
intros.
apply (compile_correct adder_z_bexp [Some Qubit; Some Qubit; Some Qubit] 
  (fun_of_bools [y; x; cin]) z).
repeat constructor.
Qed.

Lemma adder_cout_circ_with_pads_spec : forall (n : nat) (f : Var -> bool),
⟦adder_cout_circ_with_pads n⟧ ((bool_to_matrix (f 0%nat)) ⊗ (ctx_to_matrix (list_of_Qubits (4+n)) (fun x => f (S x))))
= (bool_to_matrix ((f 0%nat) ⊕ ⌈ adder_cout_bexp | (fun x => f (S x)) ⌉)) ⊗ 
  (ctx_to_matrix (list_of_Qubits (4+n)) (fun x => f (S x))).
Proof.
intros.
apply (compile_correct adder_cout_bexp (list_of_Qubits (4+n)) (fun x => f (S x)) (f 0)).
repeat constructor.
Qed.

Lemma adder_z_circ_with_pads_spec : forall (n : nat) (f : Var -> bool),
⟦adder_z_circ_with_pads n⟧ ((bool_to_matrix (f 0)) ⊗ (ctx_to_matrix (list_of_Qubits (3+n)) (fun x => f (S x))))
= (bool_to_matrix ((f 0) ⊕ ⌈ adder_z_bexp | (fun x => f (S x)) ⌉)) ⊗ 
  (ctx_to_matrix (list_of_Qubits (3+n)) (fun x => f (S x))).
Proof.
intros.
apply (compile_correct adder_z_bexp (list_of_Qubits (3+n)) (fun x => f (S x)) (f 0%nat)).
repeat constructor.
Qed.

Lemma calc_xor_circ_spec : forall (x y r : bool),
⟦calc_xor_circ⟧ (bool_to_matrix r ⊗ bools_to_matrix [x; y])
= bool_to_matrix (r ⊕ ⌈ xor_bexp | fun_of_bools [x; y] ⌉) ⊗ 
  bools_to_matrix [x; y].
Proof.
intros.
apply (compile_correct xor_bexp [Some Qubit; Some Qubit] (fun_of_bools [x; y]) r).
repeat constructor.
Qed.

(* Proof of specification using matrix_denote : failed
Lemma calc_xor_circ_spec_matrix : forall (x y z : bool),
  ⟦xor_circ⟧ ((bool_to_matrix x) ⊗ (bool_to_matrix y) ⊗ (bool_to_matrix z))
  = ((bool_to_matrix x) ⊗ (bool_to_matrix y) ⊗ (bool_to_matrix (x ⊕ y ⊕ z))).
Proof.
  matrix_denote. Msimpl.
  destruct x, y, z; unfold bool_to_ket; simpl; Msimpl; solve_matrix. 
Qed.
*)

(* Should just be bool_to_matrix x *)
Lemma calc_id_circ_spec : forall (x r : bool),
⟦calc_id_circ⟧ (bool_to_matrix r ⊗ bools_to_matrix [x])
= (bool_to_matrix (r ⊕ ⌈ id_bexp | fun_of_bools [x] ⌉)) ⊗ 
  bools_to_matrix [x].
Proof.
intros.
apply (compile_correct id_bexp [Some Qubit] (fun_of_bools [x]) r).
apply (sub_some (Some Qubit) Qubit []).
apply sub_empty.
Qed.

Lemma calc_id_circ_with_pads_spec : forall (n : nat) (f : Var -> bool),
⟦calc_id_circ_with_pads n⟧ ((bool_to_matrix (f 0%nat)) ⊗ (ctx_to_matrix (list_of_Qubits (1+n)) (fun x => f (S x))))
= ((bool_to_matrix (f 0%nat  ⊕ ⌈ id_bexp | (fun x => f (S x)) ⌉)) ⊗ (ctx_to_matrix (list_of_Qubits (1+n)) (fun x => f (S x)))).
Proof.
intros.
apply (compile_correct id_bexp (list_of_Qubits (1+n)) (fun x => f (S x)) (f 0%nat)).
repeat constructor.
Qed.
Close Scope matrix_scope.

(*
Input : (cout, (z, (y, (x, (cin, ())))))
Output : (cout', (z', (y, (x, (cin, ())))))
*)
Definition adder_circ_1 : Box (5 ⨂ Qubit) (5 ⨂ Qubit) := 
  (id_circ ∥ adder_z_circ) ;; adder_cout_circ.

Local Obligation Tactic := program_simpl; try omega.
Program Definition adder_circ_1_with_pads (n : nat) : Box ((5+n) ⨂ Qubit) ((5+n) ⨂ Qubit) := 
  ((@id_circ Qubit) ∥ (adder_z_circ_with_pads n)) ;; 
  (adder_cout_circ_with_pads n).
Next Obligation.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Defined.
Next Obligation.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Defined.

Lemma adder_circ_1_WT : Typed_Box adder_circ_1.
Proof.
  apply inSeq_WT.
  - apply inPar_WT.
    + apply id_circ_WT.
    + apply adder_z_circ_WT.
  - apply adder_cout_circ_WT.
Qed.

Lemma adder_circ_1_with_pads_WT : forall (n : nat),
  Typed_Box (adder_circ_1_with_pads n).
Proof.
  intros.
  unfold adder_circ_1_with_pads. simpl_eq.
  apply inSeq_WT.
  - apply inPar_WT.
    + apply id_circ_WT.
    +apply adder_z_circ_with_pads_WT.
  - apply adder_cout_circ_with_pads_WT.
Qed.

Open Scope matrix_scope.
Lemma adder_circ_1_spec : forall (cin x y z cout : bool),
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [cout; z; y; x; cin]))
  = (ctx_to_matrix 
      (list_of_Qubits 5) 
      (fun_of_bools [cout ⊕ ⌈ adder_cout_bexp | fun_of_bools [z; y; x; cin] ⌉; 
                         z ⊕ ⌈ adder_z_bexp | fun_of_bools [y; x; cin] ⌉; y; x; cin])).
Proof.
  intros.
  unfold adder_circ_1.
  rewrite inSeq_correct.
  - unfold compose_super.
    unfold denote. unfold Denote_Box.
    unfold ctx_to_matrix. simpl.
    rewrite_inPar.
    + remember adder_z_circ_spec as H; clear HeqH.
      unfold bools_to_matrix in H. simpl in H.
      rewrite H. clear H.
      simpl_rewrite id_circ_Id.
      * remember adder_cout_circ_spec as H; clear HeqH.
      unfold bools_to_matrix in H. simpl in H.
        rewrite H. clear H.
        reflexivity.
      * apply WF_bool_to_matrix.
  - apply adder_cout_circ_WT.
  - apply inPar_WT.
    + apply id_circ_WT.
    + apply adder_z_circ_WT.
Qed.

Lemma adder_circ_1_with_pads_spec : forall (n : nat) (f : Var -> bool),
⟦adder_circ_1_with_pads n⟧ (ctx_to_matrix (list_of_Qubits (5+n)) f)
= (bool_to_matrix ((f 0) ⊕ ⌈ adder_cout_bexp | (fun x => f (S x)) ⌉)) ⊗
  ((bool_to_matrix ((f 1) ⊕ ⌈ adder_z_bexp | (fun x => f (S (S x))) ⌉)) ⊗
  (ctx_to_matrix (list_of_Qubits (3+n)) (fun x => f (S (S x))))).
Proof.
  intros.
  unfold adder_circ_1_with_pads.
  Opaque denote. simpl_eq. Transparent denote.
  rewrite inSeq_correct.
  - unfold compose_super.
    unfold denote. unfold Denote_Box.
    unfold ctx_to_matrix. simpl.
    rewrite_inPar.
    + 
      assert (H1 : forall n f, length (ctx_to_mat_list (list_of_Qubits n) f) = 
                          size_ctx (list_of_Qubits n)).
      { induction n0.
        - easy.
        - intros. simpl. rewrite IHn0. easy. }
      remember adder_z_circ_with_pads_spec as H; clear HeqH.
      specialize (H n%nat (fun (x : Var) => f (S x))).
      unfold ctx_to_matrix in H.
      simpl in *. unfold kron at 5.
      unfold kron in H at 4.
      rewrite H1 in H. unfold list_of_Qubits in H.
      rewrite H.
      clear H1 H.
      simpl_rewrite id_circ_Id.
      * 
        assert (H1 : forall n f, length (ctx_to_mat_list (list_of_Qubits n) f) = size_ctx (list_of_Qubits n)).
        { induction n0.
          - reflexivity.
          - intros. simpl. rewrite IHn0. reflexivity. }
        remember adder_cout_circ_with_pads_spec as H; clear HeqH.
        specialize (H n%nat (fun (x : Var) => match x with
                                              | S O => f 1%nat ⊕ (f 4%nat ⊕ (f 3%nat ⊕ f 2%nat))
                                              | _ => f x
                                              end)).
        unfold ctx_to_matrix in H. simpl in H.
        simpl in *. unfold kron at 5.
        unfold kron in H at 5.
        rewrite H1 in H. unfold list_of_Qubits in H.
        apply H.
      * apply WF_bool_to_matrix.
  - apply adder_cout_circ_with_pads_WT.
  - apply inPar_WT.
    + apply id_circ_WT.
    + apply adder_z_circ_with_pads_WT.
Qed.
Close Scope matrix_scope.

Lemma adder_circ_1_test_000 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; false; false; false]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false ; false; false; false])).
Proof. apply adder_circ_1_spec. Qed.
Lemma adder_circ_1_test_001 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; false; false; true]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; true ; false; false; true])).
Proof. apply adder_circ_1_spec. Qed.
Lemma adder_circ_1_test_010 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; false; true; false]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; true ; false; true; false] )).
Proof. apply adder_circ_1_spec. Qed.
Lemma adder_circ_1_test_011 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; false; true; true]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [true; false ; false; true; true] )).
Proof. apply adder_circ_1_spec. Qed.
Lemma adder_circ_1_test_100 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; true; false; false]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; true ; true; false; false] )).
Proof. apply adder_circ_1_spec. Qed.
Lemma adder_circ_1_test_101 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; true; false; true]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [true; false ; true; false; true] )).
Proof. apply adder_circ_1_spec. Qed.
Lemma adder_circ_1_test_110 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; true; true; false]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [true; false ; true; true; false] )).
Proof. apply adder_circ_1_spec. Qed.
Lemma adder_circ_1_test_111 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; true; true; true] ))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [true; true ; true; true; true] )).
Proof. apply adder_circ_1_spec. Qed.

(*
Input : (cout, (z1, (y1, (x1, (z2, (y2, (x2, ... , (zn, (yn, (xn, (cin, ())))))))))))
Output : (cout', (z1', (y1, (x1, (z2', (y2, (x2, ... , (zn', (yn, (xn, (cin, ())))))))))))
*)

(* This can be refactored using init_at *)
Program Fixpoint adder_circ_n (n : nat) : Box ((2+n+n+n) ⨂ Qubit) ((2+n+n+n) ⨂ Qubit) := 
  match n with
  | O => calc_id_circ
  | S n' => ((@id_circ Qubit) ∥ ((@id_circ Qubit) ∥ ((@id_circ Qubit) ∥ ((@id_circ Qubit) ∥ (strip_one_l_in (init0 ∥ (inParMany (1+n'+n'+n') (@id_circ Qubit)))))))) ;; 
            ((@id_circ Qubit) ∥ ((@id_circ Qubit) ∥ ((@id_circ Qubit) ∥ ((@id_circ Qubit) ∥ ((adder_circ_n n')))))) ;; 
            (adder_circ_1_with_pads (1+n'+n'+n')) ;;
            ((@id_circ Qubit) ∥ ((@id_circ Qubit) ∥ ((@id_circ Qubit) ∥ ((@id_circ Qubit) ∥ (strip_one_l_out (assert0 ∥ (inParMany (1+n'+n'+n') (@id_circ Qubit))))))))
  end.
Next Obligation.
  replace (n' + S n' + S n')%nat with (2 + n' + n' + n')%nat by omega.
  simpl. reflexivity.
Defined.
Next Obligation.
  replace (n' + S n' + S n')%nat with (2 + n' + n' + n')%nat by omega.
  simpl. reflexivity.
Defined.

Lemma adder_circ_n_WT : forall (n : nat),
  Typed_Box (adder_circ_n n).
Proof.
  intros. induction n.
  - unfold adder_circ_n. unfold calc_id_circ.
    simpl. apply (CNOT_at_WT 2%nat 1%nat 0%nat).
  - unfold adder_circ_n. simpl_eq.
    apply inSeq_WT.
    + compile_typing True. apply inParMany_WT. apply id_circ_WT.
    + apply inSeq_WT.
      * compile_typing True. unfold adder_circ_n in IHn.
        program_simpl.
      * apply inSeq_WT.
        { apply (adder_circ_1_with_pads_WT (S (n + n + n)%nat)). }
        { compile_typing True. apply inParMany_WT. apply id_circ_WT. }
Qed.

(* For n-adder specification *)
Fixpoint n_adder_cout_bexp (n m : nat) : bexp :=
  match m with
  | O => b_var (n+n+n+1)%nat (* cin = b_var (n+n+n+1)%nat *)
  | S m' => let i := (n-m)%nat in
            b_xor (b_and (n_adder_cout_bexp n m') (b_xor (b_var (i+i+i+3)%nat) (b_var (i+i+i+2)%nat))) (b_and (b_var (i+i+i+3)%nat) (b_var (i+i+i+2)%nat))
             (* cin = n_adder_cout_bexp n m'
                x = b_var (i+i+i+3)%nat
                y = b_var (i+i+i+2)%nat *)
  end.

Eval simpl in n_adder_cout_bexp 3 3.
Eval simpl in n_adder_cout_bexp 3 2.
Eval simpl in n_adder_cout_bexp 3 1.
Eval simpl in n_adder_cout_bexp 3 0.

Definition n_adder_z_bexp (n m : nat) : bexp :=
  match m with
  | O => b_var (n+n+n+1)%nat (* cin = b_var (n+n+n+1)%nat *)
  | S m' => let i := (n-m)%nat in
            b_xor (n_adder_cout_bexp n m') (b_xor (b_var (i+i+i+3)%nat) (b_var (i+i+i+2)%nat))
             (* cin = n_adder_cout_bexp n m'
                x = b_var (i+i+i+3)%nat
                y = b_var (i+i+i+2)%nat *)
  end.

Eval simpl in n_adder_z_bexp 3 3.
Eval simpl in n_adder_z_bexp 3 2.
Eval simpl in n_adder_z_bexp 3 1.
Eval simpl in n_adder_z_bexp 3 0.

Fixpoint n_adder_z_compute (n m : nat) (f : Var -> bool) : (Var -> bool) :=
  match m with
  | O => f
  | S m' => let i := (n-m)%nat in
            (fun f' => (fun x => if x =? (i+i+i+1)%nat then
                                  (f' x) ⊕ ⌈ n_adder_z_bexp n m | f ⌉
                                 else
                                  f' x)) (n_adder_z_compute n m' f)
  end.

Definition n_adder_cout_compute (n : nat) (f : Var -> bool) : (Var -> bool) :=
  fun x => match x with
           | O => (f 0%nat) ⊕ ⌈ n_adder_cout_bexp n n | f ⌉
           | S x' => f (S x')
           end.

Eval compute in (n_adder_z_compute 2 2 (fun_of_bools [false; false ; true; true; false; true; true; false])) 1%nat.
Eval compute in (n_adder_z_compute 3 3 (fun_of_bools [false; false ; true; true; false; true; true; false; true; true; true])).
Eval compute in (n_adder_cout_compute 3 (fun_of_bools [false; false ; true; true; false; true; true; false; true; true; true])).
Eval compute in (n_adder_cout_compute 3 (n_adder_z_compute 3 3 (fun_of_bools [false; false ; true; true; false; true; true; false; true; true; true]))).

(* Simplified, but I can't see this doing what we want *)
Fixpoint adder_circ_n' (n : nat) : Box ((2+n) ⨂ Qubit) ((2+n) ⨂ Qubit) := 
  match n with
  | O => calc_id_circ
  | S n' => ((@id_circ Qubit) ∥ (strip_one_l_in (init0 ∥ id_circ))) ;; 
            ((@id_circ Qubit) ∥ (strip_one_l_out (assert0 ∥ id_circ)))
  end.

Open Scope matrix_scope.
Lemma adder_circ_n'_spec : forall (n : nat) (f : Var -> bool),
⟦adder_circ_n' n⟧ (ctx_to_matrix (list_of_Qubits (2+n)) f)
= (ctx_to_matrix (list_of_Qubits (2+n)) (n_adder_cout_compute n (n_adder_z_compute n n f))).
Proof.
  induction n.
  - intros f. apply calc_id_circ_spec.
  - intros f.
    simpl.
    simpl_rewrite inSeq_correct.
    unfold compose_super.
    unfold list_of_Qubits in *.
    simpl. 
    unfold ctx_to_matrix in *. simpl in *.
    rewrite Nat.sub_diag in *. simpl in *.
    rewrite_inPar'.
    rewrite strip_one_l_in_eq.
    rewrite <- (kron_1_l _ _ (bool_to_matrix (f 1) ⊗ _)). 
    repeat rewrite_inPar'.
    repeat simpl_rewrite id_circ_Id.    
    simpl_rewrite init0_spec.
    rewrite strip_one_l_out_eq.
    rewrite_inPar'.
    simpl_rewrite id_circ_Id.    
    simpl_rewrite assert0_spec.
    rewrite kron_1_l.
(* this is an identity, so that's as far as you get *)
Abort.

Open Scope matrix_scope.
Lemma adder_circ_n_spec : forall (n : nat) (f : Var -> bool),
⟦adder_circ_n n⟧ (ctx_to_matrix (list_of_Qubits (2+n+n+n)) f)
= (ctx_to_matrix (list_of_Qubits (2+n+n+n)) (n_adder_cout_compute n (n_adder_z_compute n n f))).
Proof.
  induction n.
  - intros.
    remember (calc_id_circ_spec (f 1%nat) (f 0%nat)).
    simpl in *. unfold ctx_to_matrix in *.
    unfold big_kron in *. simpl in *. apply e.
  - intros.
    Opaque denote. simpl_eq. Transparent denote.
    specialize inSeq_correct as IS. simpl in IS.
    simpl. repeat (rewrite IS; compile_typing (compile_WT)).
    unfold compose_super.
    Set Printing All.

(* ??? *)

    apply inPar_correct 

(Tensor Qubit
        (Tensor Qubit
           (Tensor Qubit
              (Tensor Qubit
                 (Tensor Qubit
                    (Tensor Qubit
                       (NTensor (Init.Nat.add (Init.Nat.add n n) n) Qubit)))))))
(Tensor Qubit
        (Tensor Qubit
           (Tensor Qubit
              (Tensor Qubit
                 (Tensor Qubit
                    (NTensor (Init.Nat.add (Init.Nat.add n n) n) Qubit))))))


(Tensor Qubit
           (Tensor Qubit
              (Tensor Qubit
                 (Tensor Qubit
                    (Tensor Qubit
                       (Tensor Qubit
                          (NTensor (Init.Nat.add (Init.Nat.add n n) n) Qubit)))))))
(Tensor Qubit
           (Tensor Qubit
              (Tensor Qubit
                 (Tensor Qubit
                    (Tensor Qubit
                       (Tensor Qubit
                          (NTensor (Init.Nat.add (Init.Nat.add n n) n) Qubit)))))))

    assert (H1 : forall n, (size_ctx (list_of_Qubits n )) = n).
    { induction n0.
      - reflexivity.
      - simpl. rewrite IHn0. reflexivity. }

    assert (H2 : forall n f, @length (Matrix (S (S O)) (S (S O)))
    (ctx_to_mat_list (list_of_Qubits n) f) = n).
    { induction n0.
      - reflexivity.
      - intros. simpl. rewrite IHn0. reflexivity. }

    + rewrite H1.
      listify_kron.
    rewrite inPar_correct.
 rewrite_inPar.
 rewrite H2.
    rewrite_inPar.
 rewrite H2.
    apply inPar_correct.
    rewrite_inPar.
    rewrite inSeq_correct.
    + unfold compose_super.
      rewrite inSeq_correct.
      * unfold compose_super.
        rewrite inSeq_correct.
        unfold compose_super.
        { unfold denote at 0. unfold Denote_Box.
      unfold ctx_to_matrix. simpl.
      replace (n + S n + S n + 1)%nat with (3 + n + n + n)%nat by omega.
      replace (n + n + n + 1)%nat with (1 + n + n + n)%nat by omega.
      simpl.

      rewrite_inPar.
      rewrite H1.
      rewrite_inPar.
      rewrite_inPar.
      rewrite_inPar.
      Set Printing All.
      apply inSeq_correct.
      remember id_circ_Id. simpl in e. repeat rewrite e. clear e Heqe.
      unfold strip_one_l_in. unfold denote_box at 2. simpl.
      unfold compose_super. unfold apply_new0. unfold super. simpl.
      Locate "⨂".
      Check NTensor.
      Check (denote_box true (inParMany (n + n + n + 1)%nat (@id_circ Qubit))).
      fold (denote_box true (inParMany (n + n + n + 1)%nat (@id_circ Qubit))).
(NTensor (n + n + n + 1)%nat Qubit) (NTensor (n + n + n + 1)%nat Qubit)).
fold inParMany (n + n + n + 1)%nat (@id_circ Qubit).
      Check @denote_box.
      Set Printing All.
      fold (@denote_box true (⨂ ctx_to_mat_list (list_of_Qubits (n + n + n + 1)) (fun v : Var => f (S (S (S (S v))))))
                             (⨂ ctx_to_mat_list (list_of_Qubits (n + n + n + 1)) (fun v : Var => f (S (S (S (S v))))))).
      rewrite strip_one_l_in_eq. matrix_simpl.
      Set Printing All.
      rewrite_inPar.
      Set Printing All.
      apply inSeq_correct.
      Check (denote_box true (init0 ∥ id_circ # (n + n + n + 1))).
      Set Printing All. simpl.
      Set Printing All.
      Check (init0 ∥ id_circ # (n + n + n + 1)).
      Check (ctx_to_mat_list (list_of_Qubits (n + n + n + 1))).
      replace ((n + n + n + 1)%nat) with ((1 + n + n + n)%nat).
      rewrite_inPar.
      
      Transparent 
      replace (list_of_Qubits (n + n + n + 1)%nat) with (list_of_Qubits (1 + n + n + n)%nat).
      rewrite_inPar.
      unfold big_kron.
rewrite H2. rewrite inPar_correct.
      remember
      rewrite id_circ_Id.
      simpl_rewrite calc_id_circ_spec.
      rewrite calc_id_circ_spec.
      unfold strip_one_l_in. simpl.
      listify_kron. simpl.

      listify_kron. simpl.
      clear IHn.
      Set Printing All.

      rewrite inPar.
      unfold kron at 1.
      Check inPar_correct.
      replace (length
              (ctx_to_mat_list (list_of_Qubits (n + n + n))
                 (fun v : Var => f (S (S (S (S (S v)))))))) with (n+n+n)%nat.
      rewrite plus_0_r. simpl.
      rewrite inPar_correct.
      rewrite_inPar.
    Opaque denote. simpl. simpl_eq. Transparent denote.
    rewrite inSeq_correct. unfold compose_super.
    + rewrite inSeq_correct. unfold compose_super.
      * rewrite inSeq_correct. unfold compose_super.
        { unfold denote. unfold Denote_Box.
          rewrite_inPar.
    simpl. simpl_eq.

    rewrite_inPar.
    Opaque denote. unfold adder_circ_n. simpl_eq. Transparent denote.
    Opaque denote. simpl. simpl_eq. Transparent denote.
    rewrite inSeq_correct. unfold compose_super.
    + rewrite_inPar. remember ((⟦ id_circ ∥ (id_circ ∥ (id_circ ∥ (id_circ ∥ adder_circ_n n)));;
   adder_circ_1_with_pads (n + n + n + 1);;
   id_circ
   ∥ (id_circ
       ∥ (id_circ
           ∥ (id_circ
               ∥ strip_one_l_out (assert0 ∥ id_circ # (n + n + n + 1))))) ⟧)).
unfold denote at 2. rewrite inPar_correct. Check inPar_correct. rewrite_inPar.
rewrite inSeq_correct. unfold compose_super.
      * rewrite inSeq_correct. unfold compose_super.
        { assert ().
repeat (try apply inPar_correct; try apply id_circ_spec). )
    apply inSeq_correct.
    rewrite IHn.
    replace (1 + S n + S n + S n + 1)%nat with (5 + n + n + n)%nat by omega.
 unfold NTensor. unfold adder_circ_n. rewrite calc_id_circ_spec.
Qed.

Lemma adder_circ_n_spec : forall (n m : nat),
Close Scope matrix_scope.

(* unit test 0 : 0+01+10=011 (cin : 0, x : 01, y : 10, z : 11, cout : 0)
Input : (0, (0, (1, (0, (0, (0, (1, (0, ()))))))))
Output : (0, (1, (1, (0, (1, (0, (1, (0, ()))))))))
*)
Lemma adder_circ_n_unit_test_0 :
  ⟦adder_circ_n 2⟧ (ctx_to_matrix (list_of_Qubits 8) 
    (fun_of_bools [false; false; true; false; false; false; true; false] false))
  = (ctx_to_matrix (list_of_Qubits 5) 
    (fun_of_bools [false; true ; true; false; true; false; true; false] false)).
Proof.
  simpl.
  rewrite_inPar.
  rewrite_inPar.
  repeat apply inSeq_correct.
  rewrite
  simpl.
apply adder_circ_1_spec. Qed.

(*
Definition adder_circ_1 : Box (5 ⨂ Qubit) (5 ⨂ Qubit) :=
  box_ inp ⇒
    let_ (cout_1, (z_1, (y_1, (x_1, (cin_1, dum1))))) ← output inp;
    let_ (z_2, out_z) ← unbox adder_z_circ (z_1, (y_1, (pair x_1 (pair cin_1 unit))));
    let_ (cout_2, out_cout) ← unbox adder_cout_circ (cout_1, out_z);
    output (cout_2, (z_2, out_cout)).
Check adder_circ_1.
Print adder_circ_1.

Lemma type_adder_circ_1 : Typed_Box adder_circ_1.
Proof.
  unfold adder_circ_1.
  type_check.
Qed.
*)

(*
Fixpoint remove_var {W} (p : Pat W) (i : nat) : Pat W :=
  match p with
  | unit => unit
  | qubit x => qubit (pred x)
  | bit x => bit (pred x)
  | pair p1 p2 => pair (remove_var p1 i) (remove_var p2 i)
  end.
Lemma DBCircuit_equiv : forall {W1 W2} (Γ : Ctx) (b : Box W1 W2) (p : Pat W1), 
          hoas_to_db (Valid (None :: Γ)) (unbox b p) 
          = hoas_to_db Γ (unbox b (remove_var p 0)).
*)

Open Scope matrix_scope.
Lemma adder_circ_1_spec : forall (cin x y z cout : bool),
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [cout; z; y; x; cin] false))
  = (ctx_to_matrix 
      (list_of_Qubits 5) 
      (fun_of_bools [cout ⊕ ⌈ adder_cout_bexp | fun_of_bools [y; x; cin] false ⌉; 
                         z ⊕ ⌈ adder_z_bexp | fun_of_bools [y; x; cin] false ⌉; y; x; cin] false)).
Proof.
intros.
rewrite denote_db_unbox.
unfold adder_circ_1.
Opaque adder_z_circ.
Opaque adder_cout_circ.
simpl.
rewrite denote_compose with (Γ:=Valid [None; Some Qubit; Some Qubit; Some Qubit; Some Qubit]) (Γ1:=Valid [Some Qubit]).
- simpl.
  remember (adder_z_circ_spec y x cin z) as H; clear HeqH.
  rewrite denote_db_unbox in H. simpl in H.
  unfold compose_super.

  simpl in H.
  repeat (autounfold with den_db; simpl). 
  denote_matrix.
 admit.
- apply type_adder_z_circ.
  type_check_once.
  invert_patterns.
  apply types_pair with (Γ1:=Valid [None; Some Qubit]) (Γ2:=Valid [None; None; Some Qubit; Some Qubit; Some Qubit]).
  + exists [None; Some Qubit; Some Qubit; Some Qubit; Some Qubit]. reflexivity.
  + Transparent merge. simpl. reflexivity.
  + apply types_qubit.
    apply SingletonLater. apply SingletonHere.
  + apply types_pair with (Γ1:=Valid [None; None; Some Qubit]) (Γ2:=Valid [None; None; None; Some Qubit; Some Qubit]).
  + exists [None; Some Qubit; Some Qubit; Some Qubit; Some Qubit]. reflexivity.
  + Transparent merge. simpl. reflexivity.
  + apply types_qubit.
    apply SingletonLater. apply SingletonHere.
simpl. Transparent Types_Pat.

 replace (Valid [None; Some Qubit] ⋓ Valid [None; None; Some Qubit; Some Qubit; Some Qubit]) with (Valid [None; Some Qubit; Some Qubit; Some Qubit; Some Qubit]).
 unfold merge. monoid.
 Set Printing All. unfold is_valid. apply pat_ctx_valid. validate.
  eapply types_pair.
  + 

 Print Types_Pat.
  type_check.
  Check types_pair.
 Locate "⊢". Print Types_Circuit.
  
  unfold adder_z_circ.
  type_check.
  apply types_nfold Types_Circuit. simpl.
- unfold denote_circuit at 2.
  simpl.
  unfold denote_db_circuit.
  assert (H : adder_z_circ_spec).
  Check adder_z_circ_spec.
  assert (H : (⟨ (@nil)%nat ⋓ [Some Qubit; None; None; None; None]
   | [None; Some Qubit; Some Qubit; Some Qubit; Some Qubit]
   ⊩ unbox adder_z_circ
       (qubit 1%nat, (qubit 2%nat, (qubit 3%nat, (qubit 4%nat, ())))) ⟩)
  (ctx_to_matrix [Some Qubit; Some Qubit; Some Qubit; Some Qubit; Some Qubit]
     (fun_of_bools [cout; z; y; x; cin] false)) 
    = (bool_to_matrix (z ⊕ ⌈ adder_z_bexp | fun_of_bools [y; x; cin] false ⌉)) ⊗ 
  (ctx_to_matrix [Some Qubit; Some Qubit; Some Qubit] (fun_of_bools [y; x; cin] false))).
unfold compose_super.
  Check denote_circuit.
  Locate "⋓".
  Check merge.
  unfold denote.
  unfold Denote_OCtx.
  unfold size_octx.

  simpl.
  unfold merge.
  rewrite <- denote_db_unbox.
assert (H : (fresh_state (5 ⨂ Qubit)%qc []) = (qubit 0%nat, (qubit 1%nat, (qubit 2%nat, (qubit 3%nat, (qubit 4%nat, ())))))).
{ simpl. reflexivity. }
  Check denote_circuit.
  
  unfold merge_valid.
 rewrite denote_compose with (Γ:=Valid [Some Qubit; None; None; None; None; None; Some Qubit; Some Qubit; Some Qubit]) (Γ1:=Valid [None; None; None; None; None; Some Qubit; None; None; None]).
  + simpl.

(*
assert (H : (fresh_pat (5 ⨂ Qubit)%qc []) = (qubit 0%nat, (qubit 1%nat, (qubit 2%nat, (qubit 3%nat, (qubit 4%nat, ())))))).
{ simpl. reflexivity. }
*)
Set Printing All.
assert (H : (@fresh_pat (list Var) substitution_Gate_State
         (NTensor (S (S (S (S (S O))))) Qubit) (@Datatypes.nil Var)) 
       = (qubit 0%nat, (qubit 1%nat, (qubit 2%nat, (qubit 3%nat, (qubit 4%nat, ())))))).
{ simpl. reflexivity. }
simpl.
rewrite H.
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
apply (compile_correct xor_bexp [Some Qubit; Some Qubit] (fun_of_bool [x; y] false) r).
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
