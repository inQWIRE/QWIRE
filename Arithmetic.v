Require Import HOASExamples.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import HOASLib.
Require Import Oracles.
Require Import SemanticLib.
Require Import Symmetric.
Require Import Matrix.
Require Import Denotation.
Require Import Composition.
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
Output : sum = cin ⊕ (x ⊕ y)
 *)
Definition adder_sum_bexp : bexp := 2 ⊻ (1 ⊻ 0).

(*
Input : var 0 : x
        var 1 : y
Output : xor = x ⊕ y
*)
Definition xor_bexp : bexp := 0 ⊻ 1.

(*
Input : var 0 : x
Output : x' = x
*)
Definition id_bexp : bexp := 0.

Definition list_to_function {A} (l : list A) (d : A) := fun (n : nat) => nth n l d.
Definition fun_of_bools (l : list bool) := fun n => nth n l false.

(*
Fixpoint bools_to_matrix (l : list bool) : Square (2^(length l)) := 
  match l with
  | []      => I 1
  | b :: bs => (bool_to_matrix b ⊗ bools_to_matrix bs)%M
  end.
*)

Example test_adder_cout_bexp_000 : 
⌈ adder_cout_bexp | fun_of_bools [false; false; false; false]⌉ = false.
Proof. simpl. reflexivity. Qed.
Example test_adder_cout_bexp_001 : 
⌈ adder_cout_bexp | fun_of_bools [false; false; false; true] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Example test_adder_cout_bexp_010 : 
⌈ adder_cout_bexp | fun_of_bools [false; false; true; false] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Example test_adder_cout_bexp_011 : 
⌈ adder_cout_bexp | fun_of_bools [false; false; true; true] ⌉ = true.
Proof. simpl. reflexivity. Qed.
Example test_adder_cout_bexp_100 : 
⌈ adder_cout_bexp | fun_of_bools [false; true; false; false] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Example test_adder_cout_bexp_101 : 
⌈ adder_cout_bexp | fun_of_bools [false; true; false; true] ⌉ = true.
Proof. simpl. reflexivity. Qed.
Example test_adder_cout_bexp_110 : 
⌈ adder_cout_bexp | fun_of_bools [false; true; true; false] ⌉ = true.
Proof. simpl. reflexivity. Qed.
Example test_adder_cout_bexp_111 : 
⌈ adder_cout_bexp | fun_of_bools [false; true; true; true] ⌉ = true.
Proof. simpl. reflexivity. Qed.

Example test_adder_sum_bexp_000 : 
⌈ adder_sum_bexp | fun_of_bools [false; false; false] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Example test_adder_sum_bexp_001 : 
⌈ adder_sum_bexp | fun_of_bools [false; false; true] ⌉ = true.
Proof. simpl. reflexivity. Qed.
Example test_adder_sum_bexp_010 : 
⌈ adder_sum_bexp | fun_of_bools [false; true; false] ⌉ = true.
Proof. simpl. reflexivity. Qed.
Example test_adder_sum_bexp_011 : 
⌈ adder_sum_bexp | fun_of_bools [false; true; true] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Example test_adder_sum_bexp_100 : 
⌈ adder_sum_bexp | fun_of_bools [true; false; false] ⌉ = true.
Proof. simpl. reflexivity. Qed.
Example test_adder_sum_bexp_101 : 
⌈ adder_sum_bexp | fun_of_bools [true; false; true] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Example test_adder_sum_bexp_110 : 
⌈ adder_sum_bexp | fun_of_bools [true; true; false] ⌉ = false.
Proof. simpl. reflexivity. Qed.
Example test_adder_sum_bexp_111 : 
⌈ adder_sum_bexp | fun_of_bools [true; true; true] ⌉ = true.
Proof. simpl. reflexivity. Qed.

Close Scope bexp_scope.


Definition list_of_Qubits (n : nat) : Ctx := repeat (Some Qubit) n.

Definition adder_cout_circ :=
  compile adder_cout_bexp (list_of_Qubits 4).
Eval compute in adder_cout_circ.

Definition adder_sum_circ := compile adder_sum_bexp (list_of_Qubits 3).

(* adder_cout circuit with pads, input type is ((4+n) ⨂ Qubit), Box ((5+n) ⨂ Qubit) ((5+n) ⨂ Qubit) *)
Definition adder_cout_circ_with_pads (n : nat) :=
  compile adder_cout_bexp (list_of_Qubits (4+n)).

(* adder_sum circuit with pads, input type is ((3+n) ⨂ Qubit), Box ((4+n) ⨂ Qubit) ((4+n) ⨂ Qubit) *)
Definition adder_sum_circ_with_pads (n : nat) :=
  compile adder_sum_bexp (list_of_Qubits (3+n)).

Definition calc_xor_circ :=
  compile xor_bexp (list_of_Qubits 2).

Definition calc_id_circ := compile id_bexp (list_of_Qubits 1).

Notation "'let_' ( p1 , p2 ) ← 'output' p3 ; c" := (letpair p1 p2 p3 c) (at level 14, right associativity) : circ_scope.

Ltac compute_compile :=
  repeat (try unfold compile; simpl;
          try unfold inPar; try unfold inSeq;
          try unfold id_circ; try unfold init_at; try unfold assert_at;
          try unfold Symmetric.CNOT_at).

(*
Require Coq.derive.Derive.
Derive p SuchThat (calc_id_circ = p) As h.
Proof.
  unfold calc_id_circ; unfold id_bexp.
  compute_compile.
 *)
(*
Require Coq.derive.Derive.
Derive p SuchThat (adder_sum_circ = p) As h.
Proof.
  unfold adder_sum_circ; unfold adder_sum_bexp.
  compute_compile. 
  repeat (unfold comp; simpl). cbv.
  
  Check (output ∘ pair (qubit 1)). simpl_eq. show_goal. show_hyps. program_simpl. unfold compose. simpl.
  unfold comp. Locate "∘". Check pair.
Notation "'let_' p ← 'unbox' ( c1 ) ; c2" := (comp p c1 c2) (at level 14, right associativity) : circ_scope.

(let_ (p8, p9)← output p7;
                          comp p2'
                            (comp x
                               (let_ (p10, p11)← output p9;
                                gate_ p' ← assert0 @ p10; (p', p11))
                               (let_ (_, p')← output x; p')) (p8, p2'))
  
  let_ (z_2, out_z) ← unbox adder_z_circ (z_1, (y_1, (pair x_1 (pair cin_1 unit))));
*)

Definition calc_id_circ_with_pads (n : nat) := compile id_bexp (list_of_Qubits (1+n)).

Lemma adder_cout_circ_WT : Typed_Box adder_cout_circ.
Proof. apply compile_WT. Qed.

Lemma adder_sum_circ_WT : Typed_Box adder_sum_circ.
Proof. apply compile_WT. Qed.

Lemma adder_cout_circ_with_pads_WT : forall n,
  Typed_Box (adder_cout_circ_with_pads n).
Proof. intros. apply compile_WT. Qed.

Lemma adder_sum_circ_with_pads_WT : forall n,
  Typed_Box (adder_sum_circ_with_pads n).
Proof. intros. apply compile_WT. Qed.

Lemma calc_xor_circ_WT : Typed_Box calc_xor_circ.
Proof. apply compile_WT. Qed.

Lemma calc_id_circ_WT : Typed_Box calc_id_circ.
Proof. apply compile_WT. Qed.

Lemma calc_id_circ_with_pads_WT : forall n,
  Typed_Box (calc_id_circ_with_pads n).
Proof. intros. apply compile_WT. Qed.

Hint Resolve adder_cout_circ_WT adder_sum_circ_WT adder_cout_circ_with_pads_WT adder_sum_circ_with_pads_WT calc_xor_circ_WT calc_id_circ_WT calc_id_circ_with_pads_WT : typed_db.

Hint Extern 2 (Typed_Box (adder_cout_circ_with_pads _)) => 
  apply adder_cout_circ_with_pads_WT : typed_db.
Hint Extern 2 (Typed_Box (adder_sum_circ_with_pads _)) => 
  apply adder_sum_circ_with_pads_WT : typed_db.
Hint Extern 2 (Typed_Box (calc_id_circ_with_pads _)) =>
  apply calc_id_circ_with_pads_WT : typed_db.

Open Scope matrix_scope.

(* Specifications *)

Definition calc_cout (cin x y : bool) : bool := (cin && (x ⊕ y)) ⊕ (x && y).
Definition calc_sum (cin x y : bool) : bool := cin ⊕ (x ⊕ y).

Lemma adder_cout_circ_spec : forall (cout sum y x cin : bool),
⟦adder_cout_circ⟧ (bool_to_matrix cout ⊗ bools_to_matrix [sum; y; x; cin])
= bools_to_matrix ((cout ⊕ (calc_cout cin x y)) :: [sum; y; x; cin]).
Proof.
intros.
apply (compile_correct adder_cout_bexp (list_of_Qubits 4) 
  (fun_of_bools [sum; y; x; cin]) cout).
repeat constructor.
Qed.

Lemma adder_sum_circ_spec : forall (sum y x cin : bool),
⟦adder_sum_circ⟧ (bool_to_matrix sum ⊗ bools_to_matrix [y; x; cin])
= bool_to_matrix (sum ⊕ (calc_sum cin x y)) ⊗  bools_to_matrix [y; x; cin].
Proof.
intros.
apply (compile_correct adder_sum_bexp (list_of_Qubits 3) 
  (fun_of_bools [y; x; cin]) sum).
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

Lemma adder_sum_circ_with_pads_spec : forall (n : nat) (f : Var -> bool),
⟦adder_sum_circ_with_pads n⟧ ((bool_to_matrix (f 0)) ⊗ (ctx_to_matrix (list_of_Qubits (3+n)) (fun x => f (S x))))
= (bool_to_matrix ((f 0) ⊕ ⌈ adder_sum_bexp | (fun x => f (S x)) ⌉)) ⊗ 
  (ctx_to_matrix (list_of_Qubits (3+n)) (fun x => f (S x))).
Proof.
intros.
apply (compile_correct adder_sum_bexp (list_of_Qubits (3+n)) (fun x => f (S x)) (f 0%nat)).
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
Input : (cout, (sum, (y, (x, (cin, ())))))
Output : (cout', (sum', (y, (x, (cin, ())))))
*)
Definition carrier_circ_1 : Box (5 ⨂ Qubit) (5 ⨂ Qubit) := adder_cout_circ.

(*
Input : (cout, (sum, (y, (x, (cin, ())))))
Output : (cout', (sum', (y, (x, (cin, ())))))
*)
Definition adder_circ_1 : Box (5 ⨂ Qubit) (5 ⨂ Qubit) := 
  (id_circ ∥ adder_sum_circ) ;; adder_cout_circ.

Local Obligation Tactic := program_simpl; try omega.
Program Definition carrier_circ_1_with_pads (n : nat) : Box ((5+n) ⨂ Qubit) ((5+n) ⨂ Qubit)
  := (adder_cout_circ_with_pads n).
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

Local Obligation Tactic := program_simpl; try omega.
Program Definition adder_circ_1_with_pads (n : nat) : Box ((5+n) ⨂ Qubit) ((5+n) ⨂ Qubit) := 
  ((@id_circ Qubit) ∥ (adder_sum_circ_with_pads n)) ;; 
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

Lemma carrier_circ_1_WT : Typed_Box carrier_circ_1.
Proof. type_check. Qed.

Lemma carrier_circ_1_with_pads_WT : forall (n : nat),
  Typed_Box (carrier_circ_1_with_pads n).
Proof.
  intros.
  unfold carrier_circ_1_with_pads. simpl_eq.
  apply adder_cout_circ_with_pads_WT.
Qed.

Lemma adder_circ_1_WT : Typed_Box adder_circ_1.
Proof. type_check. Qed.

Lemma adder_circ_1_with_pads_WT : forall (n : nat),
  Typed_Box (adder_circ_1_with_pads n).
Proof. 
  intros.
  unfold adder_circ_1_with_pads. simpl_eq.
  apply inSeq_WT.
  - apply inPar_WT.
    + apply id_circ_WT.
    + apply adder_sum_circ_with_pads_WT.
  - apply adder_cout_circ_with_pads_WT.
Qed.

Hint Resolve carrier_circ_1_WT carrier_circ_1_with_pads_WT adder_circ_1_WT 
     adder_circ_1_with_pads_WT : typed_db.

Hint Extern 2 (Typed_Box (carrier_circ_1_with_pads _)) =>
  apply carrier_circ_1_with_pads_WT : typed_db.
Hint Extern 2 (Typed_Box (adder_circ_1_with_pads _)) =>
  apply adder_circ_1_with_pads_WT : typed_db.

Open Scope matrix_scope.

Lemma dim_eq_lemma_1 : forall n, (size_ctx (list_of_Qubits n )) = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. unfold list_of_Qubits in IHn. rewrite IHn. reflexivity.
Qed.
Lemma dim_eq_lemma_2 : forall n (f : Var -> bool),
    @length (Square 2) (ctx_to_mat_list (list_of_Qubits n) f) = n.
Proof.
  induction n.
  - reflexivity.
  - intros. simpl. rewrite IHn. reflexivity.
Qed.
Lemma dim_eq_lemma_3 : forall n, size_wtype (NTensor n Qubit) = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
Lemma kron_eq_1 : forall {m n o p} m11 m12 m21 m22,
                 m11 = m21 -> m12 = m22 -> @kron m n o p m11 m12 = @kron m n o p m21 m22.
  intros. rewrite H. rewrite H0. reflexivity.
Qed.
Lemma big_kron_eq_1 : forall n f1 f2,
    (forall x, f1 x = f2 x) ->
    ⨂ ctx_to_mat_list (list_of_Qubits n) f1 = ⨂ ctx_to_mat_list (list_of_Qubits n) f2.
Proof.
  induction n.
  - intros. simpl. reflexivity.
  - intros. simpl. unfold list_of_Qubits in IHn.
    rewrite (IHn (fun v : Var => f1 (S v)) (fun v : Var => f2 (S v))).
    rewrite H. show_dimensions. repeat rewrite dim_eq_lemma_2. reflexivity.
    intros. rewrite H. reflexivity.
Qed.
Lemma ctx_to_matrix_eq_1 : forall n f1 f2,
    (forall x, f1 x = f2 x) ->
    ctx_to_matrix (list_of_Qubits n) f1 = ctx_to_matrix (list_of_Qubits n) f2.
Proof.
  induction n.
  - intros. matrix_denote. solve_matrix.
  - intros.
    specialize (IHn (fun v : Var => f1 (S v)) (fun v : Var => f2 (S v))).
    unfold ctx_to_matrix in *.
    unfold big_kron in *. simpl in *.
    show_dimensions.
    rewrite dim_eq_lemma_2.
    rewrite dim_eq_lemma_2.
    apply kron_eq_1.
    + rewrite H. reflexivity.
    + apply IHn. intros. apply H.
Qed.

Lemma carrier_circ_1_spec : forall (cin x y sum cout : bool),
  ⟦carrier_circ_1⟧ (bools_to_matrix [cout; sum; y; x; cin])
  = (bools_to_matrix [cout ⊕ (calc_cout cin x y); sum ; y; x; cin]).
Proof.
  intros.
  unfold carrier_circ_1.
  apply adder_cout_circ_spec.
Qed.

Lemma adder_circ_1_spec : forall (cin x y sum cout : bool),
  ⟦adder_circ_1⟧ (bools_to_matrix [cout; sum; y; x; cin])
  = (bools_to_matrix [cout ⊕ (calc_cout cin x y); sum ⊕ (calc_sum cin x y); y; x; cin]).
Proof.
  intros.
  unfold adder_circ_1. simpl.
  rewrite inSeq_correct; [|type_check|type_check].
  unfold compose_super.
  unfold denote. unfold Denote_Box.
  unfold bools_to_matrix. simpl.
  rewrite_inPar.
  remember adder_sum_circ_spec as H; clear HeqH.
  unfold bools_to_matrix in H. simpl in H.
  rewrite H. clear H.
  simpl_rewrite id_circ_spec; [|auto with wf_db].
  remember adder_cout_circ_spec as H; clear HeqH.
  unfold bools_to_matrix in H. simpl in H.
  rewrite H. clear H.
  reflexivity.
Qed.

Lemma carrier_circ_1_with_pads_spec : forall (n : nat) (f : Var -> bool),
⟦carrier_circ_1_with_pads n⟧ (ctx_to_matrix (list_of_Qubits (5+n)) f)
= (bool_to_matrix ((f 0) ⊕ ⌈ adder_cout_bexp | (fun x => f (S x)) ⌉)) ⊗
  ((bool_to_matrix (f 1)) ⊗ (ctx_to_matrix (list_of_Qubits (3+n)) (fun x => f (S (S x))))).
Proof.
  intros.
  unfold carrier_circ_1_with_pads.
  Opaque denote. simpl_eq. Transparent denote.
  assert (H1 : forall n f, length (ctx_to_mat_list (list_of_Qubits n) f) = 
                           size_ctx (list_of_Qubits n)).
  { induction n0.
    - easy.
    - intros. simpl. rewrite IHn0. easy. }
  remember adder_cout_circ_with_pads_spec as H; clear HeqH.
  specialize (H n%nat (fun (x : Var) => f x)).
  unfold ctx_to_matrix in *. simpl in *.
  show_dimensions.
  rewrite H1 in *. unfold list_of_Qubits in *.
  rewrite H. reflexivity.
Qed.

Lemma adder_circ_1_with_pads_spec : forall (n : nat) (f : Var -> bool),
⟦adder_circ_1_with_pads n⟧ (ctx_to_matrix (list_of_Qubits (5+n)) f)
= (bool_to_matrix ((f 0) ⊕ ⌈ adder_cout_bexp | (fun x => f (S x)) ⌉)) ⊗
  ((bool_to_matrix ((f 1) ⊕ ⌈ adder_sum_bexp | (fun x => f (S (S x))) ⌉)) ⊗
  (ctx_to_matrix (list_of_Qubits (3+n)) (fun x => f (S (S x))))).
Proof.
  intros.
  unfold adder_circ_1_with_pads.
  Opaque denote. simpl_eq. Transparent denote.
  simpl.
  rewrite inSeq_correct; try solve [type_check]. 
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
      remember adder_sum_circ_with_pads_spec as H; clear HeqH.
      specialize (H n%nat (fun (x : Var) => f (S x))).
      unfold ctx_to_matrix in H.
      simpl in *. unfold kron at 5.
      unfold kron in H at 4.
      rewrite H1 in H. unfold list_of_Qubits in H.
      rewrite H.
      clear H1 H.
      simpl_rewrite id_circ_spec.
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
Qed.
Close Scope matrix_scope.

Example adder_circ_1_test_000 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; false; false; false]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false ; false; false; false])).
Proof. apply adder_circ_1_spec. Qed.

Example adder_circ_1_test_001 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; false; false; true]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; true ; false; false; true])).
Proof. apply adder_circ_1_spec. Qed.

Example adder_circ_1_test_010 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; false; true; false]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; true ; false; true; false] )).
Proof. apply adder_circ_1_spec. Qed.

Example adder_circ_1_test_011 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; false; true; true]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [true; false ; false; true; true] )).
Proof. apply adder_circ_1_spec. Qed.

Example adder_circ_1_test_100 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; true; false; false]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; true ; true; false; false] )).
Proof. apply adder_circ_1_spec. Qed.

Example adder_circ_1_test_101 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; true; false; true]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [true; false ; true; false; true] )).
Proof. apply adder_circ_1_spec. Qed.

Example adder_circ_1_test_110 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; true; true; false]))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [true; false ; true; true; false] )).
Proof. apply adder_circ_1_spec. Qed.

Example adder_circ_1_test_111 :
  ⟦adder_circ_1⟧ (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [false; false; true; true; true] ))
  = (ctx_to_matrix (list_of_Qubits 5) (fun_of_bools [true; true ; true; true; true] )).
Proof. apply adder_circ_1_spec. Qed.

(*
Input : (cout, (sum1, (y1, (x1, (sum2, (y2, (x2, ... , (sumn, (yn, (xn, (cin, ())))))))))))
Output : (cout', (sum1', (y1, (x1, (sum2', (y2, (x2, ... , (sumn', (yn, (xn, (cin, ())))))))))))
*)

Open Scope nat_scope.

(* This can be refactored using init_at *)
Program Fixpoint adder_circ_n_left (n : nat) : Box ((1+3*n) ⨂ Qubit) ((1+4*n) ⨂ Qubit) := 
  match n with
  | O => id_circ
  | S n' => (@id_circ Qubit ∥ (@id_circ Qubit ∥ (@id_circ Qubit ∥ (adder_circ_n_left n')))) ;;
            (init_at false (4*n) 0) ;;
            (adder_circ_1_with_pads (4*n'))
  end.
Next Obligation.
  replace (S n' + (S n' + (S n' + (S n' + 0))))
    with (4 + n' + (n' + (n' + (n' + 0)))) by omega.
  simpl. reflexivity.
Defined.
Next Obligation.
  replace (S n' + (S n' + (S n' + (S n' + 0))))
    with (4 + n' + (n' + (n' + (n' + 0)))) by omega.
  simpl. reflexivity.
Defined.
Next Obligation.
  replace (n' + S (n' + S (n' + 0))) with (2 + n' + (n' + (n' + 0))) by omega.
  simpl. reflexivity.
Defined.
Next Obligation.
  replace (n' + S (n' + S (n' + S (n' + 0))))
    with (3 + (n' + (n' + (n' + (n' + 0))))) by omega.
  simpl. reflexivity.
Defined.

Program Fixpoint adder_circ_n_right (n : nat) : Box ((1+4*n) ⨂ Qubit) ((1+3*n) ⨂ Qubit) := 
  match n with
  | O => id_circ
  | S n' => (carrier_circ_1_with_pads (4*n')) ;;
            (assert_at false (4*n) 0) ;;
            (@id_circ Qubit ∥ (@id_circ Qubit ∥ (@id_circ Qubit ∥ (adder_circ_n_right n')))) 
  end.
Next Obligation.
  replace (S n' + (S n' + (S n' + (S n' + 0))))
    with (4 + (n' + (n' + (n' + (n' + 0))))) by omega.
  simpl. reflexivity.
Defined.
Next Obligation.
  replace (S n' + (S n' + (S n' + (S n' + 0))))
    with (4 + (n' + (n' + (n' + (n' + 0))))) by omega.
  simpl. reflexivity.
Defined.
Next Obligation.
  replace (n' + S (n' + S (n' + S (n' + 0))))
    with (3 + (n' + (n' + (n' + (n' + 0))))) by omega.
  simpl. reflexivity.
Defined.
Next Obligation.
  replace (n' + S (n' + S (n' + 0))) with (2 + n' + (n' + (n' + 0))) by omega.
  simpl. reflexivity.
Defined.
Program Fixpoint adder_circ_n (n : nat) : Box ((2+3*n) ⨂ Qubit) ((2+3*n) ⨂ Qubit) := 
  match n with
  | O => calc_id_circ
  | S n' => (id_circ ∥ (id_circ ∥ (id_circ ∥ (id_circ ∥ (adder_circ_n_left n'))))) ;; 
            (adder_circ_1_with_pads (4*n')) ;;
            (id_circ ∥ (id_circ ∥ (id_circ ∥ (id_circ ∥ (adder_circ_n_right n')))))
  end.
Next Obligation.
  replace (n' + S (n' + S (n' + 0)))
    with (2 + (n' + (n' + (n' + 0)))) by omega.
  simpl. reflexivity.
Defined.
Next Obligation.
  replace (n' + S (n' + S (n' + 0)))
    with (2 + (n' + (n' + (n' + 0)))) by omega.
  simpl. reflexivity.
Defined.

Lemma adder_circ_n_left_WT : forall (n : nat),
    Typed_Box (adder_circ_n_left n).
Proof.
  induction n.
  - unfold adder_circ_n_left. apply id_circ_WT.
  - unfold adder_circ_n_left. simpl_eq.
    apply inSeq_WT.
    + compile_typing True. unfold adder_circ_n_left in IHn.
      program_simpl.
    + simpl_eq. apply inSeq_WT.
      * apply strip_one_l_in_WT. apply inPar_WT.
        { apply boxed_gate_WT. }
        { simple_typing (inParMany_WT). }
      * simpl_eq. apply adder_circ_1_with_pads_WT.
Qed.
Lemma adder_circ_n_right_WT : forall (n : nat),
  Typed_Box (adder_circ_n_right n).
Proof.
  induction n.
  - unfold adder_circ_n_right. apply id_circ_WT.
  - unfold adder_circ_n_right. simpl_eq.
    apply inSeq_WT.
    + simpl_eq. apply carrier_circ_1_with_pads_WT.
    + simpl_eq. apply inSeq_WT.
      * apply strip_one_l_out_WT. apply inPar_WT.
        { apply boxed_gate_WT. }
        { simple_typing (inParMany_WT). }
      * simpl_eq. compile_typing True. unfold adder_circ_n_right in IHn.
        program_simpl.
Qed.
Lemma adder_circ_n_WT : forall (n : nat),
  Typed_Box (adder_circ_n n).
Proof.
  induction n.
  - unfold adder_circ_n. apply calc_id_circ_WT.
  - unfold adder_circ_n. simpl_eq.
    apply inSeq_WT.
    + simple_typing (adder_circ_n_left_WT).
    + apply inSeq_WT.
      { apply adder_circ_1_with_pads_WT. }
      { simple_typing (adder_circ_n_right_WT). }
Qed.

Open Scope matrix_scope.

(* For n-adder specification *)

Lemma mixed_state_big_kron_ctx_to_mat_list : forall n f,  Mixed_State (⨂ ctx_to_mat_list (list_of_Qubits n) f).
Proof.
  induction n.
  - intros. simpl. show_mixed.
  - intros. simpl.
    specialize (mixed_state_kron 2) as H. apply H.
    + show_mixed.
    + apply IHn.
Qed.

Fixpoint n_adder_cout_bexp (n m : nat) : bexp :=
  match m with
  | O => b_var (1+n+n+n)%nat (* cin = b_var (1+n+n+n)%nat *)
  | S m' => let i := (n-m)%nat in
            b_xor (b_and (n_adder_cout_bexp n m') (b_xor (b_var (3+i+i+i)%nat) (b_var (2+i+i+i)%nat))) (b_and (b_var (3+i+i+i)%nat) (b_var (2+i+i+i)%nat))
             (* cin = n_adder_cout_bexp n m'
                x = b_var (3+i+i+i)%nat
                y = b_var (2+i+i+i)%nat *)
  end.

Eval simpl in n_adder_cout_bexp 3 3.
Eval simpl in n_adder_cout_bexp 3 2.
Eval simpl in n_adder_cout_bexp 3 1.
Eval simpl in n_adder_cout_bexp 3 0.

Definition n_adder_sum_bexp (n m : nat) : bexp :=
  match m with
  | 0 => b_var (1+n+n+n)%nat (* cin = b_var (1+n+n+n)%nat *)
  | S m' => let i := (n-m)%nat in
            b_xor (n_adder_cout_bexp n m') (b_xor (b_var (3+i+i+i)%nat) (b_var (2+i+i+i)%nat))
             (* cin = n_adder_cout_bexp n m'
                x = b_var (3+i+i+i)%nat
                y = b_var (2+i+i+i)%nat *)
  end.

Eval simpl in n_adder_sum_bexp 3 3.
Eval simpl in n_adder_sum_bexp 3 2.
Eval simpl in n_adder_sum_bexp 3 1.
Eval simpl in n_adder_sum_bexp 3 0.

Fixpoint increase_vars_by (k : nat) (b : bexp) : bexp :=
  match b with
  | b_t   => b_t
  | b_f   => b_f
  | b_var x => b_var (k + x)%nat
  | b_not b' => b_not (increase_vars_by k b')
  | b_and b1 b2 => b_and (increase_vars_by k b1) (increase_vars_by k b2)
  | b_xor b1 b2 => b_xor (increase_vars_by k b1) (increase_vars_by k b2)
  end.

Lemma bexp_interpret_equiv_1 : forall (k : nat) (b : bexp) (f : Var -> bool),
    ⌈ b | fun x : Var => f (k + x)%nat ⌉
    = ⌈ increase_vars_by k b | f ⌉.
Proof.
  induction b.
  - intros. simpl. reflexivity.
  - intros. simpl. reflexivity.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite IHb. reflexivity.
  - intros. simpl. rewrite IHb1. rewrite IHb2. reflexivity.
  - intros. simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

Lemma n_adder_cout_bexp_equiv_1 : forall (n m : nat),
    (m <= n)%nat ->
    increase_vars_by 3%nat (n_adder_cout_bexp n m) = n_adder_cout_bexp (S n) m.
Proof.
  intros. generalize dependent n.
  induction m.
  - intros. simpl. replace (n + S n + S n)%nat with (2 + n + n + n)%nat by omega.
    reflexivity.
  - intros. simpl. rewrite IHm.
    remember (n - S m)%nat as i.
    replace (n - m)%nat with (1 + i)%nat by omega. simpl.
    replace (i + S i + S i)%nat with (2 + i + i + i)%nat by omega. simpl.
    reflexivity.
    omega.
Qed.

Lemma n_adder_sum_bexp_equiv_1 : forall (n m : nat),
    (m <= n)%nat ->
    increase_vars_by 3%nat (n_adder_sum_bexp n m) = n_adder_sum_bexp (S n) m.
Proof.
  intros. generalize dependent n.
  induction m.
  - intros. simpl. replace (n + S n + S n)%nat with (2 + n + n + n)%nat by omega.
    reflexivity.
  - intros. simpl. rewrite n_adder_cout_bexp_equiv_1.
    remember (n - S m)%nat as i.
    replace (n - m)%nat with (1 + i)%nat by omega. simpl.
    replace (i + S i + S i)%nat with (2 + i + i + i)%nat by omega. simpl.
    reflexivity.
    omega.
Qed.

(* compute_adder_n_left
   : Functional meaning of [adder_circ_n_left]
     Input  (list of bools of length 3n+1) : [z0 y0 x0 z1 y1 x1 ... zn yn xn cin]
     Output (list of bools of length 4n+1) : [c0 z0 y0 x0 c1 z1 y1 x1 ... cn zn yn xn cin]
*)
Fixpoint compute_adder_n_left (n : nat) (f : Var -> bool) : Var -> bool :=
  match n with
  | 0 => f
  | S n' =>
    (fun x => match x with
              | 0 => ⌈ n_adder_cout_bexp n n |
              (fun i => match i with
                        | 0 => false
                        | S i' => f i'
                        end) ⌉
              | 1 => (f 0) ⊕ ⌈ n_adder_sum_bexp n n |
              (fun i => match i with
                        | 0 => false
                        | S i' => f i'
                        end) ⌉
              | 2 => f 1
              | 3 => f 2
              | S (S (S (S x'))) => (compute_adder_n_left n' (fun i => f (3 + i))) x'
              end)
  end.

Definition compute_adder_n_left_inp_1 := (fun (x : Var) =>
                     match x with
                     | 0 => false
                     | 1 => true
                     | 2 => true
                     | 3 => true
                     | _ => false
                     end).
Eval compute in compute_adder_n_left 1 compute_adder_n_left_inp_1.

Lemma adder_circ_n_spec_left_1 : forall (n : nat) (f : Var -> bool),
    let l1 := list_of_Qubits (1 + 3 * n) in
    let l2 := list_of_Qubits (1 + 4 * n) in
    ⟦adder_circ_n_left n⟧ (ctx_to_matrix l1 f)
    = (ctx_to_matrix l2 (compute_adder_n_left n f)).
Proof.
  induction n.
  - intros. unfold ctx_to_matrix. simpl.
    remember id_circ_spec. simpl in *. apply e.
    rewrite kron_1_r. apply WF_bool_to_matrix.
  - intros. unfold list_of_Qubits in *.
    Opaque compute_adder_n_left.
    unfold adder_circ_n_left. unfold adder_circ_n_left in IHn.
    Set Printing Implicit. show_dimensions. simpl_eq.
    specialize inSeq_correct as IS. simpl in IS. rewrite IS. clear IS.
    + unfold compose_super.
      simpl_eq. program_simpl.
      replace (n + S (n + S (n + S (n + 0)))) with (3 + (n + (n + (n + (n + 0))))) by omega.
      specialize inSeq_correct as IS. simpl in IS. rewrite IS. clear IS.
      * unfold compose_super. simpl_eq. program_simpl.
        replace (ctx_to_matrix l1 f) with (bool_to_matrix (f 0) ⊗ ctx_to_matrix (list_of_Qubits (3 + 3*n)) (fun x => f (S x))).
        { simpl. Set Printing All.
          rewrite dim_eq_lemma_1.
          specialize (inPar_correct
                        Qubit Qubit
                        (Tensor Qubit (Tensor Qubit (Tensor Qubit (NTensor (n + (n + (n + 0))) Qubit))))
                        (Tensor Qubit (Tensor Qubit (Tensor Qubit (NTensor (n + (n + (n + (n + 0)))) Qubit)))))
            as IP.
          simpl in IP. rewrite dim_eq_lemma_3 in IP.
          unfold list_of_Qubits. unfold ctx_to_matrix. simpl.
          rewrite dim_eq_lemma_2. rewrite dim_eq_lemma_1. rewrite IP. clear IP.
          - specialize (inPar_correct
                          Qubit Qubit
                          (Tensor Qubit (Tensor Qubit (NTensor (n + (n + (n + 0))) Qubit)))
                          (Tensor Qubit (Tensor Qubit (NTensor (n + (n + (n + (n + 0)))) Qubit))))
              as IP.
            simpl in IP. rewrite dim_eq_lemma_3 in IP.
            rewrite dim_eq_lemma_2. rewrite IP. clear IP.
            + specialize (inPar_correct
                            Qubit Qubit
                            (Tensor Qubit (NTensor (n + (n + (n + 0))) Qubit))
                            (Tensor Qubit (NTensor (n + (n + (n + (n + 0)))) Qubit)))
                as IP.
              simpl in IP. rewrite dim_eq_lemma_3 in IP.
              rewrite IP. clear IP.
              * replace (@kron
                           (S (S O)) (S (S O))
                           (Nat.pow (S (S O))
                                    (Init.Nat.add n (Init.Nat.add n (Init.Nat.add n O))))
                           (Nat.pow (S (S O))
                                    (Init.Nat.add n (Init.Nat.add n (Init.Nat.add n O))))
                           (bool_to_matrix (f 3))
                           (big_kron (ctx_to_mat_list (repeat (Some Qubit) (n + (n + (n + 0)))) (fun v : Var => f (S (S (S (S v)))))))) with
                    (ctx_to_matrix (repeat (Some Qubit) (1 + 3 * n)) (fun v : Var => f (S (S (S v))))).
                { simpl in *. rewrite IHn. clear IHn.
                  Unset Printing All. Unset Printing Implicit.
                  specialize id_circ_spec as Iid. simpl in Iid. repeat rewrite Iid. clear Iid.
                  Locate "⊗".
                  - rewrite strip_one_l_in_eq.
                    specialize (kron_1_l
                                  (2 * (2 * (2 * 2 ^ ⟦ Some Qubit :: repeat (Some Qubit) (n + (n + (n + (n + 0)))) ⟧)))
                                  (2 * (2 * (2 * 2 ^ ⟦ Some Qubit :: repeat (Some Qubit) (n + (n + (n + (n + 0)))) ⟧)))
                                  (bool_to_matrix (f 0) ⊗ (bool_to_matrix (f 1) ⊗ (bool_to_matrix (f 2) ⊗ ctx_to_matrix (Some Qubit :: repeat (Some Qubit) (n + (n + (n + (n + 0))))) (compute_adder_n_left n (fun v : Var => f (S (S (S v))))))))) as IK.
                    simpl in IK.
                    Set Printing All. rewrite dim_eq_lemma_1 in IK. rewrite dim_eq_lemma_3.
                    rewrite <- IK. Unset Printing All. clear IK.
                    + Set Printing Implicit. Check inPar_correct.
                      replace (n + S (n + S (n + S (n + 0)))) with (3 + (n + (n + (n + (n + 0))))) by omega.
                      simpl.
                      specialize (inPar_correct
                                    One Qubit
                                    (Tensor Qubit (NTensor (3 + (n + (n + (n + (n + 0))))) Qubit))
                                    (Tensor Qubit (NTensor (3 + (n + (n + (n + (n + 0))))) Qubit))
                                    init0 id_circ)
                        as IP.
                      simpl in IP. rewrite dim_eq_lemma_3 in IP.
                      rewrite dim_eq_lemma_2. rewrite IP. clear IP.
                      Unset Printing Implicit.
                      * specialize init0_spec as IG. simpl in IG. rewrite IG. clear IG.
                        specialize id_circ_spec as Iid. simpl in Iid. rewrite Iid. clear Iid.
                        { Check adder_circ_1_with_pads_spec.
                          Set Printing Implicit.
                          specialize (adder_circ_1_with_pads_spec
                                        (n + (n + (n + (n + 0))))
                                        (fun x => match x with
                                                  | 0 => false
                                                  | 1 => f 0
                                                  | 2 => f 1
                                                  | 3 => f 2
                                                  | S (S (S (S x'))) => (compute_adder_n_left n (fun v : Var => f (S (S (S v))))) x'
                                                  end))
                            as IA. unfold ctx_to_matrix in IA. simpl in IA.
                          unfold ctx_to_matrix. simpl. Set Printing All.
                          unfold NTensor in IA. unfold NTensor.
                          rewrite dim_eq_lemma_1 in IA. rewrite dim_eq_lemma_2 in IA.
                          rewrite dim_eq_lemma_2. rewrite IA. clear IA. Unset Printing All.
                          repeat apply kron_eq_1.
                          - clear l1. clear l2.
                            Transparent compute_adder_n_left. simpl.
                            replace (n - n + (n - n) + (n - n)) with 0 by omega.
                            rewrite <- n_adder_cout_bexp_equiv_1; try apply Nat.le_refl.
                            rewrite <- bexp_interpret_equiv_1.
                            destruct n.
                            + simpl. remember ((f 3 && f 2 ⊕ f 1) ⊕ (f 2 && f 1)).
                              destruct b; reflexivity.
                            + simpl.
                              replace (n - n + (n - n) + (n - n)) with 0 by omega.
                              rewrite <- n_adder_cout_bexp_equiv_1; try apply Nat.le_refl.
                              rewrite <- bexp_interpret_equiv_1.
                              rewrite <- bexp_interpret_equiv_1.
                              simpl.
                              remember (((⌈ n_adder_cout_bexp n n |
                                          fun x : Var => f (S (S (S (S (S x))))) ⌉
                                                           && f 5 ⊕ f 4)
                                           ⊕ (f 5 && f 4) && f 2 ⊕ f 1) ⊕ (f 2 && f 1)).
                              destruct b; reflexivity.
                          - clear l1. clear l2.
                            Transparent compute_adder_n_left. simpl.
                            replace (n - n + (n - n) + (n - n)) with 0 by omega.
                            rewrite <- n_adder_cout_bexp_equiv_1; try apply Nat.le_refl.
                            rewrite <- bexp_interpret_equiv_1.
                            destruct n.
                            + simpl. reflexivity.
                            + simpl. replace (n - n + (n - n) + (n - n)) with 0 by omega.
                              rewrite <- n_adder_cout_bexp_equiv_1; try apply Nat.le_refl.
                              rewrite <- bexp_interpret_equiv_1.
                              rewrite <- bexp_interpret_equiv_1.
                              simpl. reflexivity.
                          - simpl. reflexivity.
                          - simpl. reflexivity.
                          - simpl. reflexivity.
                          - simpl. reflexivity.
                        }
                        clear l1. clear l2.
                        apply WF_kron; simpl; try rewrite dim_eq_lemma_3; try reflexivity; try apply WF_bool_to_matrix.
                        apply WF_kron; simpl; try rewrite dim_eq_lemma_3; try reflexivity; try apply WF_bool_to_matrix.
                        apply WF_kron; simpl; try rewrite dim_eq_lemma_3; try reflexivity; try apply WF_bool_to_matrix.
                        specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0)))))) as IW.
                        simpl in IW. rewrite dim_eq_lemma_1 in IW. apply IW.
                      * apply (init_WT false).
                      * apply id_circ_WT.
                      * auto with wf_db.
                      * apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                        apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                        apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                        specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0)))))) as IW.
                        simpl in IW. rewrite dim_eq_lemma_1 in IW. apply IW.
                    + apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                      apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                      apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                      specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0)))))) as IW.
                      simpl in IW. rewrite dim_eq_lemma_1 in IW. apply IW.
                  - apply WF_bool_to_matrix.
                  - apply WF_bool_to_matrix.
                  - apply WF_bool_to_matrix.
                }
                { unfold ctx_to_matrix. simpl. rewrite dim_eq_lemma_2. reflexivity. }
              * apply id_circ_WT.
              * apply adder_circ_n_left_WT.
              * apply WF_bool_to_matrix.
              * specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + 0)))) (fun x => f (S (S (S x))))) as IW.
                unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW.
            + apply id_circ_WT.
            + repeat apply inPar_WT; try apply id_circ_WT; try apply adder_circ_n_left_WT.
            + apply WF_bool_to_matrix.
            + apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
              specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + 0)))) (fun x => f (S (S (S x))))) as IW.
              unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW.
          - apply id_circ_WT.
          - repeat apply inPar_WT; try apply id_circ_WT; try apply adder_circ_n_left_WT.
          - apply WF_bool_to_matrix.
          - apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
            apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
            specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + 0)))) (fun x => f (S (S (S x))))) as IW.
            unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW.
        }
        { unfold ctx_to_matrix. simpl.
          replace (n + S (n + S (n + 0))) with (2 + (n + (n + (n + 0)))) by omega.
          simpl. rewrite dim_eq_lemma_2. rewrite dim_eq_lemma_1. reflexivity. }
      * simpl_eq. apply adder_circ_1_with_pads_WT.
      * apply strip_one_l_in_WT. apply inPar_WT; [apply (init_WT false) | apply id_circ_WT].
    + simpl_eq. apply inSeq_WT.
      * apply strip_one_l_in_WT. apply inPar_WT; [apply (init_WT false) | apply id_circ_WT].
      * simpl_eq. apply adder_circ_1_with_pads_WT.
    + repeat (apply inPar_WT; try apply id_circ_WT). apply adder_circ_n_left_WT.
Qed.



(* compute_adder_n_right
   : Functional meaning of [adder_circ_n_right]
     Input  (list of bools of length 4n+1) : [c0 z0 y0 x0 c1 z1 y1 x1 ... cn zn yn xn cin]
     Output (list of bools of length 3n+1) : [z0 y0 x0 z1 y1 x1 ... zn yn xn cin]
*)
Fixpoint compute_adder_n_right (n : nat) (f : Var -> bool) : Var -> bool :=
  match n with
  | 0 => f
  | S n' =>
    (fun x => match x with
              | 0 => f 1
              | 1 => f 2
              | 2 => f 3
              | S (S (S x')) => (compute_adder_n_right n' (fun i => f (4 + i))) x'
              end)
  end.

Definition compute_adder_n_right_inp_1 := (fun (x : Var) =>
                     match x with
                     | 0 => true
                     | 1 => true
                     | 2 => true
                     | 3 => true
                     | 4 => true
                     | _ => false
                     end).
Eval compute in compute_adder_n_right 1 compute_adder_n_right_inp_1.

Lemma adder_circ_n_spec_right_1 : forall (n : nat) (f : Var -> bool),
    let l1 := list_of_Qubits (1 + 4 * n) in
    let l2 := list_of_Qubits (1 + 3 * n) in
    ⟦adder_circ_n_right n⟧
      (ctx_to_matrix
         l1
         (fun x =>
            match x with
            | 0 => (compute_adder_n_left n (fun v : Var => f (S (S (S (S v))))) 0)
            | S x' =>
              (fun v : Var =>
                 compute_adder_n_left n (fun v0 : Var => f (S (S (S (S v0))))) (S v)) x'
            end))
    = (ctx_to_matrix
         l2 (compute_adder_n_right
               n
               (fun x =>
                  match x with
                  | 0 => (compute_adder_n_left n (fun v : Var => f (S (S (S (S v))))) 0)
                  | S x' =>
                    (fun v : Var =>
                       compute_adder_n_left n (fun v0 : Var => f (S (S (S (S v0))))) (S v)) x'
                  end))).
Proof.
  induction n.
  - intros. simpl.
    specialize id_circ_spec as Iid. simpl in Iid. repeat rewrite Iid. clear Iid. reflexivity.
    apply WF_kron; try reflexivity; try apply WF_bool_to_matrix; try apply WF_I.
  - intros. simpl_eq.
    replace (n - n + (n - n) + (n - n)) with 0 in * by omega.
    specialize inSeq_correct as IS. simpl in IS. rewrite IS. clear IS.
    + unfold compose_super. simpl_eq.
      specialize inSeq_correct as IS. simpl in IS. rewrite IS. clear IS.
      * unfold compose_super. simpl_eq.
        specialize (carrier_circ_1_with_pads_spec
                      (n + (n + (n + (n + 0))))
                      (fun x => match x with
                                | 0 => ((⌈ n_adder_cout_bexp (S n) n
                                        | fun i : Var => match i with
                                                         | 0 => false
                                                         | S i' => f (S (S (S (S i'))))
                                                         end ⌉ && f 6 ⊕ f 5) ⊕ (f 6 && f 5))
                                | 1 => (f 4
                                          ⊕ (⌈ n_adder_cout_bexp (S n) n
                                            | fun i : Var =>
                                                match i with
                                                | 0 => false
                                                | S i' => f (S (S (S (S i'))))
                                                end ⌉ ⊕ (f 6 ⊕ f 5)))
                                | S (S x') => (fun v : Var =>
                                                 match v with
                                                 | 0 => f 5
                                                 | 1 => f 6
                                                 | S (S v') =>
                                                   compute_adder_n_left n
                                                                        (fun i : Var => f (S (S (S (S (S (S (S i)))))))) v'
                                                 end) x'
                                end)) as H.
        unfold ctx_to_matrix in *. simpl in *.
        replace (n + S (n + S (n + S (n + 0)))) with (3 + n + (n + (n + (n + 0)))) by omega.
        simpl. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *.
        rewrite H. clear H.

        rewrite strip_one_l_out_eq.

        specialize (inPar_correct
                      Qubit One
                      (NTensor (4 + n + (n + (n + (n + 0)))) Qubit)
                      (NTensor (4 + n + (n + (n + (n + 0)))) Qubit))
          as IP.
        simpl in IP. rewrite dim_eq_lemma_3 in *. rewrite dim_eq_lemma_2 in *.
        rewrite IP. clear IP.

        { rewrite <- n_adder_cout_bexp_equiv_1; try apply Nat.le_refl.
          rewrite <- bexp_interpret_equiv_1. simpl.
          assert (H : ⌈ n_adder_cout_bexp n n |
                  fun x : Var => f (S (S (S (S (S (S x)))))) ⌉
                                 = compute_adder_n_left n (fun i : Var => f (S (S (S (S (S (S (S i)))))))) 0).
          { destruct n.
            - simpl. reflexivity.
            - simpl. replace (n - n + (n - n) + (n - n)) with 0 by omega.
              rewrite <- n_adder_cout_bexp_equiv_1; try apply Nat.le_refl.
              rewrite <- bexp_interpret_equiv_1.
              rewrite <- bexp_interpret_equiv_1.
              simpl. reflexivity. }
          rewrite H. clear H.
          remember ((compute_adder_n_left n (fun i : Var => f (S (S (S (S (S (S (S i)))))))) 0 && f 6 ⊕ f 5) ⊕ (f 6 && f 5)).
          rewrite xorb_nilpotent. clear b Heqb. simpl.
          specialize assert0_spec as IA. simpl in IA. rewrite IA. clear IA.

          rewrite kron_1_l.
          - specialize id_circ_spec as Iid. simpl in Iid. repeat rewrite Iid. clear Iid.
            + specialize (inPar_correct
                            Qubit Qubit
                            (NTensor (3 + n + (n + (n + (n + 0)))) Qubit)
                            (NTensor (3 + n + (n + (n + 0))) Qubit))
                as IP.
              simpl in IP. rewrite dim_eq_lemma_3 in *.
              rewrite IP. clear IP.
              * specialize (inPar_correct
                              Qubit Qubit
                              (NTensor (2 + n + (n + (n + (n + 0)))) Qubit)
                              (NTensor (2 + n + (n + (n + 0))) Qubit))
                  as IP.
                simpl in IP. rewrite dim_eq_lemma_3 in *.
                rewrite IP. clear IP.
                { specialize (inPar_correct
                                Qubit Qubit
                                (NTensor (1 + n + (n + (n + (n + 0)))) Qubit)
                                (NTensor (1 + n + (n + (n + 0))) Qubit))
                    as IP.
                  simpl in IP. rewrite dim_eq_lemma_3 in *.
                  rewrite IP. clear IP.
                  - specialize id_circ_spec as Iid. simpl in Iid. repeat rewrite Iid. clear Iid.
                    + replace (n + S (n + S (n + 0))) with (2 + n + (n + (n + 0))) by omega.
                      simpl. rewrite dim_eq_lemma_3. repeat apply kron_eq_1.
                      * reflexivity.
                      * reflexivity.
                      * rewrite dim_eq_lemma_2. apply kron_eq_1.
                        { reflexivity. }
                        { specialize (IHn (fun i : Var => f (S (S (S i))))) as H.
                          simpl in H. rewrite dim_eq_lemma_2 in H. rewrite H.
                          rewrite dim_eq_lemma_2. apply kron_eq_1.
                          - destruct n.
                            + simpl. reflexivity.
                            + simpl. reflexivity.
                          - destruct n.
                            + simpl. reflexivity.
                            + simpl. reflexivity. }
                    + apply WF_bool_to_matrix.
                    + apply WF_bool_to_matrix.
                    + apply WF_bool_to_matrix.
                  - apply id_circ_WT.
                  - apply adder_circ_n_right_WT.
                  - apply WF_bool_to_matrix.
                  - specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0))))) (compute_adder_n_left n (fun i : Var => f (S (S (S (S (S (S (S i)))))))))) as IW.
                    unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW.
                }
                { apply id_circ_WT. }
                { apply inPar_WT.
                  - apply id_circ_WT.
                  - apply adder_circ_n_right_WT. }
                { apply WF_bool_to_matrix. }
                { apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                  specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0))))) (compute_adder_n_left n (fun i : Var => f (S (S (S (S (S (S (S i)))))))))) as IW.
                  unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW. }
              * apply id_circ_WT.
              * repeat apply inPar_WT; try apply id_circ_WT. apply adder_circ_n_right_WT.
              * apply WF_bool_to_matrix.
              * apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0))))) (compute_adder_n_left n (fun i : Var => f (S (S (S (S (S (S (S i)))))))))) as IW.
                unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW.
            + repeat apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
              * simpl. rewrite dim_eq_lemma_3. reflexivity.
              * simpl. rewrite dim_eq_lemma_3. reflexivity.
              * specialize (WF_ctx_to_matrix (@repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0)))))) as IW. simpl in IW. rewrite dim_eq_lemma_1 in IW. apply IW.
          - specialize id_circ_spec as Iid. simpl in Iid. repeat rewrite Iid. clear Iid.
            repeat apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
            specialize (WF_ctx_to_matrix (@repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0)))))) as IW. simpl in IW. rewrite dim_eq_lemma_1 in IW. apply IW.
            simpl. rewrite dim_eq_lemma_3.
            repeat apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
            specialize (WF_ctx_to_matrix (@repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0)))))) as IW. simpl in IW. rewrite dim_eq_lemma_1 in IW. apply IW.
        }
        { apply (assert_WT false). }
        { apply id_circ_WT. }
        { apply WF_bool_to_matrix. }
        { apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
          apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
          apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
          specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0))))) (compute_adder_n_left n (fun i : Var => f (S (S (S (S (S (S (S i)))))))))) as IW.
          unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW. }
      * simpl_eq. repeat (apply inPar_WT; try apply id_circ_WT).
        apply adder_circ_n_right_WT.
      * apply strip_one_l_out_WT.
        apply inPar_WT; [apply (assert_WT false) | apply id_circ_WT].
    + simpl_eq. apply inSeq_WT.
      * apply strip_one_l_out_WT.
        apply inPar_WT; [apply (assert_WT false) | apply id_circ_WT].
      * simpl_eq. repeat (apply inPar_WT; try apply id_circ_WT).
        apply adder_circ_n_right_WT.
    + apply carrier_circ_1_with_pads_WT.
Qed.

(* compute_adder_n_aux
   : Helper function for defining functional meaning of [adder_circ_n]
     Input  (list of bools of length 3n+1) : [z0 y0 x0 z1 y1 x1 ... zn yn xn cin]
     Output (list of bools of length 3n+1) : [z0 y0 x0 z1 y1 x1 ... zn yn xn cin]
*)
Fixpoint compute_adder_n_aux (n : nat) (f : Var -> bool) : Var -> bool :=
  match n with
  | 0 => f
  | S n' =>
    (fun x => match x with
              | 0 => (f 0) ⊕ ⌈ n_adder_sum_bexp n n |
              (fun i => match i with
                        | 0 => false
                        | S i' => f i'
                        end) ⌉
              | 1 => f 1
              | 2 => f 2
              | S (S (S x')) => (compute_adder_n_aux n' (fun i => f (3 + i))) x'
              end)
  end.
(* compute_adder_n
   : Functional meaning of [adder_circ_n]
     Input  (list of bools of length 3n+2) : [cout z0 y0 x0 z1 y1 x1 ... zn yn xn cin]
     Output (list of bools of length 3n+2) : [cout z0 y0 x0 z1 y1 x1 ... zn yn xn cin]
 *)
Fixpoint compute_adder_n (n : nat) (f : Var -> bool) : Var -> bool :=
  match n with
  | 0 => (fun x => match x with
                   | 0 => (f 0) ⊕ (f 1)
                   | _ => f x
                   end)
  | S n' => (fun x => match x with
                      | 0 => (f 0) ⊕ ⌈ n_adder_cout_bexp n n |
                      (fun i => match i with
                                | 0 => false
                                | S i' => f (S i')
                                end) ⌉
                      | S x' => (compute_adder_n_aux n (fun i => f (S i)) x')
                      end)
  end.

Definition compute_adder_n_inp_1 := (fun (x : Var) =>
                     match x with
                     | 0 => false
                     | 1 => false
                     | 2 => true
                     | 3 => true
                     | 4 => true
                     | _ => false
                     end).
Eval compute in compute_adder_n 1 compute_adder_n_inp_1.

Lemma adder_circ_n_spec : forall (n : nat) (f : Var -> bool),
    let li := list_of_Qubits (2 + 3 * n) in
    ⟦adder_circ_n n⟧ (ctx_to_matrix li f)
    = (ctx_to_matrix li (compute_adder_n n f)).
Proof.
  destruct n.
  - intros. unfold ctx_to_matrix. simpl.
    specialize (calc_id_circ_spec (f 1) (f 0)) as H.
    unfold fun_of_bools in H. unfold bools_to_matrix in H.
    simpl in *. rewrite H. reflexivity.
  - intros. unfold list_of_Qubits in *.
    Opaque compute_adder_n.
    unfold adder_circ_n. simpl_eq.
    unfold list_of_Qubits. unfold ctx_to_matrix. simpl.
    replace (n + S (n + S (n + 0))) with (2 + n + (n + (n + 0))) by omega. simpl.
    specialize inSeq_correct as IS. simpl in IS. rewrite IS. clear IS.
    + unfold compose_super.
      specialize inSeq_correct as IS. simpl in IS. rewrite IS. clear IS.
      * unfold compose_super.
        specialize (inPar_correct
                      Qubit Qubit
                      (NTensor (4 + n + (n + (n + 0))) Qubit)
                      (NTensor (4 + n + (n + (n + (n + 0)))) Qubit))
          as IP.
        simpl in IP. rewrite dim_eq_lemma_3 in IP.
        rewrite dim_eq_lemma_2. rewrite dim_eq_lemma_1. rewrite dim_eq_lemma_2.
        rewrite dim_eq_lemma_3 in IP.
        rewrite IP. clear IP.
        { specialize (inPar_correct
                        Qubit Qubit
                        (NTensor (3 + n + (n + (n + 0))) Qubit)
                        (NTensor (3 + n + (n + (n + (n + 0)))) Qubit))
            as IP.
          simpl in IP. rewrite dim_eq_lemma_3 in IP.
          rewrite dim_eq_lemma_3 in IP.
          rewrite IP. clear IP.
          - specialize (inPar_correct
                          Qubit Qubit
                          (NTensor (2 + n + (n + (n + 0))) Qubit)
                          (NTensor (2 + n + (n + (n + (n + 0)))) Qubit))
              as IP.
            simpl in IP. rewrite dim_eq_lemma_3 in IP.
            rewrite dim_eq_lemma_3 in IP.
            rewrite IP. clear IP.
            + specialize (inPar_correct
                            Qubit Qubit
                            (NTensor (1 + n + (n + (n + 0))) Qubit)
                            (NTensor (1 + n + (n + (n + (n + 0)))) Qubit))
                as IP.
              simpl in IP. rewrite dim_eq_lemma_3 in IP.
              rewrite dim_eq_lemma_3 in IP.
              rewrite IP. clear IP.
              * specialize id_circ_spec as Iid. simpl in Iid. repeat rewrite Iid. clear Iid.
                specialize
                  (adder_circ_n_spec_left_1 n (fun v => f (4 + v))) as H.
                simpl in H. unfold ctx_to_matrix in H. simpl in H.
                rewrite dim_eq_lemma_1 in H. rewrite dim_eq_lemma_2 in H. rewrite H. clear H.
                { simpl. rewrite dim_eq_lemma_2.
                  specialize
                    (adder_circ_1_with_pads_spec
                       (n + (n + (n + (n + 0))))
                       (fun x => match x with
                                 | 0 => f 0
                                 | 1 => f 1
                                 | 2 => f 2
                                 | 3 => f 3
                                 | S (S (S (S x'))) => (compute_adder_n_left n (fun v : Var => f (S (S (S (S v))))) x')
                                 end)) as H.
                  simpl in H. unfold ctx_to_matrix in H. simpl in H.
                  rewrite dim_eq_lemma_1 in H. rewrite dim_eq_lemma_2 in H.
                  rewrite H. clear H.
                  
                  specialize (inPar_correct
                                Qubit Qubit
                                (NTensor (4 + n + (n + (n + (n + 0)))) Qubit)
                                (NTensor (4 + n + (n + (n + 0))) Qubit))
                    as IP.
                  simpl in IP. rewrite dim_eq_lemma_3 in IP.
                  rewrite dim_eq_lemma_3 in IP.
                  rewrite IP. clear IP.
                  - specialize (inPar_correct
                                  Qubit Qubit
                                  (NTensor (3 + n + (n + (n + (n + 0)))) Qubit)
                                  (NTensor (3 + n + (n + (n + 0))) Qubit))
                      as IP.
                    simpl in IP. rewrite dim_eq_lemma_3 in IP.
                    rewrite dim_eq_lemma_3 in IP.
                    rewrite IP. clear IP.
                    + specialize (inPar_correct
                                    Qubit Qubit
                                    (NTensor (2 + n + (n + (n + (n + 0)))) Qubit)
                                    (NTensor (2 + n + (n + (n + 0))) Qubit))
                        as IP.
                      simpl in IP. rewrite dim_eq_lemma_3 in IP.
                      rewrite dim_eq_lemma_3 in IP.
                      rewrite IP. clear IP.
                      * specialize (inPar_correct
                                      Qubit Qubit
                                      (NTensor (1 + n + (n + (n + (n + 0)))) Qubit)
                                      (NTensor (1 + n + (n + (n + 0))) Qubit))
                          as IP.
                        simpl in IP. rewrite dim_eq_lemma_3 in IP.
                        rewrite dim_eq_lemma_3 in IP.
                        rewrite IP. clear IP.
                        { specialize id_circ_spec as Iid. simpl in Iid. repeat rewrite Iid.
                          clear Iid.
                          - repeat apply kron_eq_1.
                            + Transparent compute_adder_n. simpl.
                              destruct n.
                              * simpl. reflexivity.
                              * simpl. replace (match n with
                                                | 0 => S n
                                                | S l => n - l
                                                end) with 1.
                                replace (n - n + (n - n) + (n - n)) with 0 in * by omega.
                                rewrite <- n_adder_cout_bexp_equiv_1; try apply Nat.le_refl.
                                rewrite <- n_adder_cout_bexp_equiv_1; try (apply le_S; apply Nat.le_refl).
                                rewrite <- n_adder_cout_bexp_equiv_1; try apply Nat.le_refl.
                                rewrite <- bexp_interpret_equiv_1.
                                rewrite <- bexp_interpret_equiv_1.
                                rewrite <- bexp_interpret_equiv_1.
                                simpl. reflexivity.
                                induction n; try reflexivity.
                                simpl. apply IHn.
                            + Transparent compute_adder_n. simpl.
                              replace (n - n + (n - n) + (n - n)) with 0 in * by omega.
                              destruct n.
                              * simpl. reflexivity.
                              * simpl. replace (match n with
                                                | 0 => S n
                                                | S l => n - l
                                                end) with 1.
                                replace (n - n + (n - n) + (n - n)) with 0 in * by omega.
                                rewrite <- n_adder_cout_bexp_equiv_1; try apply Nat.le_refl.
                                rewrite <- n_adder_cout_bexp_equiv_1; try (apply le_S; apply Nat.le_refl).
                                rewrite <- n_adder_cout_bexp_equiv_1; try apply Nat.le_refl.
                                rewrite <- bexp_interpret_equiv_1.
                                rewrite <- bexp_interpret_equiv_1.
                                rewrite <- bexp_interpret_equiv_1.
                                simpl. reflexivity.
                                induction n; try reflexivity.
                                simpl. apply IHn.
                            + simpl. reflexivity.
                            + simpl. reflexivity.
                            + clear li.
                              specialize (adder_circ_n_spec_right_1 n f) as H.
                              simpl in H. unfold ctx_to_matrix in H. simpl in H.
                              rewrite dim_eq_lemma_2 in H. rewrite H. clear H.
                              assert (H : forall x : Var,
                                         (compute_adder_n_right
                                            n (fun i : Var =>
                                                 match i with
                                                 | 0 =>
                                                   compute_adder_n_left
                                                     n (fun v : Var => f (S (S (S (S v))))) 0
                                                 | S i' =>
                                                   compute_adder_n_left
                                                     n (fun v0 : Var => f (S (S (S (S v0))))) (S i')
                                                 end) (S x))
                                         = compute_adder_n (S n) f (S (S (S (S (S x)))))).
                              { intros. simpl.
                                assert (L : forall x : Var,
                                           compute_adder_n_right
                                             n (fun i : Var =>
                                                  match i with
                                                  | 0 =>
                                                    compute_adder_n_left
                                                      n (fun v : Var => f (S (S (S (S v))))) 0
                                                  | S i' =>
                                                    compute_adder_n_left
                                                      n (fun v0 : Var =>
                                                           f (S (S (S (S v0))))) (S i')
                                                  end) (S x)
                                           = compute_adder_n_right
                                               n
                                               (compute_adder_n_left
                                               n (fun v0 : Var =>
                                                    f (S (S (S (S v0)))))) (S x)).
                                { unfold compute_adder_n_right.
                                  destruct n.
                                  - reflexivity.
                                  - destruct x0; try reflexivity. }
                                rewrite L. clear L.

                                generalize dependent x. generalize dependent f. induction n.
                                - reflexivity.
                                - intros. simpl.
                                  destruct x; try reflexivity.
                                  destruct x; try reflexivity.
                                  destruct x.
                                  + destruct n.
                                    * reflexivity.
                                    * reflexivity.
                                  + destruct n.
                                    * simpl in *. reflexivity.
                                    * specialize (IHn (fun i => f (S (S (S i))))) as H.
                                      simpl in *. rewrite <- H. clear H. reflexivity.
                              }
                              rewrite dim_eq_lemma_2. apply kron_eq_1.
                              * destruct n; reflexivity.
                              * apply big_kron_eq_1. simpl in *.
                                intros. rewrite H. reflexivity.
                          - apply WF_bool_to_matrix.
                          - apply WF_bool_to_matrix.
                          - apply WF_bool_to_matrix.
                          - apply WF_bool_to_matrix.
                        }
                        { apply id_circ_WT. }
                        { apply adder_circ_n_right_WT. }
                        { apply WF_bool_to_matrix. }
                        { specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0))))) (compute_adder_n_left n (fun i : Var => f (S (S (S (S i))))))) as IW.
                          unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW. }
                      * apply id_circ_WT.
                      * apply inPar_WT; try apply id_circ_WT. apply adder_circ_n_right_WT.
                      * apply WF_bool_to_matrix.
                      * apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                        specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0))))) (compute_adder_n_left n (fun i : Var => f (S (S (S (S i))))))) as IW.
                        unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW.
                    + apply id_circ_WT.
                    + repeat apply inPar_WT; try apply id_circ_WT.
                      apply adder_circ_n_right_WT.
                    + apply WF_bool_to_matrix.
                    + apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                      apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                      specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0))))) (compute_adder_n_left n (fun i : Var => f (S (S (S (S i))))))) as IW.
                      unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW.
                  - apply id_circ_WT.
                  - repeat apply inPar_WT; try apply id_circ_WT. apply adder_circ_n_right_WT.
                  - apply WF_bool_to_matrix.
                  - apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                    apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                    apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
                    specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + (n + 0))))) (compute_adder_n_left n (fun i : Var => f (S (S (S (S i))))))) as IW.
                    unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW.
                }
                { apply WF_bool_to_matrix. }
                { apply WF_bool_to_matrix. }
                { apply WF_bool_to_matrix. }
                { apply WF_bool_to_matrix. }
              * apply id_circ_WT.
              * apply adder_circ_n_left_WT.
              * apply WF_bool_to_matrix.
              * specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + 0)))) (fun v : Var => f (S (S (S (S v)))))) as IW.
                unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW.
            + apply id_circ_WT.
            + repeat apply inPar_WT; try apply id_circ_WT. apply adder_circ_n_left_WT.
            + apply WF_bool_to_matrix.
            + apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
              specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + 0)))) (fun v : Var => f (S (S (S (S v)))))) as IW.
              unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW.
          - apply id_circ_WT.
          - repeat apply inPar_WT; try apply id_circ_WT. apply adder_circ_n_left_WT.
          - apply WF_bool_to_matrix.
          - apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
            apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
            specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + 0)))) (fun v : Var => f (S (S (S (S v)))))) as IW.
            unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW.
        }
        { apply id_circ_WT. }
        { repeat apply inPar_WT; try apply id_circ_WT. apply adder_circ_n_left_WT. }
        { apply WF_bool_to_matrix. }
        { apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
          apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
          apply WF_kron; try reflexivity; try apply WF_bool_to_matrix.
          specialize (WF_ctx_to_matrix (@Some WType Qubit :: @repeat (option WType) (@Some WType Qubit) (n + (n + (n + 0)))) (fun v : Var => f (S (S (S (S v)))))) as IW.
          unfold ctx_to_matrix in IW. simpl in IW. rewrite dim_eq_lemma_1 in *. rewrite dim_eq_lemma_2 in *. apply IW.
        }
      * repeat apply inPar_WT; try apply id_circ_WT. apply adder_circ_n_right_WT.
      * apply adder_circ_1_with_pads_WT.
    + apply inSeq_WT.
      * apply adder_circ_1_with_pads_WT.
      * repeat (apply inPar_WT; try apply id_circ_WT).
        apply adder_circ_n_right_WT.
    + repeat (apply inPar_WT; try apply id_circ_WT).
      apply adder_circ_n_left_WT.
Qed.

Close Scope matrix_scope.

Close Scope nat_scope.

Open Scope nat_scope.

(* Unit test : 10100(2) + 11000(2) + 1(2) = 101101(2) *)
Example adder_circ_n_test_10100_11000_1 :
  ⟦adder_circ_n 5⟧ (ctx_to_matrix (list_of_Qubits 17) (list_to_function [false; false; true; true; false; false; true; false; true; false; false; false; false; false; false; false; true] false))
  = (ctx_to_matrix (list_of_Qubits 17) (list_to_function [true; false; true; true; true; false; true; true; true; false; false; false; false; true; false; false; true] false)).
Proof.
  rewrite (adder_circ_n_spec 5).
  apply ctx_to_matrix_eq_1.
  repeat (try destruct x; try reflexivity).
Qed.

(* Unit test : 10100(2) + 11000(2) + 0(2) = 101100(2) *)
Example adder_circ_n_test_10100_11000_0 :
  ⟦adder_circ_n 5⟧ (ctx_to_matrix (list_of_Qubits 17) (list_to_function [false; false; true; true; false; false; true; false; true; false; false; false; false; false; false; false; false] false))
  = (ctx_to_matrix (list_of_Qubits 17) (list_to_function [true; false; true; true; true; false; true; true; true; false; false; false; false; false; false; false; false] false)).
Proof.
  rewrite (adder_circ_n_spec 5).
  apply ctx_to_matrix_eq_1.
  repeat (try destruct x; try reflexivity).
Qed.

(* Unit test : 1010010100(2) + 1100011000(2) + 0(2) = 10110101100(2) *)
Example adder_circ_n_test_1010010100_1100011000_0 :
  ⟦adder_circ_n 10⟧ (ctx_to_matrix (list_of_Qubits 32) (list_to_function [false; false; true; true; false; false; true; false; true; false; false; false; false; false; false; false; false; true; true; false; false; true; false; true; false; false; false; false; false; false; false; false] false))
  = (ctx_to_matrix (list_of_Qubits 32) (list_to_function [true; false; true; true; true; false; true; true; true; false; false; false; false; true; false; false; false; true; true; true; false; true; true; true; false; false; false; false; false; false; false; false] false)).
Proof.
  rewrite (adder_circ_n_spec 10).
  apply ctx_to_matrix_eq_1.
  repeat (try destruct x; try reflexivity).
Qed.

(* Unit test : 10100101001010010100(2) + 11000110001100011000(2) + 0(2) = 
               101101011010110101100(2) *)
Example adder_circ_n_test_10100101001010010100_11000110001100011000_0 :
  ⟦adder_circ_n 20⟧ (ctx_to_matrix (list_of_Qubits 62) (list_to_function [false; false; true; true; false; false; true; false; true; false; false; false; false; false; false; false; false; true; true; false; false; true; false; true; false; false; false; false; false; false; false; false; true; true; false; false; true; false; true; false; false; false; false; false; false; false; false; true; true; false; false; true; false; true; false; false; false; false; false; false; false; false] false))
  = (ctx_to_matrix (list_of_Qubits 62) (list_to_function [true; false; true; true; true; false; true; true; true; false; false; false; false; true; false; false; false; true; true; true; false; true; true; true; false; false; false; false; true; false; false; false; true; true; true; false; true; true; true; false; false; false; false; true; false; false; false; true; true; true; false; true; true; true; false; false; false; false; false; false; false; false] false)).
Proof.
  rewrite (adder_circ_n_spec 20).
  apply ctx_to_matrix_eq_1.
  repeat (try destruct x; try reflexivity).
Qed.

Fixpoint nat_bool_list (n : nat) (i : nat) : list bool :=
  match i with
  | O => (@nil bool)
  | S i' => (Nat.odd n) :: (nat_bool_list (n/2) i')
  end.

Close Scope nat.

Open Scope N_scope.

Fixpoint store_input_bits (x : BinNums.N) (y : BinNums.N) (len : nat) : list bool
  := match len with
     | O => [false]
     | S len' => (store_input_bits (x/2) (y/2) len')
                   ++ [false; (N.odd x); (N.odd y)]
  end.

Fixpoint store_output_bits (sum : BinNums.N) (x : BinNums.N) (y : BinNums.N) (len : nat) : list bool
  := match len with
     | O => [(N.odd sum)]
     | S len' => (store_output_bits (sum/2) (x/2) (y/2) len')
                   ++ [(N.odd sum); (N.odd x); (N.odd y)]
     end.

Definition prepare_n_adder_input (x : BinNums.N) (y : BinNums.N) (cin : bool) (len : nat) :=
  (fun_of_bools ((store_input_bits x y len) ++ [cin])).

Definition prepare_n_adder_output (sum : BinNums.N) (x : BinNums.N) (y : BinNums.N) (cin : bool) (len : nat) :=
  (fun_of_bools ((store_output_bits sum x y len) ++ [cin])).

(* Unit test : 13 + 80 + 0 = 93, length = 9 *)
Example adder_circ_n_test_13_80_false_9 :
  let x := 13 in let y := 80 in let cin := false in let sum := 93 in let len := 9%nat in
  ⟦adder_circ_n len⟧ (ctx_to_matrix (list_of_Qubits (2+3*len)) (prepare_n_adder_input x y cin len))
  = (ctx_to_matrix (list_of_Qubits (2+3*len)) (prepare_n_adder_output sum x y cin len)).
Proof.
  intros.
  rewrite (adder_circ_n_spec len (prepare_n_adder_input x y cin len)).
  apply ctx_to_matrix_eq_1.
  repeat (try destruct x0; try reflexivity).
Qed.

(* Unit test : 1310293 + 8123900 + 0 = 9434193, length = 9 
   buffer overflow! *)
Proposition adder_circ_n_test_1310293_8123900_false_9 :
  let x := 1310293 in let y := 8123900 in
                      let cin := false in let sum := 9434193 in let len := 9%nat in
  ⟦adder_circ_n len⟧ (ctx_to_matrix (list_of_Qubits (2+3*len)) (prepare_n_adder_input x y cin len))
  = (ctx_to_matrix (list_of_Qubits (2+3*len)) (prepare_n_adder_output sum x y cin len)).
Proof.
  intros.
  rewrite (adder_circ_n_spec len (prepare_n_adder_input x y cin len)).
  apply ctx_to_matrix_eq_1.
  repeat (try destruct x0; try reflexivity).
Abort.

(* Unit test : 1310293 + 8123900 + 0 = 9434193, length = 32 *)
Example adder_circ_n_test_1310293_8123900_false_32 :
  let x := 1310293 in let y := 8123900 in
                      let cin := false in let sum := 9434193 in let len := 32%nat in
  ⟦adder_circ_n len⟧ (ctx_to_matrix (list_of_Qubits (2+3*len)) (prepare_n_adder_input x y cin len))
  = (ctx_to_matrix (list_of_Qubits (2+3*len)) (prepare_n_adder_output sum x y cin len)).
Proof.
  intros.
  rewrite (adder_circ_n_spec len (prepare_n_adder_input x y cin len)).
  apply ctx_to_matrix_eq_1.
  repeat (try destruct x0; try reflexivity).
Qed.

(* Unit test : 1310293123487 + 8112873462390 + 0 = 9423166585877, length = 64 *)
Example adder_circ_n_test_1310293123487_8112873462390_false_64 :
  let x := 1310293123487 in let y := 8112873462390 in
                      let cin := false in let sum := 9423166585877 in let len := 64%nat in
  ⟦adder_circ_n len⟧ (ctx_to_matrix (list_of_Qubits (2+3*len)) (prepare_n_adder_input x y cin len))
  = (ctx_to_matrix (list_of_Qubits (2+3*len)) (prepare_n_adder_output sum x y cin len)).
Proof.
  intros.
  rewrite (adder_circ_n_spec len (prepare_n_adder_input x y cin len)).
  apply ctx_to_matrix_eq_1.
  repeat (try destruct x0; try reflexivity).
Qed.
