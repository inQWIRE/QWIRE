Require Import Program. 
Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Psatz.
Require Import Omega.
Require Import Coq.Strings.String.
Require Import List.
Require Import Bool.
Import ListNotations.

Open Scope R_scope.
Open Scope C_scope.
Open Scope nat_scope.

Bind Scope R_scope with R.
Bind Scope C_scope with C.
Bind Scope nat_scope with nat.

(** Useful C stuff *)

Notation C0 := (RtoC 0). 
Notation C1 := (RtoC 1).
Notation "√ n" := (sqrt n) (at level 20).

Lemma c_proj_eq : forall (c1 c2 : C), fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.  
Proof. intros c1 c2 H1 H2. destruct c1, c2. simpl in *. subst. reflexivity. Qed.

Ltac clra := eapply c_proj_eq; simpl; lra.

(** Matrix Definitions **)

Record Matrix := Mat { dim_x : nat
                     ; dim_y : nat
                     ; entry : nat -> nat -> C
                     }
.
Definition Pos x := x <> 0. Hint Unfold Pos.
Record WF_Matrix x y (A : Matrix) : Prop := WF_Mat 
    { wf_dim_x : dim_x A = x
    ; wf_dim_y : dim_y A = y
    ; pos_x    : Pos x
    ; pos_y    : Pos y
    ; wf_entry : forall x y, x >= dim_x A \/ y >= dim_y A -> entry A x y = C0
    }.

Record Matrix_Equiv (A B : Matrix) : Prop := Mat_Equiv
    { equiv_dim_x : dim_x A = dim_x B
    ; equiv_dim_y : dim_y A = dim_y B
    ; equiv_entry : forall x y, x < dim_x A -> y < dim_y A ->
                    entry A x y = entry B x y }.

Record WF_Matrix_Equiv m n (A B : Matrix) := WF_Mat_Equiv
    { wf_equiv_1 : WF_Matrix m n A 
    ; wf_equiv_2 : WF_Matrix m n B
    ; wf_equiv   : Matrix_Equiv A B }.

Ltac prep_matrix_hypotheses :=
  repeat (match goal with
  | [ H : WF_Matrix _ _ ?A |- _ ]       => destruct H
  | [ H : Matrix_Equiv _ _ |- _ ]       => destruct H
  | [ H : WF_Matrix_Equiv _ _ _ _ |- _ ]=> destruct H
(*  | [ H : WF_Dimension _ _ |- _ ]       => destruct H *)
  | [ A : Matrix |- _ ]                 => destruct A
  end; simpl in *); subst.
Ltac prep_matrix_equality :=
  let i := fresh "i" in 
  let j := fresh "j" in 
  f_equal; simpl in *; try omega;
  unfold dim_x in *; simpl in *;
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.

Lemma matrix_equiv_eq : forall m n A B, WF_Matrix_Equiv m n A B -> A = B.
Proof. 
  intros. 
  prep_matrix_hypotheses.  
  prep_matrix_equality.
  destruct (lt_dec i m); [|rewrite wf_entry1, wf_entry0; auto; omega].
  destruct (lt_dec j n); [|rewrite wf_entry1, wf_entry0; auto; omega].  
  auto.
Qed.

    
Definition list2D_to_matrix (l : list (list R)) : Matrix :=
  Mat (length l) (length (hd [] l))
  (fun x y => nth y (nth x l []) 0%R).

Definition M23 : Matrix := Mat 2 3
  (fun x y => 
  match (x, y) with
  | (0, 0) => 1%R
  | (0, 1) => 2%R
  | (0, 2) => 3%R
  | (1, 0) => 4%R
  | (1, 1) => 5%R
  | (1, 2) => 6%R
  | _ => C0
  end).

Definition M23' : Matrix :=
  list2D_to_matrix  
   ([[1; 2; 3];
     [4; 5; 6]])%R. 
(*Eval compute in M23'.*)

Lemma M23eq : M23 = M23'.
Proof.
  unfold M23'.
  compute.
  prep_matrix_equality.
  do 4 (try destruct i; try destruct j; simpl; trivial).
Qed.

(** Operands and Operations **)

Definition Zero m n : Matrix:= Mat m n (fun x y => 0%R).

Definition Id (n : nat) := Mat n n
  (fun x y => if (x =? y) && (x <? n) then C1 else C0).

(* sum to n exclusive *)
Fixpoint Csum_to_n (f : nat -> C) (n : nat) : C := 
  match n with
  | 0 => C0
  | S n' => (Csum_to_n f n' +  f n')%C
  end.

Definition matrix_op (f : (nat -> nat -> C)) (A : Matrix) 
         : Matrix :=
  Mat (dim_x A) (dim_y A) f.

(* Input: A a square matrix
 *)
Definition trace (A : Matrix) : C := 
  Csum_to_n (fun x => entry A x x) (dim_x A).

Definition scale (r : C) (A : Matrix) : Matrix :=
  matrix_op (fun x y => r * entry A x y)%C A.

(* Input: A is a  1×n matrix
 *        B is an n×1 matrix 
 *)
Definition dot (A B : Matrix) : C :=
  let n := dim_y A in
  Csum_to_n (fun x => entry A O x  * entry B x O)%C n.

(* Input: A and B should be dimensions of the same size 
 * Output: matrix of the same dimensions as A and B 
 *)
Definition Mplus (A B : Matrix) : Matrix :=
  Mat (dim_x A) (dim_y A) (fun x y => (entry A x y + entry B x y)%C).

(* Input: A is an m×n matrix
 *        B is an n×o matrix
 * Output: m×o matrix
 *)
Definition Mmult (A B : Matrix) : Matrix :=
  Mat (dim_x A) (dim_y B) 
  (fun x z => Csum_to_n (fun y => entry A x y * entry B y z)%C (dim_x B)).


(* Only well-defined when o and p are non-zero *)
(* Input: A an m×n matrix
 *        B an o×p matrix
 *        such that o,p ≠ 0
 * Output: an (m*o)×(n*p) matrix
 *)
Definition kron (A B : Matrix) : Matrix :=
  let m := dim_x A in
  let n := dim_y A in
  let o := dim_x B in
  let p := dim_y B in
  Mat (m*o) (n*p)
  (fun x y => Cmult (entry A (x / o) (y / p)) (entry B (x mod o) (y mod p))).

(* Input: an m×n matrix
   Output: an n×m matrix
 *)
Definition transpose (A : Matrix) : Matrix :=
  Mat (dim_y A) (dim_x A) (fun x y => entry A y x).

(* Input: an m×n matrix
   Output: an n×m matrix
 *)
Definition conj_transpose (A : Matrix) : Matrix :=
  Mat (dim_y A) (dim_x A) (fun x y => Cconj (entry A y x)).


Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Infix ".+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix ".*" := scale (at level 40, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Infix "≡" := Matrix_Equiv (at level 100) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope. 
Notation "A †" := (conj_transpose A) (at level 0) : matrix_scope. 
Notation "Σ^ n f" := (Csum_to_n f n) (at level 90) : matrix_scope.
Open Scope matrix_scope.

(** Matrix Tactics **)

(* Would rather use something more basic than lra - but fourier and ring 
   aren't always up to the task *)
Ltac Rsimpl := 
  simpl;
  unfold Rminus;
  unfold Rdiv;
  repeat (
    try rewrite Ropp_0;
    try rewrite Ropp_involutive;
    try rewrite Rplus_0_l;
    try rewrite Rplus_0_r;
    try rewrite Rmult_0_l;
    try rewrite Rmult_0_r;
    try rewrite Rmult_1_l;
    try rewrite Rmult_1_r;
    try rewrite <- Ropp_mult_distr_l;
    try rewrite <- Ropp_mult_distr_r;
    try (rewrite Rinv_l; [|lra]);
    try (rewrite Rinv_r; [|lra]);
    try (rewrite sqrt_sqrt; [|lra])        
).

(* Seems like this could loop forever *)
Ltac group_radicals := 
  repeat (
  match goal with
    | [ |- context[(?r1 * √ ?r2)%R] ] => rewrite (Rmult_comm r1 (√r2)) 
    | [ |- context[(?r1 * (√ ?r2 * ?r3))%R] ] => rewrite <- (Rmult_assoc _ (√ r2) _)
    | [ |- context[((√?r * ?r1) + (√?r * ?r2))%R ] ] => 
        rewrite <- (Rmult_plus_distr_l r r1 r2)
  end).

Ltac Rsolve := repeat (try Rsimpl; try group_radicals); lra.

Ltac Csolve := eapply c_proj_eq; simpl; Rsolve.

(* I'd like a version of this that makes progress even if it doesn't succeed *)
Ltac Msolve := 
  compute;
  repeat match goal with 
  | [ |- (fun _ => _) = (fun _ => _) ]  => let x := fresh "x" in 
                                           apply functional_extensionality; intros x
  | [ |- _ = _ ]                        => Csolve 
  | [ x : nat |- _ ]                    => destruct x (* I'd rather bound this *)
  end.



(** Well-Formedness **)

Lemma WF_Zero : forall m n, Pos m -> Pos n -> WF_Matrix m n (Zero m n).
Proof. intros. constructor; auto. Qed.

Lemma WF_Id : forall n, Pos n -> WF_Matrix n n (Id n). 
Proof. 
  intros. constructor; auto.
  intros x y [H1 | H2]; simpl in *.
  + replace (x <? n) with false by (symmetry; rewrite Nat.ltb_nlt; omega).
    destruct (x =? y); simpl; reflexivity.
  + destruct (x =? y) eqn:Eq.
    - apply Nat.eqb_eq in Eq; subst.
      replace (y <? n) with false by (symmetry; rewrite Nat.ltb_nlt; omega).
      reflexivity.
    - reflexivity.
Qed.


Lemma pos_plus_l : forall m n, Pos m -> Pos (m + n).
Proof.
  destruct m; intros; simpl; auto.
Qed.
Lemma pos_plus_r : forall m n, Pos n -> Pos (m + n).
Proof.
  intros. rewrite plus_comm. apply pos_plus_l. auto.
Qed.

Lemma pos_plus : forall m n, Pos m \/ Pos n -> Pos (m + n).
Proof.
  destruct 1; [apply pos_plus_l | apply pos_plus_r]; auto.
Qed.

Lemma pos_mult : forall m n, Pos m -> Pos n -> Pos (m*n).
Proof.
  destruct m; intros; simpl.
  - contradiction.
  - apply pos_plus_l; auto.
Qed.

Lemma pos_pow : forall m n, Pos m -> Pos (m ^ n).
Proof.
  unfold Pos.
  intros; induction n; simpl; [intuition | ]. 
  apply Nat.neq_mul_0; split; omega.
Qed.



Ltac solve_pos := 
  repeat match goal with
  | [ H : WF_Matrix ?m _ _ |- Pos ?m ] => apply (pos_x _ _ _ H)
  | [ H : WF_Matrix _ ?m _ |- Pos ?m ] => apply (pos_y _ _ _ H)
  | [ |- Pos (_ * _) ] => apply pos_mult
  | [ H : Pos ?m |- Pos (?m + ?n) ] => apply pos_plus_l
  | [ H : Pos ?n |- Pos (?m + ?n) ] => apply pos_plus_r
  | [ |- Pos (?m + ?n) ] => apply pos_plus
  | [ |- ?m <> 0 ] => change (m <> 0) with (Pos m)
  | [ |- Pos (_ ^ _) ] => apply pos_pow
  | [ |- Pos (S _) ]   => inversion 1
  | [ |- Pos _ \/ Pos _ ] => (left; solve_pos; fail) || (right; solve_pos; fail)
  end.

Ltac rewrite_wf_matrix A :=
  match goal with
  | [ H : WF_Matrix _ _ A |- context[entry A _ _] ] => 
    rewrite (wf_entry _ _ _ H); auto
  | [ H : WF_Matrix ?m ?n A |- context[dim_x A] ] => rewrite (wf_dim_x _ _ _ H); auto
  | [ H : WF_Matrix ?m ?n A |- context[dim_y A] ] => rewrite (wf_dim_y _ _ _ H); auto
  end.
Ltac rewrite_all_wf_matrix :=
  repeat (intros; match goal with
  | [ H : WF_Matrix _ _ ?A |- context[entry ?A _ _] ] => 
    rewrite (wf_entry _ _ _ H) in *; auto
  | [ H : WF_Matrix _ _ ?A , G : context[entry ?A _ _] |- _ ] => 
    rewrite (wf_entry _ _ _ H) in *; auto
  | [ H : WF_Matrix ?m ?n ?A |- context[dim_x ?A] ] => 
    rewrite (wf_dim_x _ _ _ H) in *; auto
  | [ H : WF_Matrix _ _ ?A , G : context[dim_x ?A] |- _ ] => 
    rewrite (wf_dim_x _ _ _ H) in *; auto
  | [ H : WF_Matrix ?m ?n ?A |- context[dim_y ?A] ] => 
    rewrite (wf_dim_y _ _ _ H) in *; auto
  | [ H : WF_Matrix _ _ ?A , G : context[dim_y ?A] |- _ ] => 
    rewrite (wf_dim_y _ _ _ H) in *; auto
  | [ |- Pos _ ] => solve_pos
  end).

Lemma WF_scale : forall {m n : nat} (r : C) (A : Matrix), 
  WF_Matrix m n A -> WF_Matrix m n (scale r A).
Proof.
  intros m n r A H.
  constructor; simpl; try rewrite_all_wf_matrix. 
  clra.
Qed.

Lemma WF_plus : forall {m n} (A B : Matrix), 
  WF_Matrix m n A -> WF_Matrix m n B -> WF_Matrix m n (A .+ B).
Proof.
  intros. 
  constructor; simpl; try rewrite_all_wf_matrix.
  clra. 
Qed.

Lemma WF_mult : forall {m n o : nat} (A B : Matrix),
  WF_Matrix m n A -> WF_Matrix n o B -> WF_Matrix m o (A × B).
Proof.
  intros m n o A B wf_A wf_B.
  constructor; simpl; try rewrite_all_wf_matrix. 
  destruct H.
  + assert (forall y, entry A x y = 0%R) as H' by rewrite_all_wf_matrix.
    clear wf_A wf_B.
    induction n; simpl; auto.
    rewrite IHn; auto. rewrite H'. clra.
  + assert (forall x, entry B x y = 0%R) as H' by rewrite_all_wf_matrix.
    clear wf_A wf_B.
    induction n; simpl; auto. rewrite IHn. rewrite H'. clra.
Qed.

(* Should the non-zero assumptions be here? *)
Lemma WF_kron : forall {m1 m2 m n1 n2 n : nat} A B,
                WF_Matrix m1 n1 A -> WF_Matrix m2 n2 B ->
                m = m1 * m2 -> n = n1 * n2 ->
                WF_Matrix m n (A ⊗ B).
Proof.
  intros; subst.
  constructor; simpl; 
    [rewrite_all_wf_matrix | rewrite_all_wf_matrix | solve_pos | solve_pos | ].
  intros x y [? | ?].
  - rewrite_wf_matrix A; try clra.
    rewrite_all_wf_matrix.
    left. apply Nat.div_le_lower_bound; auto. solve_pos.
    rewrite Nat.mul_comm; assumption.
  - rewrite_wf_matrix A; try clra.
    rewrite_all_wf_matrix.
    right. apply Nat.div_le_lower_bound; auto. solve_pos.
    rewrite Nat.mul_comm; assumption.
Qed. 


Lemma WF_transpose : forall {m n : nat} (A : Matrix), 
                     WF_Matrix m n A -> WF_Matrix n m A⊤. 
Proof. 
  intros. 
  constructor; simpl; auto; rewrite_all_wf_matrix; omega.
Qed.

Lemma WF_conj_transpose : forall {m n : nat} (A : Matrix), 
      WF_Matrix m n A -> WF_Matrix n m A†. 
Proof. 
  intros.
  constructor; simpl; auto; rewrite_all_wf_matrix; [clra | omega].
Qed.


Ltac show_wf_manual :=
  repeat match goal with
  | [ |- WF_Matrix _ _ _ ] => constructor
  | [ |- _ = _ ] => simpl; reflexivity
  | [ |- Pos _ ] => solve_pos
  | [ H : (_ >= _)%nat \/ (_ >= _)%nat |- _ ] => destruct H
  | [ H : (?x >= _)%nat |- context[match ?x with 
                                   | O => _
                                   | S _ => _ 
                                   end] ] => destruct x; simpl
  | [ |- match ?x with O => ?a | S _ => _ end = ?a ] => 
    destruct x; [reflexivity | simpl]
  | [ H : (O >= S _)%nat |- _ ] => omega
  | [ H : (S ?m >= S ?n)%nat |- _] => assert (m >= n)%nat by omega; clear H
  | [ |- _ ] => simpl; intros
  end.

(* Well-formedness tactic *)
Ltac show_wf :=
  repeat match goal with
  | [ H : WF_Matrix _ _ ?A |- WF_Matrix _ _ ?A ] => exact H
  | [ |- WF_Matrix _ _  (Zero ?m ?n) ] => eapply WF_Zero
  | [ |- WF_Matrix _ _ (Id ?n) ]      => eapply WF_Id 
  | [ |- WF_Matrix _ _ (?A × ?B) ]    => eapply WF_mult 
  | [ |- WF_Matrix _ _ (?A .+ ?B) ]   => eapply WF_plus 
  | [ |- WF_Matrix _ _ (?p .* ?B) ]   => eapply WF_scale
  | [ |- WF_Matrix _ _ (?A ⊗ ?B) ]    => eapply WF_kron
  | [ |- WF_Matrix _ _ (?A⊤) ]        => eapply WF_transpose 
  | [ |- WF_Matrix _ _ (?A†) ]        => eapply WF_conj_transpose 
  | [ H : WF_Matrix ?m ?n ?A |- context[dim_x ?A] ] => 
    rewrite (wf_dim_x _ _ _ H) in *; auto
  | [ H : WF_Matrix ?m ?n ?A |- context[dim_y ?A] ] => 
    rewrite (wf_dim_y _ _ _ H) in *; auto
  | [ |- Pos _ ] => solve_pos
  end.
(*
  trivial;
  let x := fresh "x" in
  let y := fresh "y" in
  let H := fresh "H" in
  intros x y [H | H];
    repeat (destruct x; try reflexivity; try omega);
    repeat (destruct y; try reflexivity; try omega).
*)

Ltac show_wf_safe :=
  repeat match goal with
  | [ _ : WF_Matrix _ _ ?A |- WF_Matrix _ _ ?A ] => assumption
  | [ |- WF_Matrix _ _  (Zero ?m ?n) ] => apply WF_Zero
  | [ |- WF_Matrix _ _ (Id ?n) ]      => apply WF_Id 
  | [ |- WF_Matrix _ _ (?A × ?B) ]    => apply WF_mult 
  | [ |- WF_Matrix _ _ (?A .+ ?B) ]   => apply WF_plus 
  | [ |- WF_Matrix _ _ (?p .* ?B) ]   => apply WF_scale
  | [ |- WF_Matrix _ _ (?A ⊗ ?B) ]    => apply WF_kron
  | [ |- WF_Matrix _ _ (?A⊤) ]        => apply WF_transpose 
  | [ |- WF_Matrix _ _ (?A†) ]        => apply WF_conj_transpose 
  end; trivial.


Lemma Cconj_R : forall r : R, Cconj r = r. Proof. intros. clra. Qed.

(* More basic for the moment *)
Ltac Csimpl := 
  simpl;
  repeat (
    try rewrite Cconj_R;
    try rewrite Cplus_0_l;
    try rewrite Cplus_0_r;
    try rewrite Cmult_0_l;
    try rewrite Cmult_0_r;
    try rewrite Cmult_1_l;
    try rewrite Cmult_1_r
).

Ltac Nsimpl :=
  simpl;
  repeat (
    try rewrite plus_0_l;
    try rewrite plus_0_r;
    try rewrite mult_0_l;
    try rewrite mult_0_r;
    try rewrite mult_1_l;
    try rewrite mult_1_r
).


(* To solve goals of the form M1 = M2 for well-formed matrices M1 and M2 *)
(*
Ltac mlra := 
  eapply matrix_equiv_eq; (* show matrix equivalence by decomposing into parts *) 
  constructor; show_wf; 
  constructor; simpl; 
    [try rewrite_all_wf_matrix; auto | try rewrite_all_wf_matrix; auto | ];
  intros; try clra.
*)
(*
(*  compute; *)
  unfold Mplus, Mmult, dot, kron, transpose, conj_transpose;
  prep_matrix_equality;
  repeat match goal with
  | [ |- _ = _]  => clra
  | [ x : nat |- _ ] => destruct x
  end.
(** Basic Matrix Lemmas **)
*)

Ltac mlra :=
  intros;
  repeat (match goal with
  | [ |- WF_Matrix _ _ _  ] => show_wf
  | _ => omega
  | [ |- ?A = ?B] => match type of A with
                     | Matrix => eapply matrix_equiv_eq
                     | C => clra
                     | _ => fail
                     end
  | [ |- WF_Matrix_Equiv _ _ _ _ ] => constructor
  | [ |- _ ≡ _ ] => constructor
  | [ |- context[dim_x _] ] => erewrite wf_dim_x; eauto
  | [ |- context[dim_y _] ] => erewrite wf_dim_y; eauto
  | [ H : context[dim_x _] |- _ ] => erewrite wf_dim_x in H; eauto
  | [ H : context[dim_y _] |- _ ] => erewrite wf_dim_y in H; eauto
  | [ |- context[Pos _] ] => solve_pos; fail
  end; Nsimpl; Csimpl; intros; auto).


Lemma Mplus_0_l : forall {m n : nat} (A : Matrix), WF_Matrix m n A ->
      Zero m n .+ A = A.
Proof. mlra. Qed.

Lemma Mplus_0_r : forall {m n : nat} (A : Matrix), WF_Matrix m n A ->
      A .+ Zero m n = A.
Proof. mlra. Qed.
    
Program Lemma Mmult_0_l : forall {m n o : nat} (A : Matrix), 
        Pos m -> WF_Matrix n o A ->
       (Zero m n) × A = Zero m o.
Proof. mlra. clear H H0.
       induction n; simpl; try rewrite IHn; clra. 
Qed.

Lemma Csum_to_0 : forall f n,
      (forall x, f x = C0) -> Csum_to_n f n = C0.
Proof. mlra. 
  induction n; intros; simpl; auto.
  rewrite IHn. rewrite H. clra.
Qed.

Program Lemma Mmult_0_r : forall {m n o : nat} (A : Matrix),  
              Pos o -> WF_Matrix m n A ->
              A × Zero n o = Zero m o.
Proof.
  mlra.
  clear H0.
  induction n; simpl; try rewrite IHn; mlra. 
Qed.

(* using <= because our form RCsum_to_n is exclusive. *)
Lemma Mmult_1_l_gen: forall {m n : nat} (A : Matrix) (x z k : nat), 
  WF_Matrix m n A ->
  k <= m ->
  (k <= x -> Csum_to_n (fun y : nat => (entry (Id m) x y * entry A y z)%C) k = C0) /\
  (k > x -> Csum_to_n (fun y : nat => (entry (Id m) x y * entry A y z)%C) k = entry A x z).
Proof.  
  intros.
  induction k; simpl.
  * split; intros; try clra.
    rewrite_all_wf_matrix. omega.
  * destruct IHk as [IH1 IH2]; [omega | ]; simpl in *.
    split; intros.
    + replace (x =? k) with false by (symmetry; apply Nat.eqb_neq; omega).
      Csimpl. 
      rewrite IH1; [clra | omega].
    + destruct (x =? k) eqn:Hxk.
      - replace k with x in *; [ | apply Nat.eqb_eq; auto]. simpl.
        rewrite IH1; auto. Csimpl.
        replace (x <? m) with true by (symmetry; apply Nat.ltb_lt; omega). 
        clra. 
      - Csimpl. apply Nat.eqb_neq in Hxk.
        rewrite IH2; auto. omega.
Qed.


(* Actually, I think we want a fold over lists of nats? *)
Lemma Csum_to_n_partition : forall (p : nat -> bool)(f : nat -> C) n,
      (forall x, if p x then f x = C0 else True) -> 
      Csum_to_n f n = Csum_to_n (fun x => if p x then C0 else f x) n.
Proof.
Admitted.

Lemma Mmult_1_l_mat_eq : forall {m n : nat} (A : Matrix), WF_Matrix m n A ->
      Id m × A = A.
Proof.
  mlra.
  generalize dependent m.
  induction m; intros.
  - absurd (x < 0); auto. inversion 1.
  - simpl. (*rewrite IHm.*)
Admitted.

Lemma Mmult_1_l: forall {m n : nat} (A : Matrix),
  WF_Matrix m n A -> Id m × A = A.
Proof. 
  mlra.
  edestruct (@Mmult_1_l_gen m n A x) as [Hl Hr]; simpl in *; auto.
Qed.

Lemma Mmult_1_r_gen: forall {m n : nat} (A : Matrix) (x z k : nat), 
  WF_Matrix m n A ->
  k <= n ->
  (k <= z -> Csum_to_n (fun y : nat => (entry A x y * entry (Id n) y z)%C) k = C0) /\
  (k > z -> Csum_to_n (fun y : nat => (entry A x y * entry (Id n) y z)%C) k = entry A x z).
Proof.  
  intros.
  induction k; simpl.
  * split; [reflexivity | omega].
  * destruct IHk as [IHl IHr]; [omega | ].
    split; intros.
    + simpl in *.
      replace (k =? z) with false by (symmetry; apply Nat.eqb_neq; omega).
      rewrite IHl; [ clra | omega]. 
    + simpl in *.
      destruct (k =? z) eqn:Eqkz.
      - apply Nat.eqb_eq in Eqkz; subst.
        replace (z <? n) with true in * by (symmetry; apply Nat.ltb_lt; omega).
        rewrite IHl; [clra | omega].
      - apply Nat.eqb_neq in Eqkz.
        simpl in *. Csimpl.
        apply IHr.
        omega.
Qed.

(*
Lemma Mmult_1_r_mat_eq : forall {m n : nat} (A : Matrix), 
      WF_Matrix m n A ->
      A × Id n ≡ A.
Proof.
  intros m n A x y.
  destruct x as [x Px], y as [y Py].
  simpl. 
  unfold Mmult.
  edestruct (@Mmult_1_r_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  apply Hr.
  omega.
Qed.  
*)

Lemma Mmult_1_r: forall {m n : nat} (A : Matrix), 
  WF_Matrix m n A -> A × Id n = A.
Admitted.
(*
Proof.
  intros m n A H.
  apply mat_equiv_eq; trivial.
  apply WF_mult; trivial.
  apply WF_Id.
  apply Mmult_1_r_mat_eq.
Qed.
*)

Ltac strip_matrix_proofs :=
  repeat match goal with
    | [ |- context[eq_rect ?x ?P ?Px ?y ?eq]] => destruct eq; simpl
  end. 

Lemma divmod_1 : forall n, Nat.divmod n 0 0 0 = (n,0).
Proof.
  intros.
  specialize (Nat.divmod_spec n 0 0 0); intros H.
  destruct (Nat.divmod n 0 0 0) as [x y].
  destruct H; auto.
  f_equal; omega. 
Qed.



Lemma kron_1_r : forall (m n : nat) (A : Matrix), 
      WF_Matrix m n A ->
      A ⊗ Id 1 = A.
Proof.
  mlra. 
  simpl. 
  repeat rewrite divmod_1. mlra. 
Qed.



(* This side is much more limited/annoying *)
Lemma kron_1_l : forall (m n : nat) (A : Matrix), 
  m > 0 -> n > 0 -> WF_Matrix m n A -> Id 1 ⊗ A = A.
Proof.
  mlra.
  replace (x mod m) with x by (rewrite Nat.mod_small; auto). 
  replace (y mod n) with y by (rewrite Nat.mod_small; auto).
  replace (x / m) with 0 by (rewrite Nat.div_small; auto).
  replace (y / n) with 0 by (rewrite Nat.div_small; auto).
  clra.
Qed.

Theorem transpose_involutive : forall (A : Matrix), 
        (A⊤)⊤ = A.
Proof. intros. destruct A; reflexivity. Qed.

Lemma conj_involutive : forall c, Cconj (Cconj c) = c.
Proof. intros. clra. Qed.

Theorem conj_transpose_involutive : forall m n A,
        WF_Matrix m n A -> A†† = A.
Proof. intros. mlra. Qed.  

Lemma id_transpose_eq : forall n, Pos n -> (Id n)⊤ = (Id n).
Proof.
  intros. mlra.
  destruct (x =? y) eqn:Eq.
  + apply Nat.eqb_eq in Eq; subst. rewrite Nat.eqb_refl. auto.
  + rewrite Nat.eqb_sym. rewrite Eq. auto.
Qed.

Lemma id_conj_transpose_eq : forall n, Pos n -> (Id n)† = (Id n).
Proof.
  intros n. mlra.
  destruct (x =? y) eqn:Eq.
  + apply Nat.eqb_eq in Eq; subst. rewrite Nat.eqb_refl. simpl.
    destruct (y <? n); clra.
  + rewrite Nat.eqb_sym. rewrite Eq. simpl. clra.
Qed.

Theorem Mplus_comm : forall m n A B,
        WF_Matrix m n A -> WF_Matrix m n B ->
        A .+ B = B .+ A.
Proof.
  mlra. 
Qed.


Theorem Mplus_assoc : forall m n A B C,
        WF_Matrix m n A -> WF_Matrix m n B -> WF_Matrix m n C ->
        A .+ B .+ C = A .+ (B .+ C).
Proof.
  mlra.
Qed.

Theorem Mmult_assoc : forall m n o p A B C,
        WF_Matrix m n A -> WF_Matrix n o B -> WF_Matrix o p C ->
        A × B × C = A × (B × C).
Proof.
  mlra.
  (* Should be a property of sum_to_n *)
Admitted.

Lemma Csum_eq : forall f g k, f = g -> Csum_to_n f k = Csum_to_n g k.
Proof. intros f g k H. subst. reflexivity. Qed.

Lemma Csum_add : forall f g k, 
                   (Csum_to_n (fun x => f x + g x) k = Csum_to_n f k + Csum_to_n g k)%C.
Proof.
  intros f g k.
  induction k.
  + simpl. clra.
  + simpl. rewrite IHk. clra.
Qed.

Lemma Mmult_plus_distr_l : forall m n o A B C,
      WF_Matrix m n A -> WF_Matrix n o B -> WF_Matrix n o C ->
      A × (B .+ C) = A × B .+ A × C.
Proof. 
  mlra.
  rewrite <- Csum_add.
  f_equal.
  apply functional_extensionality; intros z.
  clra.
Qed.

Lemma Mmult_plus_distr_r : forall m n o A B C,
      WF_Matrix m n A -> WF_Matrix m n B -> WF_Matrix n o C ->
      (A .+ B) × C = A × C .+ B × C.
Proof. 
  mlra.
  rewrite <- Csum_add.
  f_equal.
  apply functional_extensionality; intros.
  clra.
Qed.

(* These are easy - just haven't done them *)
Lemma Mscale_mult_dist_l : forall m n o x A B,
                           WF_Matrix m n A -> WF_Matrix n o B -> 
                           ((x .* A) × B) = x .* (A × B).
Proof.
  mlra.
Admitted.

Lemma Mscale_mult_dist_r : forall m n o x A B,
                           WF_Matrix m n A -> WF_Matrix n o B -> 
                             (A × (x .* B)) = x .* (A × B).
Proof.
  mlra.
Admitted.

(* Inverses of square matrices *)

Definition Minv n A B : Prop := A × B = Id n /\ B × A = Id n.

Lemma Minv_unique : forall n A B C,
                      WF_Matrix n n A -> WF_Matrix n n B -> WF_Matrix n n C ->
                      Minv n A B -> Minv n A C -> B = C.
Proof.
  intros n A B C WFA WFB WFC [HAB HBA] [HAC HCA]. 
  replace B with (B × Id n) by (eapply Mmult_1_r; eauto).
  rewrite <- HAC.  
  replace C with (Id n × C) at 2 by (eapply Mmult_1_l; eauto).
  rewrite <- HBA.  
  erewrite Mmult_assoc; eauto.
Qed.

Lemma Minv_symm : forall n A B, Minv n A B -> Minv n B A.
Proof. unfold Minv; intuition. Qed.

(* Important but hardish lemma *)
Lemma Minv_flip : forall n A B, WF_Matrix n n A -> WF_Matrix n n B ->
      A × B = Id n -> B × A = Id n.
Admitted.
  
Lemma Minv_left : forall n A B, WF_Matrix n n A -> WF_Matrix n n B ->
      A × B = Id n -> Minv n A B.
Proof.
  intros n A B H. 
  unfold Minv. split; trivial.
  apply Minv_flip; auto.
Qed.

Lemma Minv_right : forall n A B, WF_Matrix n n A -> WF_Matrix n n B ->
      B × A = Id n -> Minv n A B.
Proof.
  intros n A B H. 
  unfold Minv. split; auto.
  apply Minv_flip; auto.
Qed.

(* Not generally true, just like sum_sum wasn't.
   A general sum_n_to_m function might have better properties. 
Theorem sum_product : forall (p q : nat) (f : nat -> R), 
  Csum_to_n f (p * q) = ((Csum_to_n f p) * (Csum_to_n f q))%R.
Proof. 
  intros p q f.
  induction p. simpl. lra.
  simpl.
  *)

Lemma kron_mixed_product : forall m n o p q r A B C D,
      WF_Matrix m n A -> WF_Matrix p q B -> WF_Matrix n o C -> WF_Matrix q r D ->
      p <> 0 -> q <> 0 -> r <> 0 ->
      (A ⊗ B) × (C ⊗ D) = (A × C) ⊗ (B × D).
Proof. mlra.
Admitted.

Theorem kron_transpose : forall A B,
       (A ⊗ B)⊤ = A⊤ ⊗ B⊤.
Proof. reflexivity. Qed.

Lemma conj_mult_dist : forall (x y : C), Cconj (x * y) = (Cconj x * Cconj y)%C.
Proof. intros x y. clra. Qed.
  
Lemma Mmult_conj_transpose : forall m n o A B,
      WF_Matrix m n A -> WF_Matrix n o B ->
      (A × B)† = B† × A†.
Proof.
  mlra.
Admitted.  


Lemma kron_conj_transpose : forall m n o p A B,
      WF_Matrix m n A -> WF_Matrix o p B -> o <> 0 -> p <> 0 ->
      (A ⊗ B)† = A† ⊗ B†.
Proof.
  mlra. 
Qed.

Lemma id_kron : forall m n, n <> 0 -> Id m ⊗ Id n = Id (m * n).
Proof.
(*
  mlra.
  destruct (x =? y) eqn:Eq.
  + apply beq_nat_true in Eq; subst.
    repeat rewrite <- beq_nat_refl; simpl.
    destruct n.
    - simpl.
      rewrite mult_0_r.
      replace (y <? O) with false. clra.
      symmetry; apply Nat.ltb_nlt. omega.
    - replace (y mod S n <? S n) with true.
      Focus 2. symmetry. apply Nat.ltb_lt.
               apply Nat.mod_upper_bound. 
               omega.      
      rewrite Cmult_1_r.
      destruct (y / S n <? m) eqn:L1, (y <? m * S n) eqn:L2; trivial.
      * apply Nat.ltb_lt in L1. 
        apply Nat.ltb_nlt in L2. 
        contradict L2. 
        (* Why doesn't this lemma exist??? *)
        destruct m.
        omega.
        apply Nat.div_small_iff; try omega. 
        simpl. apply Nat.neq_succ_0. 
        apply Nat.div_small in L1.
        rewrite Nat.div_div in L1; try omega.
        rewrite mult_comm.
        assumption.
      * apply Nat.ltb_nlt in L1. 
        apply Nat.ltb_lt in L2. 
        contradict L1. 
        apply Nat.div_lt_upper_bound. omega.
        rewrite mult_comm.
        assumption.
  + simpl.
    destruct (x / n =? y / n) eqn:Eq1;
    destruct (x mod n =? y mod n) eqn:Eq2; simpl; try clra.
    destruct n; try clra.    
    apply beq_nat_false in Eq.
    apply beq_nat_true in Eq1. 
    apply beq_nat_true in Eq2. 
    contradict Eq.
    assert (S n <> 0) as H by omega.
    specialize (Nat.div_mod x (S n) H). intros H1.
    specialize (Nat.div_mod y (S n) H). intros H2.    
    rewrite Eq1, Eq2 in H1.
    rewrite <- H2 in H1.
    assumption.
Qed.
*)
Admitted.
  
(*  
Theorem Mmult_assoc : forall (m n o p : nat) (A : Matrix m n) (B : Matrix n o) 
  (C: Matrix o p), A × B × C = A × (B × C).
Proof.
  intros m n o p A B C.
  unfold Mmult.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  induction n.
  + simpl.
    clear B.
    induction o. reflexivity.
    simpl. rewrite IHo. lra.
  + simpl. 
    rewrite <- IHn.
    simpl.
Admitted.
*)

Ltac Msimpl1 := 
  repeat rewrite kron_1_l;
  repeat rewrite kron_1_r;
  repeat rewrite Mmult_1_l; 
  repeat rewrite Mmult_1_r; 
  repeat rewrite id_conj_transpose_eq;
  repeat rewrite id_conj_transpose_eq; 
  repeat rewrite conj_transpose_involutive;
  try show_wf_safe; try omega.
Ltac Msimpl := simpl; repeat Msimpl1.




(* *)