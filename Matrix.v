Require Import Program. 
Require Import Reals.
Require Import Complex.
Require Import Psatz.
Require Import Omega.
Require Import Coq.Strings.String.
Require Import List.
Require Import Bool.
Import ListNotations.

Open Scope R_scope.
Open Scope C_scope.
Open Scope nat_scope.

Bind Scope nat_scope with nat.
Bind Scope R_scope with R.
Bind Scope C_scope with C.


(** Useful C stuff *)

Notation C0 := (RtoC 0). 
Notation C1 := (RtoC 1).
Notation C2 := (RtoC 2).
Notation "√ n" := (sqrt n) (at level 20).

Lemma c_proj_eq : forall (c1 c2 : C), fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.  
Proof. intros c1 c2 H1 H2. destruct c1, c2. simpl in *. subst. reflexivity. Qed.

Ltac clra := eapply c_proj_eq; simpl; lra.

(* A bit of useful reflection from Software Foundations Vol 3 *)

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.  apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].


(** Matrix Definitions **)

Definition Matrix (m n : nat) := nat -> nat -> C.

Ltac prep_matrix_equality :=
  let x := fresh "x" in 
  let y := fresh "y" in 
  apply functional_extensionality; intros x;
  apply functional_extensionality; intros y.


Parameter print_C : C -> string.
Fixpoint print_row {m n} i j (A : Matrix m n) : string :=
  match j with
  | 0   => "\n"
  | S j' => print_C (A i j') ++ ", " ++ print_row i j' A
  end.
Fixpoint print_rows {m n} i j (A : Matrix m n) : string :=
  match i with
  | 0   => ""
  | S i' => print_row i' n A ++ print_rows i' n A
  end.
Definition print_matrix {m n} (A : Matrix m n) : string :=
  print_rows m n A.

Notation Square n := (Matrix n n).

Definition WF_Matrix (m n: nat) (A : Matrix m n) : Prop := 
  forall x y, x >= m \/ y >= n -> A x y = C0. 

(* I won't be using this much, but it can ensure the matrix bounds *)
Definition get {m n} (A : Matrix m n) (a : nat | a < m) (b : nat | b < n) := 
  A (`a) (`b).

Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop := 
  forall (x : nat | x < m) (y : nat | y < n), A (`x) (`y) = B (`x) (`y).

Lemma mat_equiv_eq : forall {m n : nat} (A B : Matrix m n),
  WF_Matrix m n A -> 
  WF_Matrix m n B -> 
  mat_equiv A B ->
  A = B.
Proof.
  intros m n A' B' WFA WFB Eq.
  prep_matrix_equality.
  unfold mat_equiv in Eq.
  bdestruct (x <? m).
  bdestruct (y <? n).
  + specialize (Eq (exist _ x H) (exist _ y H0)). apply Eq.
  + rewrite WFA, WFB; trivial; right; try omega.
  + rewrite WFA, WFB; trivial; left; try omega.
Qed.
    
Definition list2D_to_matrix (l : list (list C)) : 
  Matrix (length l) (length (hd [] l)) :=
  (fun x y => nth y (nth x l []) 0%R).

Definition M23 : Matrix 2 3 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => 1%R
  | (0, 1) => 2%R
  | (0, 2) => 3%R
  | (1, 0) => 4%R
  | (1, 1) => 5%R
  | (1, 2) => 6%R
  | _ => C0
  end.

Definition M23' : Matrix 2 3 := 
  list2D_to_matrix  
  ([[RtoC 1; RtoC 2; RtoC 3];
    [RtoC 4; RtoC 5; RtoC 6]]).

Lemma M23eq : M23 = M23'.
Proof.
  unfold M23'.
  compute.
  prep_matrix_equality.
  do 4 (try destruct x; try destruct y; simpl; trivial).
Qed.

(** Operands and Operations **)

Definition Zero (m n : nat) : Matrix m n := fun x y => 0%R.

Definition Id (n : nat) : Square n := 
  (fun x y => if (x =? y) && (x <? n) then C1 else C0).

(* sum to n exclusive *)
Fixpoint Rsum_to_n (f : nat -> C) (n : nat) : C := 
  match n with
  | 0 => C0
  | S n' => (Rsum_to_n f n' +  f n')%C
  end.

Definition trace {n : nat} (A : Square n) := 
  Rsum_to_n (fun x => A x x) n.

Definition scale {m n : nat} (r : C) (A : Matrix m n) : Matrix m n := 
  (fun x y => (r * A x y)%C).

Definition dot {n : nat} (A : Matrix 1 n) (B : Matrix n 1) : C :=
  Rsum_to_n (fun x => A O x  * B x O)%C n.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  (fun x y => (A x y + B x y)%C).


Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o := 
  (fun x z => Rsum_to_n (fun y => A x y * B y z)%C n).


(* Only well-defined when o and p are non-zero *)
Definition kron {m n o p : nat} (A : Matrix m n) (B : Matrix o p) : 
  Matrix (m*o) (n*p) :=
  (fun x y => Cmult (A (x / o) (y / p)) (B (x mod o) (y mod p))).

Definition transpose {m n} (A : Matrix m n) : Matrix n m := 
    (fun x y => A y x).

Definition conj_transpose {m n} (A : Matrix m n) : Matrix n m := 
  (fun x y => Cconj (A y x)).

Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Infix ".+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix ".*" := scale (at level 40, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Infix "≡" := mat_equiv (at level 100) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope. 
Notation "A †" := (conj_transpose A) (at level 0) : matrix_scope. 
Notation "Σ^ n f" := (Rsum_to_n f n) (at level 90) : matrix_scope.
Hint Unfold Zero Id trace dot Mplus scale Mmult kron mat_equiv transpose 
            conj_transpose : M_db.
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
  | [ |- _ = _ ]                  => Csolve 
  | [ x : nat |- _ ]                => destruct x (* I'd rather bound this *)
  end.

(* Similar to Msolve but often faster *)
(* I'd rather not use compute. *)
Ltac mlra := 
(*  compute; *)
  unfold Mplus, Mmult, dot, scale, kron, transpose, conj_transpose, mat_equiv;  
  prep_matrix_equality;
  repeat match goal with
  | [ |- _ = _]  => clra
  | [ x : nat |- _ ] => destruct x
  end.


(** Well-Formedness **)

Lemma WF_Zero : forall {m n : nat}, WF_Matrix m n (Zero m n).
Proof. intros m n. unfold WF_Matrix. reflexivity. Qed.

Lemma WF_Id : forall {n : nat}, WF_Matrix n n (Id n). 
Proof. 
  unfold WF_Matrix, Id. intros n x y H.
  simpl.
  destruct H; bdestruct (x =? y); bdestruct (x <? n); trivial; omega.
Qed.

Lemma WF_scale : forall {m n : nat} (r : C) (A : Matrix m n), 
  WF_Matrix m n A -> WF_Matrix m n (scale r A).
Proof.
  unfold WF_Matrix, scale.
  intros m n r A H x y H0. simpl.
  rewrite H; trivial.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

Lemma WF_plus : forall {m n} (A B : Matrix m n), 
  WF_Matrix m n A -> WF_Matrix m n B -> WF_Matrix m n (A .+ B).
Proof.
  unfold WF_Matrix, Mplus.
  intros m n A B H H0 x y H1. simpl.
  rewrite H, H0; trivial.
  rewrite Cplus_0_l.
  reflexivity.
Qed.

Lemma WF_mult : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o), 
  WF_Matrix m n A -> WF_Matrix n o B -> WF_Matrix m o (A × B).
Proof.
  unfold WF_Matrix, Mmult.
  intros m n o A B H H0 x y H1. simpl.
  destruct H1.
  + assert (forall y, A x y = 0%R) as H'. {intros. apply H. auto. } clear H H0 H1.
    induction n.
    * simpl. reflexivity.
    * simpl. rewrite H'. 
      rewrite Cmult_0_l.
      rewrite Cplus_0_r.    
      apply IHn; trivial.
  + assert (forall x, B x y = 0%R) as H'. { intros. apply H0. auto. } 
    clear H H0 H1.
    induction n.
    * simpl. reflexivity.
    * simpl. 
      rewrite H'.
      rewrite Cmult_0_r.
      rewrite Cplus_0_r.
      apply IHn; trivial.
Qed.

(*
Lemma WF_kron : forall {m n o p : nat} (A : Matrix m n) (B : Matrix o p), 
                  o <> 0 -> p <> 0 ->
                  WF_Matrix m n A -> WF_Matrix o p B -> WF_Matrix (m*o) (n*p) (A ⊗ B).
Proof.
  unfold WF_Matrix, kron.
  intros m n o p A B Nn No H H0 x y H1. simpl.
  rewrite H.
  rewrite Cmult_0_l; reflexivity.
  destruct H1.
  unfold ge in *.
  left. 
  apply Nat.div_le_lower_bound; trivial.
  rewrite Nat.mul_comm.
  assumption.
  right.
  apply Nat.div_le_lower_bound; trivial.
  rewrite Nat.mul_comm.
  assumption.
Qed. 
*)

(* Should the non-zero assumptions be here? *)
(* Adding equivalence conditions *)
Lemma WF_kron : forall {m n o p q r : nat} (A : Matrix m n) (B : Matrix o p), 
                  o <> 0 -> p <> 0 ->
                  q = m * o -> r = n * p -> 
                  WF_Matrix m n A -> WF_Matrix o p B -> WF_Matrix q r (A ⊗ B).
Proof.
  unfold WF_Matrix, kron.
  intros m n o p q r E1 E2 A B Nn No H H0 x y H1. subst.
  rewrite H.
  rewrite Cmult_0_l; reflexivity.
  destruct H1.
  unfold ge in *.
  left. 
  apply Nat.div_le_lower_bound; trivial.
  rewrite Nat.mul_comm.
  assumption.
  right.
  apply Nat.div_le_lower_bound; trivial.
  rewrite Nat.mul_comm.
  assumption.
Qed. 

Lemma WF_transpose : forall {m n : nat} (A : Matrix m n), 
                     WF_Matrix m n A -> WF_Matrix n m A⊤. 
Proof. unfold WF_Matrix, transpose. intros m n A H x y H0. apply H. 
       destruct H0; auto. Qed.

Lemma WF_conj_transpose : forall {m n : nat} (A : Matrix m n), 
      WF_Matrix m n A -> WF_Matrix n m A†. 
Proof. unfold WF_Matrix, conj_transpose, Cconj. intros m n A H x y H0. simpl. 
rewrite H. clra. omega. Qed.


(* Well-formedness tactic *)
Ltac show_wf :=
  repeat match goal with
  | [ |- WF_Matrix _ _ (?A × ?B) ]  => apply WF_mult 
  | [ |- WF_Matrix _ _ (?A .+ ?B) ] => apply WF_plus 
  | [ |- WF_Matrix _ _ (?p .* ?B) ] => apply WF_scale
  | [ |- WF_Matrix _ _ (?A ⊗ ?B) ]  => apply WF_kron
  | [ |- WF_Matrix _ _ (?A⊤) ]      => apply WF_transpose 
  | [ |- WF_Matrix _ _ (?A†) ]      => apply WF_conj_transpose 
  end;
  trivial;
  unfold WF_Matrix;
  let x := fresh "x" in
  let y := fresh "y" in
  let H := fresh "H" in
  intros x y [H | H];
    repeat (destruct x; try reflexivity; try omega);
    repeat (destruct y; try reflexivity; try omega).

(* Create HintDb wf_db. *)
Hint Resolve WF_Zero WF_Id WF_mult WF_plus WF_scale WF_kron WF_transpose 
     WF_conj_transpose : wf_db.

(* Deprecated in favor of "auto with wf_db" *)
Ltac show_wf_safe :=
  repeat match goal with
  | [ |- WF_Matrix _ _  (Zero ?m ?n) ] => apply WF_Zero
  | [ |- WF_Matrix _ _ (Id ?n) ]      => apply WF_Id 
  | [ |- WF_Matrix _ _ (?A × ?B) ]    => apply WF_mult 
  | [ |- WF_Matrix _ _ (?A .+ ?B) ]   => apply WF_plus 
  | [ |- WF_Matrix _ _ (?p .* ?B) ]   => apply WF_scale
  | [ |- WF_Matrix _ _ (?A ⊗ ?B) ]    => apply WF_kron
  | [ |- WF_Matrix _ _ (?A⊤) ]        => apply WF_transpose 
  | [ |- WF_Matrix _ _ (?A†) ]        => apply WF_conj_transpose 
  end; auto.


Lemma Cconj_R : forall r : R, Cconj r = r. Proof. intros. clra. Qed.
Lemma Cconj_rad2 : (Cconj (C1 / √2) = C1 / √2)%C. Proof. clra. Qed.
Lemma square_rad2 : ((C1/√2) * (C1/√2) = C1/C2)%C. 
Proof. 
  eapply c_proj_eq; simpl; try lra.
  Rsimpl.
  Search (_ * _ * _ * _)%R.
  rewrite Rmult_assoc.
  rewrite (Rmult_comm (/2) _).
  repeat rewrite <- Rmult_assoc.
  rewrite sqrt_def; lra.
Qed.

(* deprecated in favor of autorewrite *)
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

Hint Rewrite Cconj_R Cconj_rad2 square_rad2 Cplus_0_l Cplus_0_r 
     Cmult_0_l Cmult_0_r Cmult_1_l Cmult_1_r : C_db.

(** Basic Matrix Lemmas **)

Lemma Mplus_0_l : forall (m n : nat) (A : Matrix m n), Zero m n .+ A = A.
Proof. intros. mlra. Qed.

Lemma Mplus_0_r : forall (m n : nat) (A : Matrix m n), A .+ Zero m n = A.
Proof. intros. mlra. Qed.
    
Program Lemma Mmult_0_l : forall (m n o : nat) (A : Matrix n o), 
       (Zero m n) × A = Zero m o.
Proof.
  intros m n o A. unfold Mmult, Zero.
  prep_matrix_equality.
  induction n.
  + simpl. reflexivity.
  + simpl in *.
    autorewrite with C_db.
    apply IHn.
Qed.    

Program Lemma Mmult_0_r : forall (m n o : nat) (A : Matrix m n), 
              A × Zero n o = Zero m o.
Proof.
  intros m n o A. 
  unfold Zero, Mmult.
  prep_matrix_equality.
  induction n.
  + simpl. reflexivity.
  + simpl. 
    autorewrite with C_db.
    apply IHn.
Qed.

(* using <= because our form Rsum_to_n is exclusive. *)
Lemma Mmult_1_l_gen: forall (m n : nat) (A : Matrix m n) (x z k : nat), 
  k <= m ->
  (k <= x -> Rsum_to_n (fun y : nat => ((Id m) x y * A y z)%C) k = C0) /\
  (k > x -> Rsum_to_n (fun y : nat => ((Id m) x y * A y z)%C) k = A x z).
Proof.  
  intros m n A x z k B.
  induction k.
  * simpl. split. reflexivity. omega.
  * destruct IHk as [IHl IHr]. omega.  
    split.
    + intros leSkx.
      simpl.
      unfold Id.
      bdestruct (x =? k); try omega.
      autorewrite with C_db.
      apply IHl.
      omega.
    + intros gtSkx.
      simpl in *.
      unfold Id in *.
      bdestruct (x =? k); bdestruct (x <? m); subst; try omega.
      rewrite IHl by omega; simpl; clra.
      rewrite IHr by omega; simpl; clra.
Qed.

Lemma Mmult_1_l_mat_eq : forall (m n : nat) (A : Matrix m n), Id m × A ≡ A.
Proof.
  intros m n A x y.
  destruct x as [x Px], y as [y Py].
  simpl. 
  unfold Mmult.
  edestruct (@Mmult_1_l_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  apply Hr.
  omega.
Qed.  

Lemma Mmult_1_l: forall (m n : nat) (A : Matrix m n), 
  WF_Matrix m n A -> Id m × A = A.
Proof.
  intros m n A H.
  apply mat_equiv_eq; trivial.
  auto with wf_db.
  apply Mmult_1_l_mat_eq.
Qed.

Lemma Mmult_1_r_gen: forall (m n : nat) (A : Matrix m n) (x z k : nat), 
  k <= n ->
  (k <= z -> Rsum_to_n (fun y : nat => (A x y * (Id n) y z)%C) k = C0) /\
  (k > z -> Rsum_to_n (fun y : nat => (A x y * (Id n) y z)%C) k = A x z).
Proof.  
  intros m n A x z k B.
  induction k.
  simpl. split. reflexivity. omega.
  destruct IHk as [IHl IHr].
  omega.
  split.
  + intros leSkz.
    simpl in *.
    unfold Id.
    bdestruct (k =? z); try omega.
    autorewrite with C_db.
    apply IHl; omega.
  + intros gtSkz.
    simpl in *.
    unfold Id in *.
    bdestruct (k =? z); subst.
    - bdestruct (z <? n); try omega.
      rewrite IHl by omega; clra.
    - rewrite IHr by omega; simpl; clra.
Qed.

Lemma Mmult_1_r_mat_eq : forall (m n : nat) (A : Matrix m n), A × Id n ≡ A.
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

Lemma Mmult_1_r: forall (m n : nat) (A : Matrix m n), 
  WF_Matrix m n A -> A × Id n = A.
Proof.
  intros m n A H.
  apply mat_equiv_eq; trivial.
  auto with wf_db.
  apply Mmult_1_r_mat_eq.
Qed.

Ltac strip_matrix_proofs :=
  repeat match goal with
    | [ |- context[eq_rect ?x ?P ?Px ?y ?eq]] => destruct eq; simpl
  end. 

Lemma kron_1_r : forall (m n : nat) (A : Matrix m n), A ⊗ Id 1 = A.
Proof.
  intros m n A.
  prep_matrix_equality.
  unfold Id, kron.
  rewrite 2 Nat.div_1_r.
  rewrite 2 Nat.mod_1_r.
  simpl.
  autorewrite with C_db.
  reflexivity.
Qed.

(* This side is much more limited/annoying *)
Lemma kron_1_l : forall (m n : nat) (A : Matrix m n), 
  m > 0 -> n > 0 -> WF_Matrix m n A -> Id 1 ⊗ A = A.
Proof.
  intros m n A H1 H2 WF.
  unfold Id, kron.
  prep_matrix_equality.
  bdestruct (x / m <? 1); rename H into Eq1.
  bdestruct (x / m =? y / n); rename H into Eq2; simpl.
  + assert (x / m = 0) by omega. clear Eq1. rename H into Eq1.
    rewrite Eq1 in Eq2.     
    symmetry in Eq2.
    rewrite Nat.div_small_iff in Eq2 by omega.
    rewrite Nat.div_small_iff in Eq1 by omega.
    rewrite 2 Nat.mod_small; trivial.
    clra.
  + assert (x / m = 0) by omega. clear Eq1.
    rewrite H in Eq2. clear H.
    assert (y / n <> 0) by omega. clear Eq2.
    rewrite Nat.div_small_iff in H by omega.
    rewrite Cmult_0_l.
    destruct WF with (x := x) (y := y). omega.
    reflexivity.
  + rewrite andb_false_r.
    assert (x / m <> 0) by omega. clear Eq1.
    rewrite Nat.div_small_iff in H by omega.
    rewrite Cmult_0_l.
    destruct WF with (x := x) (y := y). omega.
    reflexivity.
Qed.

Theorem transpose_involutive : forall (m n : nat) (A : Matrix m n), (A⊤)⊤ = A.
Proof. reflexivity. Qed.

Lemma conj_involutive : forall c, Cconj (Cconj c) = c.
Proof. intros. clra. Qed.

Theorem conj_transpose_involutive : forall (m n : nat) (A : Matrix m n), A†† = A.
Proof. intros. mlra. Qed.  

Lemma id_transpose_eq : forall n, (Id n)⊤ = (Id n).
Proof.
  intros n. unfold transpose, Id.
  prep_matrix_equality.
  bdestruct (y =? x); bdestruct (x =? y); bdestruct (y <? n); bdestruct (x <? n);
    trivial; omega.
Qed.

Lemma id_conj_transpose_eq : forall n, (Id n)† = (Id n).
Proof.
  intros n.
  unfold conj_transpose, Id.
  prep_matrix_equality.
  bdestruct (y =? x); bdestruct (x =? y); bdestruct (y <? n); bdestruct (x <? n);
    try omega; clra.
Qed.

Theorem Mplus_comm : forall (m n : nat) (A B : Matrix m n), A .+ B = B .+ A.
Proof.
  unfold Mplus. 
  intros m n A B.
  prep_matrix_equality.
  apply Cplus_comm.
Qed.


Theorem Mplus_assoc : forall (m n : nat) (A B C : Matrix m n), A .+ B .+ C = A .+ (B .+ C).
Proof.
  unfold Mplus. 
  intros m n A B C.
  prep_matrix_equality.
  rewrite Cplus_assoc.
  reflexivity.
Qed.

Theorem Mmult_assoc : forall (m n o p : nat) (A : Matrix m n) (B : Matrix n o) 
  (C: Matrix o p), A × B × C = A × (B × C).
Proof.
  intros m n o p A B C.
  unfold Mmult.
  prep_matrix_equality.
  induction n.
  + simpl.
    clear B.
    induction o. reflexivity.
    simpl. rewrite IHo. clra.
  + simpl. 
    rewrite <- IHn.
    simpl.
Admitted.

Lemma Rsum_eq : forall f g k, f = g -> Rsum_to_n f k = Rsum_to_n g k.
Proof. intros f g k H. subst. reflexivity. Qed.

Lemma Rsum_add : forall f g k, 
                   (Rsum_to_n (fun x => f x + g x) k = Rsum_to_n f k + Rsum_to_n g k)%C.
Proof.
  intros f g k.
  induction k.
  + simpl. clra.
  + simpl. rewrite IHk. clra.
Qed.

Lemma Mmult_plus_distr_l : forall (m n o : nat) (A : Matrix m n) (B C : Matrix n o), 
                           A × (B .+ C) = A × B .+ A × C.
Proof. 
  intros m n o A B C.
  unfold Mplus, Mmult.
  prep_matrix_equality.
  rewrite <- Rsum_add.
  apply Rsum_eq.
  apply functional_extensionality. intros z.
  rewrite Cmult_plus_distr_l. 
  reflexivity.
Qed.

Lemma Mmult_plus_distr_r : forall (m n o : nat) (A B : Matrix m n) (C : Matrix n o), 
                           (A .+ B) × C = A × C .+ B × C.
Proof. 
  intros m n o A B C.
  unfold Mplus, Mmult.
  prep_matrix_equality.
  rewrite <- Rsum_add.
  apply Rsum_eq.
  apply functional_extensionality. intros z.
  rewrite Cmult_plus_distr_r. 
  reflexivity.
Qed.

(* These are easy - just haven't done them *)
Lemma Mscale_mult_dist_l : forall (m n o : nat) (x : C) (A : Matrix m n) (B : Matrix n o), ((x .* A) × B) = x .* (A × B).
Proof.
  intros m n o x A B.
  unfold scale, Mmult.
Admitted.

Lemma Mscale_mult_dist_r : forall (m n o : nat) (x : C) (A : Matrix m n) (B : Matrix n o), (A × (x .* B)) = x .* (A × B).
Admitted.

(* Inverses of square matrices *)

Definition Minv {n : nat} (A B : Square n) : Prop := A × B = Id n /\ B × A = Id n.

Lemma Minv_unique : forall (n : nat) (A B C : Square n), 
                      WF_Matrix n n A -> WF_Matrix n n B -> WF_Matrix n n C ->
                      Minv A B -> Minv A C -> B = C.
Proof.
  intros n A B C WFA WFB WFC [HAB HBA] [HAC HCA].
  replace B with (B × Id n) by (apply Mmult_1_r; assumption).
  rewrite <- HAC.  
  replace C with (Id n × C) at 2 by (apply Mmult_1_l; assumption).
  rewrite <- HBA.  
  rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma Minv_symm : forall (n : nat) (A B : Square n), Minv A B -> Minv B A.
Proof. unfold Minv; intuition. Qed.

(* Important but hardish lemma *)
Lemma Minv_flip : forall (n : nat) (A B : Square n), A × B = Id n -> B × A = Id n.
Admitted.
  
Lemma Minv_left : forall (n : nat) (A B : Square n), A × B = Id n -> Minv A B.
Proof.
  intros n A B H. 
  unfold Minv. split; trivial.
  apply Minv_flip.
  assumption.
Qed.

Lemma Minv_right : forall (n : nat) (A B : Square n), B × A = Id n -> Minv A B.
Proof.
  intros n A B H. 
  unfold Minv. split; trivial.
  apply Minv_flip.
  assumption.
Qed.

(* Not generally true, just like sum_sum wasn't.
   A general sum_n_to_m function might have better properties. 
Theorem sum_product : forall (p q : nat) (f : nat -> R), 
  Rsum_to_n f (p * q) = ((Rsum_to_n f p) * (Rsum_to_n f q))%R.
Proof. 
  intros p q f.
  induction p. simpl. lra.
  simpl.
  *)


Lemma kron_mixed_product : forall (m n o p q r : nat) (A : Matrix m n) (B : Matrix p q ) 
  (C : Matrix n o) (D : Matrix q r), (A ⊗ B) × (C ⊗ D) = (A × C) ⊗ (B × D).
Proof.
  intros m n o p q r A B C D.
  unfold kron, Mmult.
  prep_matrix_equality.
  induction n. simpl. 
Admitted.

Theorem kron_transpose : forall (m n o p : nat) (A : Matrix m n) (B : Matrix o p ),
  (A ⊗ B)⊤ = A⊤ ⊗ B⊤.
Proof. reflexivity. Qed.

Lemma conj_mult_dist : forall (x y : C), Cconj (x * y) = (Cconj x * Cconj y)%C.
Proof. intros x y. clra. Qed.
  
Lemma Mmult_conj_transpose : forall (m n o : nat) (A : Matrix m n) (B : Matrix n o),
      (A × B)† = B† × A†.
Admitted.  


Lemma kron_conj_transpose : forall (m n o p : nat) (A : Matrix m n) (B : Matrix o p ),
  (A ⊗ B)† = A† ⊗ B†.
Proof. 
  intros. unfold conj_transpose, kron. 
  prep_matrix_equality.
  setoid_rewrite conj_mult_dist.
  reflexivity.
Qed.

Lemma id_kron : forall (m n : nat),  Id m ⊗ Id n = Id (m * n).
Proof.
  intros.
  unfold Id, kron.
  prep_matrix_equality.
  bdestruct (x =? y); rename H into Eq; subst.
  + repeat rewrite <- beq_nat_refl; simpl.
    destruct n.
    - simpl.
      rewrite mult_0_r.
      bdestruct (y <? 0); try omega.
      autorewrite with C_db; reflexivity.
    - bdestruct (y mod S n <? S n). 
      2: specialize (Nat.mod_upper_bound y (S n)); intros; omega. 
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
    bdestruct (x / n =? y / n); simpl; try clra.
    bdestruct (x mod n =? y mod n); simpl; try clra.
    destruct n; try clra.    
    contradict Eq.
    rewrite (Nat.div_mod x (S n)) by omega.
    rewrite (Nat.div_mod y (S n)) by omega.
    rewrite H, H0; reflexivity.
Qed.


(*  
Theorem Mmult_assoc : forall {m n o p : nat} (A : Matrix m n) (B : Matrix n o) 
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

(*
Unset Maximal Implicit Insertion.

Arguments kron_1_l : clear implicits.
Arguments kron_1_l {m} {n}.
Arguments kron_1_l [m] [n].
Arguments kron_1_l m n.

About kron_1_l.
*)


Hint Rewrite kron_1_l kron_1_r Mmult_1_l Mmult_1_r id_conj_transpose_eq
     Mmult_conj_transpose kron_conj_transpose
     id_conj_transpose_eq conj_transpose_involutive using 
     (auto 100 with wf_db; autorewrite with M_db; auto 100 with wf_db; omega) : M_db.

Ltac destruct_m_1 :=
  match goal with
  | [ |- context[match ?x with 
                 | 0   => _
                 | S _ => _
                 end] ] => is_var x; destruct x
  end.
Ltac destruct_m_eq := repeat (destruct_m_1; simpl).


(* Note on "using [tactics]": Most generated subgoals will be of the form 
   WF_Matrix M, where auto with wf_db will work.
   Occasionally WF_Matrix M will rely on rewriting to match an assumption in the 
   context, here we recursively autorewrite (which adds time). 
   kron_1_l requires proofs of (n > 0)%nat, here we use omega. *)

(* *)