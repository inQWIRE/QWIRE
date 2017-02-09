Require Import Program. 
Require Import Reals.
Require Import Psatz.
Require Import Omega.
Require Import List.
Import ListNotations.

Open Scope R_scope.
Open Scope nat_scope.

Bind Scope R_scope with R.
Bind Scope nat_scope with nat.


Definition Matrix (m n : nat) := nat -> nat -> R. 

Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop := 
  forall (x : nat | x < m) (y : nat | y < n), (A (`x) (`y)) = (B (`x) (`y)).

(* I won't be using this much, but it can ensure the matrix bounds *)
Definition get {m n} (A : Matrix m n) (a : nat | a < m) (b : nat | b < n) := 
  A (`a) (`b).

Definition list2D_to_matrix (l : list (list R)) : 
  Matrix (length l) (length (hd [] l)) :=
  fun x y => nth y (nth x l []) 0%R.

Definition M23 : Matrix 2 3 :=
fun x y => 
  match (x, y) with
  | (0, 0) => 1%R
  | (0, 1) => 2%R
  | (0, 2) => 3%R
  | (1, 0) => 4%R
  | (1, 1) => 5%R
  | (1, 2) => 6%R
  | _ => 0%R
  end.

Definition M23' := 
  list2D_to_matrix  
  ([[1; 2; 3];
    [4; 5; 6]])%R.

Lemma M23eq : M23 = M23'.
Proof.
  unfold M23'.
  compute.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  do 4 (try destruct x; try destruct y; simpl; trivial).
Qed.


Definition Zero (m n : nat) : Matrix m n := fun x y => 0%R.

Definition Id (n : nat) : Matrix n n := fun x y => if (x =? y) then 1%R else 0%R.
(* or if (x =? y) && (x <? n) then *)

(* to n exclusive *)
Fixpoint Rsum_to_n (f : nat -> R) (n : nat) := 
  match n with
  | 0 => 0%R
  | S n' => (Rsum_to_n f n' +  f n')%R
  end.

(* to n inclusive *)
Fixpoint Rsum_to_n_in (f : nat -> R) (n : nat) := 
  match n with
  | 0 => f 0
  | S n' => (Rsum_to_n f n' +  f n')%R
  end.

Definition scale {m n : nat} (r : R) (A : Matrix m n) := 
  fun x y => (r * A x y)%R.

Definition dot {n : nat} (A : Matrix 1 n) (B : Matrix n 1) : R :=
  Rsum_to_n (fun x => A O x * B x O)%R n.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun x y => (A x y + B x y)%R.

Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o := 
  fun x z => Rsum_to_n (fun y => A x y * B y z )%R n.

Definition kron {m n o p : nat} (A : Matrix m n) (B : Matrix o p) : 
  Matrix (m*o) (n*p) :=
  fun x y => Rmult (A (x / o) (y / p)) (B (x mod o) (y mod p)).

Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Infix "+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Infix "≡" := mat_equiv (at level 100) : matrix_scope.

Open Scope matrix_scope.

Lemma Mplus_0_l : forall {m n : nat} (A : Matrix m n), Zero m n + A = A.
Proof.
  intros m n A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold Zero, Mplus.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Lemma Mplus_0_r : forall {m n : nat} (A : Matrix m n), A + Zero m n = A.
Proof.
  intros m n A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold Zero, Mplus.
  rewrite Rplus_0_r.
  reflexivity.
Qed.

Program Lemma Mmult_0_l : forall {m n o : nat} (A : Matrix n o), (Zero m n) × A = Zero m n.
Proof.
  intros m n o A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold Zero, Mmult.
  induction n.
  + simpl. reflexivity.
  + simpl. 
    rewrite Rmult_0_l.
    rewrite Rplus_0_r.
    apply IHn.
Qed.    

Program Lemma Mmult_0_r : forall {m n o : nat} (A : Matrix m n), A × Zero n o = Zero n o.
Proof.
  intros m n o A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold Zero, Mmult.
  induction n.
  + simpl. reflexivity.
  + simpl. 
    rewrite Rmult_0_r.
    rewrite Rplus_0_r.
    apply IHn.
Qed.    

(* using <= because our form Rsum_to_n is exclusive. *)
Lemma Mmult_1_l_gen: forall {m n : nat} (A : Matrix m n) (x z k : nat), 
  (k <= x -> Rsum_to_n (fun y : nat => (Id m x y * A y z)%R) k = 0%R) /\
  (k > x -> Rsum_to_n (fun y : nat => (Id m x y * A y z)%R) k = A x z).
Proof.  
  intros m n A x z k.
  induction k.
  simpl. split. reflexivity. omega.
  destruct IHk as [IHl IHr].
  split.
  + intros leSkx.
    simpl.
    unfold Id.
    replace (x =? k) with false by (symmetry; apply Nat.eqb_neq; omega).
    rewrite Rmult_0_l, Rplus_0_r.
    apply IHl.
    omega.
  + intros gtSkx.
    simpl. 
    unfold Id in *.
    destruct (x =? k) eqn:Eqxk.
    - apply Nat.eqb_eq in Eqxk; subst.
      rewrite Rmult_1_l.
      rewrite IHl; try omega.
      rewrite Rplus_0_l.     
      reflexivity.
    - apply Nat.eqb_neq in Eqxk; subst.
      rewrite Rmult_0_l.
      rewrite Rplus_0_r.
      apply IHr.
      omega.
Qed.

Lemma Mmult_1_l : forall {m n : nat} (A : Matrix m n), Id m × A ≡ A.
Proof.
  intros m n A x y.
  destruct x as [x Px], y as [y Py].
  simpl. 
  unfold Mmult.
  edestruct (@Mmult_1_l_gen m n) as [Hl Hr].
  apply Hr.
  omega.
Qed.  

Lemma Mmult_1_r_gen: forall {m n : nat} (A : Matrix m n) (x z k : nat), 
  (k <= z -> Rsum_to_n (fun y : nat => (A x y * Id m y z)%R) k = 0%R) /\
  (k > z -> Rsum_to_n (fun y : nat => (A x y * Id m y z)%R) k = A x z).
Proof.  
  intros m n A x z k.
  induction k.
  simpl. split. reflexivity. omega.
  destruct IHk as [IHl IHr].
  split.
  + intros leSkz.
    simpl.
    unfold Id.
    replace (k =? z) with false by (symmetry; apply Nat.eqb_neq; omega).
    rewrite Rmult_0_r, Rplus_0_r.
    apply IHl.
    omega.
  + intros gtSkz.
    simpl. 
    unfold Id in *.
    destruct (k =? z) eqn:Eqxk.
    - apply Nat.eqb_eq in Eqxk; subst.
      rewrite Rmult_1_r.
      rewrite IHl; try omega.
      rewrite Rplus_0_l.     
      reflexivity.
    - apply Nat.eqb_neq in Eqxk; subst.
      rewrite Rmult_0_r.
      rewrite Rplus_0_r.
      apply IHr.
      omega.
Qed.

Lemma Mmult_1_r : forall {m n : nat} (A : Matrix m n), A × Id n ≡ A.
Proof.
  intros m n A x y.
  destruct x as [x Px], y as [y Py].
  simpl. 
  unfold Mmult.
  edestruct (@Mmult_1_r_gen m n) as [Hl Hr].
  apply Hr.
  omega.
Qed.  


(* *)