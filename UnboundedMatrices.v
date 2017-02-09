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

(* I won't be using this much, but it can ensure the matrix bounds *)
Definition get {m n} (A : Matrix m n) (a : nat | a < m) (b : nat | b < n) := 
  A (`a) (`b).

Definition list2D_to_matrix (l : list (list R)) : 
  Matrix (length l) (length (hd l [])) :=
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
  | _ => 0%R (* bah. still there *)
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

Definition dot {n : nat} (A : Matrix 1 n) (B : Matrix n 1) :=
  Rsum_to_n (fun x => A O x * B x O)%R n.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun x y => (A x y + B x y)%R.

Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) := 
  fun x z => Rsum_to_n (fun y => A x y * B y z )%R n.

Definition kron {m n o p : nat} (A : Matrix m n) (B : Matrix o p) : 
  Matrix (m*o) (n*p) :=
  fun x y => Rmult (A (x / o) (y / p)) (B (x mod o) (y mod p)).

Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Infix "+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.

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

Lemma Mmult_1_l' : forall {m n x y z : nat} (A : Matrix m n), 
  ((Id m) x y * A y z)%R = if x =? y then A y z else 0%R.
Proof.
  intros m n x y z A.
  unfold Id.
  destruct (x =? y); lra.
Qed.

Lemma Mmult_1_l'': forall {m n : nat} (A : Matrix m n) (x z k : nat), 
  k > 0 ->
  Rsum_to_n (fun y : nat => (Id n x y * A y z)%R) k = if x <? k then 0%R else A k z.  
Proof.
  induction k.
  + omega. 
  + intros. 
    simpl. 
    destruct (x <? k) eqn:ltx.
    - apply Nat.ltb_lt in ltx.
      replace (x <? S k) with true.
      rewrite IHk; [|omega].
      rewrite Rplus_0_l.
      unfold Id. 
      replace (x=?k) with false.
      rewrite Rmult_0_l.
      reflexivity.
      symmetry; apply Nat.eqb_neq; omega.
      symmetry; apply Nat.ltb_lt; omega.
    - rewrite IHk.
      

Search nat "dec".


Lemma Mmult_1_l : forall {m n : nat} (A : Matrix m n), m > 0 ->  Id m × A = A.
Proof.
  intros m n A H.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold Mmult.


    

    rewrite Mmult_1_l'.

    unfold Id in *.
    rewrite IHm.
    destruct (x =? m) eqn:Eq.
    




    destruct (x =? m) eqn:Eq.
    - apply beq_nat_true in Eq; subst.
      assert (Rsum_to_n (fun y0 : nat => Id (S m) m y0 * A y0 y) m = 0)%R as H'.
      2: rewrite H'; lra.
      clear IHm H.
      induction m; trivial. 
      simpl. 
      unfold Id in *. 
      replace (S m =? m) with false. 
      rewrite Rmult_0_l.
      rewrite Rplus_0_r.
      

      


2: simpl. 
Search beq_nat false.


      rewrite IHm.

    rewrite Rmult_0_r.
    rewrite Rplus_0_r.
    apply IHn.
Qed.    




(* *)