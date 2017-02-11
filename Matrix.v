Require Import Program. 
Require Import Reals.
Require Import Psatz.
Require Import Omega.
Require Import List.
Import ListNotations.


(* Require Import ProofIrrelevance. *)

Open Scope R_scope.
Open Scope nat_scope.

Bind Scope R_scope with R.
Bind Scope nat_scope with nat.

(* Nats to Bounded Nats *)

Definition T {b : nat} (a : nat) {pf : a <? b = true} : {x : nat | x < b}.
  exists a; apply Nat.ltb_lt; exact pf.
Defined.

Notation "^ X" := (T X) (at level 1).


Definition Matrix (a b : nat) : Type := {x : nat | x < a} -> {y : nat | y < b} -> R.

(** Some utility operations **)

Program Definition list2D_to_matrix (l : list (list R)) : 
  Matrix (length l) (length (hd [] l)) :=
  fun x y => nth y (nth x l []) 0%R.

Definition M23 : Matrix 2 3 :=
fun x y => 
  match (`x, `y) with
  | (0, 0) => 1%R
  | (0, 1) => 2%R
  | (0, 2) => 3%R
  | (1, 0) => 4%R
  | (1, 1) => 5%R
  | (1, 2) => 6%R
  | _ => 0%R (* bah. still there *)
  end.

Eval simpl in (length (hd [] [[1%R; 2%R; 3%R]; [4%R; 5%R; 6%R]])).

Program Definition M23' : Matrix 2 3 := 
  list2D_to_matrix  
  ([[1; 2; 3];
    [4; 5; 6]])%R.

Lemma M23eq : M23 = M23'.
Proof.
  unfold M23'.
  compute.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  destruct x as [x Px], y as [y Py].
  do 4 (try destruct x; try destruct y; simpl; trivial).
Qed.

Definition M32 : Matrix 3 2 :=
fun x y => 
  match (`x, `y) with
  | (0, 0) => 7%R
  | (0, 1) => 8%R
  | (1, 0) => 9%R
  | (1, 1) => 10%R
  | (2, 0) => 11%R
  | (2, 1) => 12%R
  | _ => 0%R
  end.


Definition proj_row {m n : nat} (r : nat | r < m) (A : Matrix m n) : Matrix 1 n :=
  fun x y => A r y.

Definition proj_col {m n : nat} (c : nat | c < n) (A : Matrix m n) : Matrix m 1 :=
  fun x y => A x c.

Program Definition swap_rows {m n: nat} (r1 r2: { x : nat | x < m}) (A : Matrix m n) : 
  Matrix m n :=
  fun x y => if x =? r1 then A r2 y else 
          if x =? r2 then A r1 y else A x y.

Program Definition swap_cols {m n: nat} (c1 c2 : {x : nat | x < n}) (A : Matrix m n) : 
  Matrix m n :=
  fun x y => if y =? c1 then A x c2 else 
          if y =? c2 then A x c1 else A x y.

Program Definition submatrix {a' b' : nat} (a : nat | a <= a') (b : nat | b <= b') (A : Matrix a' b') : Matrix a b := fun x y => A x y.
Next Obligation. omega. Defined.
Next Obligation. omega. Defined.


(** Matrix Constants and Operations **)

Definition Zero (a b : nat) : Matrix a b := fun x y => 0%R. 

Program Definition Id (n : nat) : Matrix n n := fun x y => if x =? y then 1%R else 0%R.
   
Definition scale {m n : nat} (r : R) (A : Matrix m n) := fun x y => (r * A x y)%R.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n := 
  fun x y => ((A x y) + (B x y))%R.

Program Fixpoint Rsum_to_n {t} (f : { x : nat | x < t} -> R) (n : nat) (P : n <= t) {struct n} : R :=
  match n as m with
  | 0 =>  0%R
  | S n' => Rplus (Rsum_to_n f n' _) (f n')
  end.
Next Obligation. omega. Defined.

Program Fixpoint dot {n} (A : Matrix 1 n) (B: Matrix n 1) := 
  Rsum_to_n (fun x => (Rmult (A 0 x) (B x 0))) n _.  

Program Definition Mmult {m n p : nat} (A : Matrix m n) (B: Matrix n p) : Matrix m p :=
  fun x z => Rsum_to_n (fun y => (Rmult (A x y) (B y z))) n _.

Program Definition kron {m n o p : nat} (A : Matrix m n) (B: Matrix o p) : Matrix (m*o) (n*p) := fun x y => Rmult (A (x / o) (y / p)) (B (x mod o) (y mod p)).
Next Obligation. simpl. apply Nat.div_lt_upper_bound. intros eq; subst. omega. 
                 rewrite Nat.mul_comm. omega. Defined.
Next Obligation. simpl. apply Nat.div_lt_upper_bound. intros eq; subst. omega. 
                 rewrite Nat.mul_comm. omega. Defined.
Next Obligation. simpl. apply Nat.mod_upper_bound. destruct o; omega. Defined.
Next Obligation. simpl. apply Nat.mod_upper_bound. destruct p; omega. Defined.

Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Infix "+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.

Open Scope matrix_scope.

Theorem Mplus_0_l : forall {m n} (A : Matrix m n), (Zero m n) + A = A.
Proof.
  intros m n A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold Mplus, Zero.
  apply Rplus_0_l.
Qed.

Theorem Mplus_0_r : forall {m n} (A : Matrix m n), A + (Zero m n) = A.
Proof.
  intros m n A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold Mplus, Zero.
  apply Rplus_0_r.
Qed.

Lemma Mmult_0_l'' : forall {m n o} x z k (A : Matrix n o) (Q : (`k) <= n), 
  Rmult ((Zero m n) x k) (A k z) = 0%R.
Proof.
  destruct k.
  intros A Q.
  unfold Zero.
  rewrite Rmult_0_l.
  reflexivity.
Qed.

Program Lemma Mmult_0_l' : forall {m n o} x z k (A : Matrix n o) (Q : k <= n), 
  Rsum_to_n (fun y => Rmult ((Zero m n) x y) (A y z)) k Q = 0%R.
Proof.
  induction k.
  + simpl. reflexivity.
  + intros A Q. 
    assert (k <= n) as Q' by omega.
    specialize (IHk A).
    simpl. 
    rewrite IHk.
    rewrite Rplus_0_l.
    apply Mmult_0_l''.
    simpl.
    assumption.
Qed.

Program Theorem Mmult_0_l : forall {m n o} (A : Matrix n o), (Zero m n) × A = Zero m o.
Proof.
  intros m n o A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold Mmult.
  unfold Mmult_obligation_1. 
  apply Mmult_0_l'.
Qed.


Lemma Mmult_0_r'' : forall {m n o} x y k (A : Matrix m n) (Q : (`k) <= n), 
  Rmult (A x k) ((Zero n o) k y) = 0%R.
Proof.
  destruct k.
  intros A Q.
  unfold Zero.
  rewrite Rmult_0_r.
  reflexivity.
Qed.

Program Lemma Mmult_0_r' : forall {m n o} x z k (A : Matrix m n) (Q : k <= n), 
  Rsum_to_n (fun y => Rmult (A x y) ((Zero n o) y z)) k Q = 0%R.
Proof.
  induction k.
  + simpl. reflexivity.
  + intros A Q. 
    assert (k <= n) as Q' by omega.
    specialize (IHk A).
    simpl. 
    rewrite IHk.
    rewrite Rplus_0_l.
    apply Mmult_0_r''.
    simpl.
    assumption.
Qed.

Program Theorem Mmult_0_r : forall {m n o} (A : Matrix m n), A × (Zero n o) = Zero m o.
Proof.
  intros m n o A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold Mmult.
  unfold Mmult_obligation_1. 
  apply Mmult_0_r'.
Qed.

(* Works in unbounded case, here in progress. *)
Program Lemma Mmult_1_l_gen: forall {m n : nat} (A : Matrix m n) x z k P Q, 
  (k <= `x -> Rsum_to_n (fun y => (Id m x y * A y z)%R) k P = 0%R) /\
  (k > `x -> Rsum_to_n (fun y => (Id m x y * A y z)%R) k Q = A x z).
Proof.  
  intros m n A x z k P Q.
  induction k.
  simpl. split. reflexivity. omega.
  edestruct IHk as [IHl IHr].
  split.
  + intros leSkx.
    simpl.
    unfold Id.
    replace (`x =? k) with false by (symmetry; apply Nat.eqb_neq; omega).
    simpl.
    destruct x, z.
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


Theorem Mmult_left_id : forall {m n} (A : Matrix m n),
  (Id m) × A = A.
Proof. 
  intros m n A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.

  destruct x as [x Px], y as [y Py].


  destruct m.
  + inversion x; omega.
  + simpl.
    induction m.
    - simpl. 
      unfold Id.
      simpl.
      destruct x.
      * simpl. rewrite Rmult_1_l.
        replace (le_n 1) with Px by (apply proof_irrelevance).
        reflexivity.
      * contradict Px. omega.
    - simpl. 
      unfold Id; simpl.
      destruct (x =? S m) eqn:xeq.
      * (* last row/column *)
        apply beq_nat_true in xeq. subst.
        rewrite Rmult_1_l.
        replace (le_n (S (S m))) with Px by (apply proof_irrelevance).
        replace (Mmult' (S m) m y
                        (fun (x : {x : nat | (x < S (S m))%nat})
                           (y0 : {y0 : nat | (y0 < S (S m))%nat}) =>
                           if ` x =? ` y0 then 1 else 0) A)%R with 0%R.
        rewrite Rplus_0_l. reflexivity.

        
        clear IHm.
        induction m.
        simpl. rewrite Rmult_0_l. reflexivity.       
        assert (n <= n) as leNN by omega.
        assert (S (S m) <= S ( S ( S m))) as lemSm by omega.
        assert ((S m) < S ( S m)) as lemSm2 by omega.
        specialize (IHm (@submatrix (S (S (S m))) n (S (S m)) n lemSm leNN  A)).
        specialize (IHm lemSm2).

        


Definition M22 : Matrix 2 2 :=
fun x y => 
  match (`x, `y) with
  | (0, 0) => 1%R
  | (0, 1) => 2%R
  | (1, 0) => 3%R
  | (1, 1) => 4%R
  | _ => 0%R
  end.

(* We *can* eliminate the last case, but it's messy... *)
Program Definition M22' : Matrix 2 2 :=
fun x y => 
  match (x, y) with
  | (exist _ 0 P, exist _ 0 Q) => 1%R
  | (exist _ 0 P, exist _ 1 Q) => 2%R
  | (exist _ 1 P, exist _ 0 Q) => 3%R
  | (exist _ 1 P, exist _ 1 Q) => 4%R
  | (exist _ m P, exist _ n Q) => _
  end.
Next Obligation. 
  destruct x as [|x'], y as [|y'].
  edestruct H2; reflexivity.
  destruct y'; [|omega]. edestruct H; reflexivity.
  destruct x'; [|omega]. edestruct H0; reflexivity.
  destruct x', y'; [|omega|omega|omega]. edestruct H1; reflexivity.
Defined.
Next Obligation. contradict Q. omega. Defined.
Next Obligation. contradict Q. omega. Defined.
Next Obligation. contradict P. omega. Defined.

Print C'.



(*)