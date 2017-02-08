Require Import Program. 
Require Import Reals.
Require Import Psatz.
Require Import Omega.

Require Import ProofIrrelevance.

Open Scope R_scope.
Open Scope nat_scope.

Bind Scope R_scope with R.
Bind Scope nat_scope with nat.

Check 0.
Definition foo : R := 0.
Check foo.

(* Bounded Nats *)

(* Nats to Bounded Nats *)

Definition T {b : nat} (a : nat) {pf : a <? b = true} : {x : nat | x < b}.
  exists a; apply Nat.ltb_lt; exact pf.
Defined.

Notation "^ X" := (T X) (at level 1).

(* This kind of forces the check - but Coq can't infer B *)
(* Notation "! B , X" := (@T _ X (eq_refl true)) (at level 1). *)

Check ^4.
Check `^4.


Definition Matrix (a b : nat) : Type := {x : nat | x < a} -> {y : nat | y < b} -> R.

Check Matrix 3 3.    

Definition Zero (a b : nat) : Matrix a b := fun x y => 0%R. 

Check Zero 2 2.
Compute Zero 2 2.

Definition Id (n : nat) : Matrix n n := 
  fun x y => if `x =? `y then 1%R else 0%R.

Check Id 3.
Compute Id 3.
   
Definition scale {m n : nat} (r : R) (A : Matrix m n) := 
  fun x y => (r * A x y)%R.

Check Id 2.
Eval compute in scale 3 (Id 2).
Eval compute in (Id 2) ^0 ^0.
Eval compute in scale 3 (Id 2) ^0 ^0.
Eval compute in scale 3 (Id 2) ^0 ^1.
Eval compute in scale 3 (Id 2) ^0 ^12. (* hmmmm *)
(* Set Printing All. *)
Check (@T 12 22 _).

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun x y => ((A x y) + (B x y))%R.

Definition proj_row {m n : nat} (r : nat | r < m) (A : Matrix m n) : Matrix 1 n :=
  fun x y => A r y.

Definition proj_col {m n : nat} (c : nat | c < n) (A : Matrix m n) : Matrix m 1 :=
  fun x y => A x c.

Definition submatrix {a' b' : nat} (a b : nat) {v1' : a <= a'} {v2' : b <= b'}  (A : Matrix a' b') : Matrix a b. 
  refine (fun x y => A _ _).
  exists (`x). destruct x. simpl. omega.
  exists (`y). destruct y. simpl. omega.
Defined.  

(*
Lemma submatrix_eq : forall m n a b (A : Matrix m n) (x : nat | x < a) (y : nat | y < b),
  (submatrix a b A) x y = A ^(`x) ^(`y).
*)

(* Sum to n, inclusive 
Fixpoint Rsum_to_n (f : nat -> R) (n : nat) : R :=
  match n with 
  | 0 => f 0
  | S n' => (Rsum_to_n f n') + f n
  end.

(* Sum to n, exclusive (hence slightly weird) *) 
Fixpoint Rsum_to_n (f : nat -> R) (n : nat) : R :=
  match n with 
  | 0 => 0
  | S n' => (Rsum_to_n f n') + f n'
  end.
*)

Program Fixpoint Rsum_to_BN {t} (f : { x : nat | x < t} -> R) (n : nat) (P : n <= t) {struct n} : R :=
  match n as m with
  | 0 =>  0%R
  | S n' => Rplus (Rsum_to_BN f n' _) (f n')
  end.
Next Obligation. omega. Defined.

Program Fixpoint dot {n} (A : Matrix 1 n) (B: Matrix n 1) := 
  Rsum_to_BN (fun x => (Rmult (A 0 x) (B x 0))) n _.  

(* Initial approach:
Program Fixpoint dot' {n} (m : nat) {lt: m < n} (A : Matrix 1 n) (B: Matrix n 1): R :=
  match m with
  | 0    => (A 0 0) * (B 0 0)  
  | S m' => (dot' m' A B) + (A 0 m) * (B m 0)
  end. 
Next Obligation. omega. Defined.
  
Program Fixpoint dot {n : nat} (A : Matrix 1 n) (B: Matrix n 1) {struct n} : R := 
  match n with 
  | 0 => 0
  | S n' => dot' n' A B
  end.
*)

Program Definition Mmult {m n p : nat} (A : Matrix m n) (B: Matrix n p) : Matrix m p :=
  fun x z => @Rsum_to_BN n (fun y => (Rmult (A x y) (B y z))) n _.

(* Uses dot and proj:
Definition Mmult {m n p : nat} (A : Matrix m n) (B: Matrix n p) : Matrix m p :=
  fun x y => dot (proj_row x A) (proj_col y B).
*)

(* Uses the Mmult helper function:
Program Fixpoint Mmult' (m' n' o' : nat) {m n o : nat} 
  {ltm: m' < m}  {ltn : n' < n} {lto : o' < o} (A : Matrix m n) (B: Matrix n o) : R :=
  match n' with
  | 0    => (A m' 0) * (B 0 o')  
  | S n'' => (Mmult' m' n'' o' A B) + (A m' n') * (B n' o')
  end. 
Next Obligation. omega. Defined.

Program Definition Mmult {m n p : nat} (A : Matrix m n) (B: Matrix n p) : Matrix m p :=
  match n with 
  | 0 => Zero m p
  | S n' => (fun x y => @Mmult' x n' y _ _ _ _ _ _ A B)
  end.
*)


Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Infix "+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.

Open Scope matrix_scope.

Definition A : Matrix 2 3 :=
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

Definition B : Matrix 3 2 :=
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

Eval compute in proj_col ^1 B.
Eval compute in proj_row ^1 A.

Eval compute in (A × B).  
Eval compute in (A × B) ^0 ^0. (* 58 *)
Eval compute in (A × B) ^0 ^1. (* 64 *)
Eval compute in (A × B) ^1 ^0. (* 139 *)
Eval compute in (A × B) ^1 ^1. (* 154 *)

Eval compute in (B × A).  
Eval compute in (B × A) ^2 ^2.  

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

(* For the previous Mmult:
Lemma Mmult_0_l' : forall a b c m n o A lta ltb ltc,
  @Mmult' a b c m n o lta ltb ltc (Zero m n) A = 0%R.
Proof.
  intros.
  induction b.
  + simpl.
    unfold Zero.
    apply Rmult_0_l.
  + simpl.
    unfold Zero in *.
    rewrite Rmult_0_l.
    rewrite Rplus_0_r.
    apply IHb.
Qed.    

Theorem Mmult_0_l : forall {m n o} (A : Matrix n o), (Zero m n) × A = Zero m o.
Proof.
  intros m n o A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  induction n.
  + simpl. reflexivity.
  + unfold Mmult.
    apply Mmult_0_l'.
Qed.

Lemma Mmult_0_r' : forall a b c m n o A lta ltb ltc,
  @Mmult' a b c m n o lta ltb ltc A (Zero n o) = 0%R.
Proof.
  intros.
  induction b.
  + simpl.
    unfold Zero.
    apply Rmult_0_r.
  + simpl.
    unfold Zero in *.
    rewrite Rmult_0_r.
    rewrite Rplus_0_r.
    apply IHb.
Qed.    

Theorem Mmult_0_r : forall {m n o} (A : Matrix m n), A × (Zero n o) = Zero m o.
Proof.
  intros m n o A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  induction n.
  + simpl. reflexivity.
  + unfold Mmult.
    apply Mmult_0_r'.
Qed.

*)

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
  Rsum_to_BN (fun y => Rmult ((Zero m n) x y) (A y z)) k Q = 0%R.
Proof.
  induction k.
  + simpl. reflexivity.
  + intros A Q. 
    Search le nat (S _). 
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
  Rsum_to_BN (fun y => Rmult (A x y) ((Zero n o) y z)) k Q = 0%R.
Proof.
  induction k.
  + simpl. reflexivity.
  + intros A Q. 
    Search le nat (S _). 
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


(*
Program Theorem Mmult_left_id' : forall (a b x m n : nat) (A : Matrix (S m) n)
   {lta : a < S m} {ltm : m < S m} {ltb: b < n},
   @Mmult' a m b _ _ _ lta ltm ltb (Id (S m)) A = A a b.
*)

(*
Program Lemma mult_by_part_of_id : forall m y n o A lt1 lt2 lt3,
    @Mmult' (S m) m y (S (S m)) n o lt1 lt2 lt3 (Id (S (S m))) A = 0%R.
*)

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

        
(* Also commuted, for convenience *)
Lemma div_lt_upper_bound_strict : forall a b q : nat, a < q * b -> a / b < q.
Proof.
  intros a b q H. 
  apply Nat.div_lt_upper_bound.
  intros Eq.
  rewrite Eq in H.
  omega.
  rewrite Nat.mul_comm.
  assumption.
Qed.

Program Definition kron {m n o p : nat} (A : Matrix m n) (B: Matrix o p) : Matrix (m*o) (n*p) := fun x y => Rmult (A (x / o) (y / p)) (B (x mod o) (y mod p)).
Next Obligation. simpl. apply div_lt_upper_bound_strict. assumption. Defined.
Next Obligation. simpl. apply div_lt_upper_bound_strict. assumption. Defined.
Next Obligation. simpl. apply Nat.mod_upper_bound. destruct o; omega. Defined.
Next Obligation. simpl. apply Nat.mod_upper_bound. destruct p; omega. Defined.

Definition C : Matrix 2 2 :=
fun x y => 
  match (`x, `y) with
  | (0, 0) => 1%R
  | (0, 1) => 2%R
  | (1, 0) => 3%R
  | (1, 1) => 4%R
  | _ => 0%R
  end.


(*
Lemma lt01 : 0 < 1. Proof. omega. Qed.
Lemma lt12 : 1 < 2. Proof. omega. Qed.
Lemma lt02 : 0 < 2. Proof. omega. Qed.
*)

(* We *can* eliminate the last case, but it's messy... *)
Program Definition C' : Matrix 2 2 :=
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


Definition D : Matrix 2 2 :=
fun x y => 
  match (`x, `y) with
  | (0, 0) => 0%R
  | (0, 1) => 5%R
  | (1, 0) => 6%R
  | (1, 1) => 7%R
  | _ => 0%R
  end.

Eval compute in (kron C D ^1 ^2).
Eval compute in (kron C' D ^1 ^2).
Eval compute in (kron C D ^1 ^5).
Eval compute in (kron C' D ^1 ^5). (* hmm... *)



Definition swap_rows {m n: nat} (r1 r2: { x : nat | x < m}) (A : Matrix m n) : Matrix m n :=
  fun x y => if `x =? `r1 then A r2 y else 
          if `x =? `r2 then A r1 y else A x y.

Definition swap_cols {m n: nat} (c1 c2 : {x : nat | x < n})  
(A : Matrix m n) : Matrix m n :=
  fun x y => if `y =? `c1 then A x c2 else 
          if `y =? `c2 then A x c1 else A x y.

Eval compute in (swap_rows ^0 ^1 B) ^0 ^0.
Eval compute in (swap_rows ^0 ^1 B) ^1 ^0.

Eval compute in (swap_cols ^0 ^1 B) ^0 ^0.
Eval compute in (swap_cols ^0 ^1 B) ^1 ^0.

Check (swap_cols ^0 ^3 B).
Eval compute in (swap_cols ^0 ^3 B) ^0 ^1.


(*)