Require Export Reals.
Require Export Psatz.
Require Import Omega.

Open Scope nat_scope.
Bind Scope R_scope with R.


Definition Matrix (a b : nat) : Type := {x : nat | x < a} -> {y : nat | y < b} -> R.

Check Matrix 3 3.    

Definition Zero (a b : nat) : Matrix a b := fun x y => 0%R. 

Check Zero 2 2.
Compute Zero 2 2.

(* Bounded Nats to Nats *)
Definition p1 {P : nat -> Prop} (e:sig P) := proj1_sig e.
Definition p2 {P : nat -> Prop} (e:sig P) := proj2_sig e.

Notation "` X" := (p1 X) (at level 1).

Definition four : {x : nat | x < 10}. exists 4. omega. Defined.

Check four.
Check `four.
Check p1 four.
Check p2 four.
Compute p1 four.
Compute p2 four.
Print four.

(* Nats to Bounded Nats *)

Definition T {b : nat} (a : nat) {pf : a <? b = true} : {x : nat | x < b}.
  exists a; apply Nat.ltb_lt; exact pf.
Defined.

Check (@T 1 2 _).
Check (@T 2 1 _).

Notation "^ X" := (T X) (at level 1).


Definition four' := @T 4 10.

(* This kind of forces the check - but Coq can't infer B *)
(*
Notation "! B , X" := (@T _ X (eq_refl true)) (at level 1).
Check ! 10 , 4.
(* Check ! 4 , 5. *)
*)

Check ^4.
Check `^4.


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

Definition submatrix {a' b' : nat} (a b : nat) {v1' : a <= a'} {v2' : b <= b'}  (A : Matrix a' b') : Matrix a b. 
  refine (fun x y => A _ _).
  exists `x. destruct x. simpl. omega.
  exists `y. destruct y. simpl. omega.
Defined.  

Program Fixpoint dot {n : nat} (A : Matrix 1 n) (B: Matrix n 1) {struct n} : R := 
  match n with
  | O    => 0%R
  | S n' => ((A 0 n') * (B n' 0)) +
           (dot (submatrix 1 n' A) (submatrix n' 1 B))
  end. 

Check dot.

(* Want refine-free version:
Fixpoint dot {n : nat} (A : Matrix 1 n) (B: Matrix n 1) {struct n}: R :=
  match n with
  | O    => 0
  | S n' => A 0 n' (Nat.lt_0_1) (Nat.lt_succ_diag_r n') * B n' 0 
           + dot (submatrix 1 n' A) (submatrix n' 1 B) 
  end.
*)

Definition proj_row {m n : nat} (r : nat | r < m) (A : Matrix m n) : Matrix 1 n :=
  fun x y => A r y.

Definition proj_col {m n : nat} (c : nat | c < n) (A : Matrix m n) : Matrix m 1 :=
  fun x y => A x c.

Definition Mmult {m n p : nat} (A : Matrix m n) (B: Matrix n p) : Matrix m p :=
  fun x y => dot (proj_row x A) (proj_col y B).

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

Eval compute in (Mmult A B).  
Eval compute in (Mmult A B) ^0 ^0. (* 58 *)
Eval compute in (Mmult A B) ^0 ^1. (* 64 *)
Eval compute in (Mmult A B) ^1 ^0. (* 139 *)
Eval compute in (Mmult A B) ^1 ^1. (* 154 *)

Eval compute in (Mmult B A).  
Eval compute in (Mmult B A) ^2 ^2.  

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