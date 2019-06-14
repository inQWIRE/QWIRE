Require Import Psatz.
Require Import String.
Require Import Program.
Require Export Complex.
Require Import List.
Require Import Setoid.


(* TODO: Use matrix equality everywhere, declare equivalence relation *)
(* TODO: Make all nat arguments to matrix lemmas implicit *)

(** * Matrix Definitions and Infrastructure **)

Local Open Scope nat_scope.

Definition Matrix (m n : nat) := nat -> nat -> C.

Arguments Matrix m%nat n%nat.

Notation Vector n := (Matrix n 1).
Notation Square n := (Matrix n n).

(* We will try not to use this definition, in general. *)
Definition WF_Matrix {m n: nat} (A : Matrix m n) : Prop := 
  forall x y, x >= m \/ y >= n -> A x y = C0. 

Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop := 
  forall i j, i < m -> j < n -> A i j = B i j.

Infix "==" := mat_equiv (at level 80) : matrix_scope.
Open Scope matrix_scope.

Lemma mat_equiv_refl : forall {m n} (A : Matrix m n), A == A.
Proof. intros m n A i j Hi Hj. reflexivity. Qed.

Lemma mat_equiv_sym : forall {m n} (A B : Matrix m n), A == B -> B == A.
Proof.
  intros m n A B H i j Hi Hj.
  rewrite H; easy.
Qed.

Lemma mat_equiv_trans : forall {m n} (A B C : Matrix m n),
    A == B -> B == C -> A == C.
Proof.
  intros m n A B C HAB HBC i j Hi Hj.
  rewrite HAB; trivial.
  apply HBC; easy.
Qed.

Add Parametric Relation m n : (Matrix m n) (@mat_equiv m n)
  reflexivity proved by mat_equiv_refl
  symmetry proved by mat_equiv_sym
  transitivity proved by mat_equiv_trans
    as mat_equiv_rel.

Lemma mat_equiv_ex : forall {m n} (A B C : Matrix m n),
    A == B -> A == C -> B == C.
Proof.
  intros m n A B C HAB HAC.
  rewrite <- HAB.
  apply HAC.
Qed.

Lemma mat_equiv_eq : forall {m n : nat} (A B : Matrix m n),
  WF_Matrix A -> 
  WF_Matrix B -> 
  mat_equiv A B ->
  A = B.
Proof.
  intros m n A' B' WFA WFB Eq.
  apply functional_extensionality; intros i.
  apply functional_extensionality; intros j. 
  unfold mat_equiv in Eq.
  bdestruct (i <? m).
  bdestruct (j <? n).
  + apply Eq; easy. 
  + rewrite WFA, WFB; trivial; right; try lia.
  + rewrite WFA, WFB; trivial; left; try lia.
Qed.

(** ** Interpretation Scopes *)

Open Scope nat_scope.
Open Scope R_scope.
Open Scope C_scope.
Bind Scope matrix_scope with Matrix.
Delimit Scope matrix_scope with M.
Open Scope matrix_scope.

(** ** Printing Matrices *)

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

(** ** 2D List Representation *)
    
Definition list2D_to_matrix (l : list (list C)) : 
  Matrix (length l) (length (hd [] l)) :=
  (fun x y => nth y (nth x l []) 0%R).

Lemma WF_list2D_to_matrix : forall m n li, 
    length li = m ->
    (forall li', In li' li -> length li' = n)  ->
    @WF_Matrix m n (list2D_to_matrix li).
Proof.
  intros m n li L F x y [l | r].
  - unfold list2D_to_matrix. 
    rewrite (nth_overflow _ []).
    destruct y; easy.
    rewrite L. apply l.
  - unfold list2D_to_matrix. 
    rewrite (nth_overflow _ C0).
    easy.
    destruct (nth_in_or_default x li []) as [IN | DEF].
    apply F in IN.
    rewrite IN. apply r.
    rewrite DEF.
    simpl; lia.
Qed.

(** Example *)
Definition M23 : Matrix 2 3 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => 1
  | (0, 1) => 2
  | (0, 2) => 3
  | (1, 0) => 4
  | (1, 1) => 5
  | (1, 2) => 6
  | _ => 0
  end.

Definition M23' : Matrix 2 3 := 
  list2D_to_matrix  
  ([[RtoC 1; RtoC 2; RtoC 3];
    [RtoC 4; RtoC 5; RtoC 6]]).

Lemma M23eq : M23 == M23'.
Proof.
  intros i j Hi Hj.
  compute.
  do 4 (try destruct i; try destruct j; simpl; trivial).
Qed.



(** * Operands and Operations **)

(** Because we will use these so often, it is good to have them in matrix scope. *)
Notation "m =? n" := (Nat.eqb m n) (at level 70) : matrix_scope.
Notation "m <? n" := (Nat.ltb m n) (at level 70) : matrix_scope.
Notation "m <=? n" := (Nat.leb m n) (at level 70) : matrix_scope.

Definition Zero {m n : nat} : Matrix m n := fun x y => 0.

Definition I (n : nat) : Square n := fun x y => if (x =? y) then 1 else 0.

Fixpoint Csum (f : nat -> C) (n : nat) : C := 
  match n with
  | 0 => 0
  | S n' => Csum f n' +  f n'
  end.

Definition trace {n : nat} (A : Square n) : C := 
  Csum (fun k => A k k) n.

Definition scale {m n : nat} (r : C) (A : Matrix m n) : Matrix m n := 
  fun i j => (r * A i j)%C.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun i j => A i j + B i j.

Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o := 
  fun i j => Csum (fun k => A i k * B k j) n.

(* Only well-defined when o and p are non-zero *)
Definition kron {m n o p : nat} (A : Matrix m n) (B : Matrix o p) : Matrix (m*o) (n*p) :=
  fun i j => (A (i / o) (j / p))%nat * (B (i mod o) (j mod p))%nat.

Definition transpose {m n} (A : Matrix m n) : Matrix n m := 
  fun i j => A j i.

Definition adjoint {m n} (A : Matrix m n) : Matrix n m := 
  fun i j => (A j i)^*.

(* Old dot: 
Definition dot {n : nat} (A : Vector n) (B : Vector n) : C :=
  Csum (fun i => A i O  * B i O) n. *)

Definition dot {n : nat} (A : Vector n) (B : Vector n) : C :=
  Mmult (transpose A) B O O.

Definition inner_product {n} (u v : Vector n) : C := 
  Mmult (adjoint u) (v) O O.

Definition outer_product {n} (u v : Vector n) : Square n := 
  Mmult u (adjoint v).

(* Kronecker of n copies of A *)
Fixpoint kron_n n {m1 m2} (A : Matrix m1 m2) : Matrix (m1^n) (m2^n) :=
  match n with
  | 0    => I 1
  | S n' => kron A (kron_n n' A)
  end.

(* Kronecker product of a list *)
Fixpoint big_kron {m n} (As : list (Matrix m n)) : 
  Matrix (m^(length As)) (n^(length As)) := 
  match As with
  | [] => I 1
  | A :: As' => kron A (big_kron As')
  end.

(* Infix "≡" := mat_equiv (at level 70) : matrix_scope. *)
Notation "Σ^ n f" := (Csum f n) (at level 60) : matrix_scope.
Infix ".+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix ".*" := scale (at level 40, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope. 
Notation "A †" := (adjoint A) (at level 0) : matrix_scope. 
Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Notation "⟨ A , B ⟩" := (inner_product A B) : matrix_scope.
Notation "n ⨂ A" := (kron_n n A) (at level 30, no associativity) : matrix_scope.
Notation "⨂ A" := (big_kron A) (at level 60): matrix_scope.

Hint Unfold Zero I trace dot Mplus scale Mmult kron transpose adjoint : M_db.

(** ** Matrix Automation 1 *)

Ltac solve_end :=
  match goal with
  | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.
                
Ltac by_cell := 
  intros;
  let i := fresh "i" in 
  let j := fresh "j" in 
  let Hi := fresh "Hi" in 
  let Hj := fresh "Hj" in 
  intros i j Hi Hj; try solve_end;
  repeat (destruct i as [|i]; simpl; [|apply lt_S_n in Hi]; try solve_end); clear Hi;
  repeat (destruct j as [|j]; simpl; [|apply lt_S_n in Hj]; try solve_end); clear Hj.

Ltac lma := by_cell; lca.

(** Test *)                                                     
Lemma test_lma : 0 .* I 4 == Zero.
Proof. lma. Qed.

(* Move to Complex.v later *)
(*********************************)
(** ** Proofs about finite sums **)
(*********************************)

Lemma Csum_0 : forall f n, (forall x, f x = 0) -> Csum f n = 0. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, H. 
    lca.
Qed.

Lemma Csum_1 : forall f n, (forall x, f x = 1) -> Csum f n = INR n. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, H. 
    destruct n; lca.    
Qed.

Lemma Csum_constant : forall c n, Csum (fun x => c) n = INR n * c.
Proof.
  intros c n.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite IHn.
    destruct n; lca.
Qed.

Lemma Csum_eq : forall f g n, f = g -> Csum f n = Csum g n.
Proof. intros f g n H. subst. reflexivity. Qed.

Lemma Csum_0_bounded : forall f n, (forall x, (x < n)%nat -> f x = C0) -> Csum f n = 0. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, H. 
    lca.
    lia.
    intros.
    apply H.
    lia.
Qed.

Lemma Csum_eq_bounded : forall f g n, (forall x, (x < n)%nat -> f x = g x) -> Csum f n = Csum g n.
Proof. 
  intros f g n H. 
  induction n.
  + simpl. reflexivity.
  + simpl. 
    rewrite H by lia.
    rewrite IHn by (intros; apply H; lia).
    reflexivity.
Qed.

Lemma Csum_plus : forall f g n, Csum (fun x => f x + g x) n = Csum f n + Csum g n.
Proof.
  intros f g n.
  induction n.
  + simpl. lca.
  + simpl. rewrite IHn. lca.
Qed.

Lemma Csum_mult_l : forall c f n, c * Csum f n = Csum (fun x => c * f x) n.
Proof.
  intros c f n.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite Cmult_plus_distr_l.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Csum_mult_r : forall c f n, Csum f n * c = Csum (fun x => f x * c) n.
Proof.
  intros c f n.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite Cmult_plus_distr_r.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Csum_conj_distr : forall f n, (Csum f n) ^* = Csum (fun x => (f x)^*) n.
Proof. 
  intros f n.
  induction n.
  + simpl; lca.
  + simpl. 
    rewrite Cconj_plus_distr.
    rewrite IHn.
    reflexivity.
Qed.
    
Lemma Csum_extend_r : forall n f, Csum f n + f n = Csum f (S n).
Proof. reflexivity. Qed.

Lemma Csum_extend_l : forall n f, f O + Csum (fun x => f (S x)) n = Csum f (S n).
Proof.
  intros n f.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite Cplus_assoc.
    rewrite IHn.
    simpl.
    reflexivity.
Qed.

Lemma Csum_unique : forall (f : nat -> C) (k : C) (n x : nat), 
  (x < n)%nat ->
  f x = k ->
  (forall x', x <> x' -> f x' = 0) ->
  Csum f n = k.
Proof.
  intros f k.  
  induction n. 
  - intros x H; lia.
  - intros x H H0 H1.
    simpl.
    destruct (x =? n)%nat eqn:E. 
    + apply Nat.eqb_eq in E. subst.
      rewrite Csum_0_bounded. lca.
      intros x L. apply H1. lia.
    + apply Nat.eqb_neq in E.
      rewrite H1 by lia.
      rewrite (IHn x); trivial.
      lca.
      lia.
Qed.

Lemma Csum_sum : forall m n f, Csum f (m + n) = 
                          Csum f m + Csum (fun x => f (m + x)%nat) n. 
Proof.    
  intros m n f.
  induction m.
  + simpl. rewrite Cplus_0_l. reflexivity. 
  + simpl.
    rewrite IHm.
    repeat rewrite <- Cplus_assoc.
    remember (fun y => f (m + y)%nat) as g.
    replace (f m) with (g O) by (subst; rewrite plus_0_r; reflexivity).
    replace (f (m + n)%nat) with (g n) by (subst; reflexivity).
    replace (Csum (fun x : nat => f (S (m + x))) n) with
            (Csum (fun x : nat => g (S x)) n).
    2:{ apply Csum_eq. subst. apply functional_extensionality.
    intros; rewrite <- plus_n_Sm. reflexivity. }
    rewrite Csum_extend_l.
    rewrite Csum_extend_r.
    reflexivity.
Qed.

Lemma Csum_product : forall m n f g, n <> O ->
                              Csum f m * Csum g n = 
                              Csum (fun x => f (x / n)%nat * g (x mod n)%nat) (m * n). 
Proof.
  intros.
  induction m.
  + simpl; lca.
  + simpl.      
    rewrite Cmult_plus_distr_r.
    rewrite IHm. clear IHm.
    rewrite Csum_mult_l.    
    remember ((fun x : nat => f (x / n)%nat * g (x mod n)%nat)) as h.
    replace (Csum (fun x : nat => f m * g x) n) with
            (Csum (fun x : nat => h ((m * n) + x)%nat) n). 
    2:{
      subst.
      apply Csum_eq_bounded.
      intros x Hx.
      rewrite Nat.div_add_l by assumption.
      rewrite Nat.div_small; trivial.
      rewrite plus_0_r.
      rewrite Nat.add_mod by assumption.
      rewrite Nat.mod_mul by assumption.
      rewrite plus_0_l.
      repeat rewrite Nat.mod_small; trivial. }
    rewrite <- Csum_sum.
    rewrite plus_comm.
    reflexivity.
Qed.

Lemma Csum_ge_0 : forall f n, (forall x, 0 <= fst (f x)) -> 0 <= fst (Csum f n).
Proof.
  intros f n H.
  induction n.
  - simpl. lra. 
  - simpl in *.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat; easy.
Qed.

Lemma Csum_member_le : forall (f : nat -> C) (n : nat), (forall x, 0 <= fst (f x)) -> 
                      (forall x, (x < n)%nat -> fst (f x) <= fst (Csum f n)).
Proof.
  intros f.
  induction n.
  - intros H x Lt. inversion Lt.
  - intros H x Lt.
    bdestruct (Nat.ltb x n).
    + simpl.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat.
      apply IHn; easy.
      apply H.
    + assert (E: x = n) by lia.
      rewrite E.
      simpl.
      rewrite <- Rplus_0_l at 1.
      apply Rplus_le_compat. 
      apply Csum_ge_0; easy.
      lra.
Qed.            

(** ** Compatibility Lemmas *)

Lemma trace_compat : forall {n} (A A' : Square n),
    A == A' -> trace A = trace A'.
Proof.
  intros n A A' H.
  apply Csum_eq_bounded.
  intros x Hx.
  rewrite H; easy.
Qed.

Lemma scale_compat : forall {m n} (c c' : C) (A A' : Matrix m n),
    c = c' -> A == A' -> c .* A == c' .* A'.
Proof.
  intros m n c c' A A' Hc HA.
  intros i j Hi Hj.
  unfold scale.
  rewrite Hc, HA; easy.
Qed.

Lemma Mplus_compat : forall {m n}  (A A' B B': Matrix m n),
  A == A' -> B == B' -> A .+ B ==  A' .+ B'.
Proof.
  intros m n A A' B B' HA HB i j Hi Hj.
  unfold Mplus.
  rewrite HA, HB; try lia.
  easy.
Qed.

Lemma Mmult_compat : forall {m n o} (A A' : Matrix m n) (B B' : Matrix n o),
    A == A' -> B == B' -> A × B == A' × B'.
Proof.
  intros m n o A A' B B' HA HB i j Hi Hj.
  unfold Mmult.
  apply Csum_eq_bounded; intros x Hx.
  rewrite HA, HB; easy.
Qed.

Lemma kron_compat : forall {m n o p} (A A' : Matrix m n) (B B' : Matrix o p),
    A == A' -> B == B' -> A ⊗ B == A' ⊗ B'.
Proof.
  intros m n o p A A' B B' HA HB.
  intros i j Hi Hj.
  unfold kron.
  assert (Ho : o <> O). intros F. rewrite F in *. lia.
  assert (Hp : p <> O). intros F. rewrite F in *. lia.
  rewrite HA, HB. easy.
  - apply Nat.mod_upper_bound; easy.
  - apply Nat.mod_upper_bound; easy.
  - apply Nat.div_lt_upper_bound; lia.
  - apply Nat.div_lt_upper_bound; lia.
Qed.

Lemma transpose_compat : forall {m n} (A A' : Matrix m n),
    A == A' -> A⊤ == A'⊤.
Proof.
  intros m n A A' H.
  intros i j Hi Hj.
  unfold transpose.
  rewrite H; easy.
Qed.

Lemma adjoint_compat : forall {m n} (A A' : Matrix m n),
    A == A' -> A† == A'†.
Proof.
  intros m n A A' H.
  intros i j Hi Hj.
  unfold adjoint.
  rewrite H; easy.
Qed.


Add Parametric Morphism n : (@trace n)
  with signature mat_equiv ==> eq as trace_mor.
Proof. intros; apply trace_compat; easy. Qed.

Add Parametric Morphism m n : (@scale m n)
  with signature eq ==> mat_equiv ==> mat_equiv as Mscale_mor.
Proof. intros; apply scale_compat; easy. Qed.

Add Parametric Morphism m n : (@Mplus m n)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mplus_mor.
Proof. intros. apply Mplus_compat; easy. Qed.

Add Parametric Morphism m n o : (@Mmult m n o)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mmult_mor.
Proof. intros. apply Mmult_compat; easy. Qed.

Add Parametric Morphism m n o p : (@kron m n o p)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as kron_mor.
Proof. intros. apply kron_compat; easy. Qed.

Add Parametric Morphism m n : (@transpose m n)
  with signature mat_equiv ==> mat_equiv as transpose_mor.
Proof. intros. apply transpose_compat; easy. Qed.

Add Parametric Morphism m n : (@adjoint m n)
  with signature mat_equiv ==> mat_equiv as adjoint_mor.
Proof. intros. apply adjoint_compat; easy. Qed.


(** * Matrix Identities **)

Lemma dim0_l : forall {n : nat} (A : Matrix 0 n), A == Zero.
Proof. lma. Qed.

Lemma dim0_r : forall {n : nat} (A : Matrix n 0), A == Zero.
Proof. lma. Qed.

Lemma dim0 :forall (A : Matrix 0 0), A == Zero.
Proof. apply dim0_l. Qed.

Lemma I0_Zero : I 0 == Zero.
Proof. apply dim0. Qed.

Lemma trace_plus_dist : forall {n : nat} (A B : Square n), 
    trace (A .+ B) = (trace A + trace B). 
Proof. 
  intros.
  unfold trace, Mplus.
  induction n.
  - simpl. lca.
  - simpl. rewrite IHn. lca.
Qed.

Lemma trace_mult_dist : forall {n : nat} (p : C) (A : Square n), 
    trace (p .* A) = (p * trace A). 
Proof.
  intros.
  unfold trace, scale.
  induction n.
  - simpl. lca.
  - simpl. rewrite IHn. lca.
Qed.

Lemma Mplus_0_l : forall {m n : nat} (A : Matrix m n), Zero .+ A == A.
Proof. lma. Qed.

Lemma Mplus_0_r : forall {m n : nat} (A : Matrix m n), A .+ Zero == A.
Proof. lma. Qed.
    
Lemma Mmult_0_l : forall {m n o : nat} (A : Matrix n o), @Zero m n × A == Zero.
Proof.
  intros m n o A i j Hi Hj.
  unfold Mmult, Zero.
  rewrite Csum_0_bounded. easy.
  intros. lca.
Qed.    

Lemma Mmult_0_r : forall {m n o : nat} (A : Matrix m n), A × @Zero n o == Zero.
Proof.
  intros m n o A i j Hi Hj.
  unfold Mmult, Zero.
  rewrite Csum_0_bounded. easy.
  intros. lca.
Qed.

Lemma Mmult_1_l: forall {m n : nat} (A : Matrix m n), 
  I m × A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  eapply Csum_unique. apply Hi.
  unfold I. rewrite Nat.eqb_refl. lca.
  intros x Hx.
  unfold I.
  apply Nat.eqb_neq in Hx. rewrite Hx.
  lca.
Qed.

Lemma Mmult_1_r: forall {m n : nat} (A : Matrix m n), 
  A × I n == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  eapply Csum_unique. apply Hj.
  unfold I. rewrite Nat.eqb_refl. lca.
  intros x Hx.
  unfold I.
  apply Nat.eqb_neq in Hx. rewrite Nat.eqb_sym. rewrite Hx.
  lca.
Qed.

Lemma kron_0_l : forall {m n o p : nat} (A : Matrix o p), 
  @Zero m n ⊗ A == Zero.
Proof. lma. Qed.

Lemma kron_0_r : forall {m n o p : nat} (A : Matrix m n), 
   A ⊗ @Zero o p == Zero.
Proof. lma. Qed.

Lemma kron_1_r : forall {m n : nat} (A : Matrix m n), A ⊗ I 1 == A.
Proof. 
  intros m n A i j Hi Hj.
  unfold I, kron.
  rewrite 2 Nat.div_1_r.
  rewrite 2 Nat.mod_1_r.
  simpl; lca.
Qed.

(* This side is more limited *)
Lemma kron_1_l : forall {m n : nat} (A : Matrix m n), I 1 ⊗ A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold I, kron.
  rewrite 2 Nat.mod_small by lia.
  rewrite 2 Nat.div_small by lia.
  simpl; lca.
Qed.

Theorem transpose_involutive : forall {m n : nat} (A : Matrix m n), (A⊤)⊤ == A.
Proof. reflexivity. Qed.

Theorem adjoint_involutive : forall {m n : nat} (A : Matrix m n), A†† == A.
Proof. lma. Qed.  

Lemma id_transpose_eq : forall {n : nat}, (I n)⊤ == (I n).
Proof. 
  by_cell. 
  unfold transpose, I.
  rewrite Nat.eqb_sym.
  reflexivity.
Qed.

Lemma zero_transpose_eq : forall {m n : nat}, (@Zero m n)⊤ == @Zero m n.
Proof. reflexivity. Qed.

Lemma id_adjoint_eq : forall {n : nat}, (I n)† == (I n).
Proof.
  by_cell.
  unfold adjoint, I.
  rewrite Nat.eqb_sym.
  destruct (i =? j); lca.
Qed.

Lemma zero_adjoint_eq : forall {m n : nat}, (@Zero m n)† == @Zero n m.
Proof. 
  unfold adjoint, Zero. 
  rewrite Cconj_0. 
  reflexivity. 
Qed.

Theorem Mplus_comm : forall {m n : nat} (A B : Matrix m n), A .+ B == B .+ A.
Proof. lma. Qed.

Theorem Mplus_assoc : forall {m n : nat} (A B C : Matrix m n), A .+ B .+ C == A .+ (B .+ C).
Proof. lma. Qed.

Theorem Mmult_assoc : forall {m n o p : nat} (A : Matrix m n) (B : Matrix n o) 
  (C: Matrix o p), A × B × C == A × (B × C).
Proof.
  intros. intros i j _ _.
  unfold Mmult.
  induction n.
  + simpl.
    clear B.
    induction o. reflexivity.
    simpl. rewrite IHo. lca.
  + simpl. 
    rewrite <- IHn.
    simpl.
    rewrite Csum_mult_l.
    rewrite <- Csum_plus.
    apply Csum_eq.
    apply functional_extensionality. intros z.
    rewrite Cmult_plus_distr_r.
    rewrite Cmult_assoc.
    reflexivity.
Qed.

Lemma Mmult_plus_dist_l : forall {m n o : nat} (A : Matrix m n) (B C : Matrix n o), 
                           A × (B .+ C) == A × B .+ A × C.
Proof. 
  intros. intros i j _ _.
  unfold Mplus, Mmult.
  rewrite <- Csum_plus.
  apply Csum_eq_bounded; intros.
  rewrite Cmult_plus_distr_l. 
  reflexivity.
Qed.

Lemma Mmult_plus_dist_r : forall {m n o : nat} (A B : Matrix m n) (C : Matrix n o), 
                           (A .+ B) × C == A × C .+ B × C.
Proof. 
  intros. intros i j _ _.
  unfold Mplus, Mmult.
  rewrite <- Csum_plus.
  apply Csum_eq_bounded; intros.
  rewrite Cmult_plus_distr_r. 
  reflexivity.
Qed.

Lemma kron_plus_distr_l : forall {m n o p : nat} (A : Matrix m n) (B C : Matrix o p), 
                           A ⊗ (B .+ C) == A ⊗ B .+ A ⊗ C.
Proof. 
  intros m n o p A B C i j _ _.
  unfold Mplus, kron.
  rewrite Cmult_plus_distr_l.
  reflexivity.
Qed.

Lemma kron_plus_distr_r : forall {m n o p : nat} (A B : Matrix m n) (C : Matrix o p), 
                           (A .+ B) ⊗ C == A ⊗ C .+ B ⊗ C.
Proof. 
  intros m n o p A B C i j _ _.
  unfold Mplus, kron.
  rewrite Cmult_plus_distr_r.
  reflexivity.
Qed.

Lemma Mscale_0_l : forall {m n : nat} (A : Matrix m n), 0 .* A == Zero.
Proof. by_cell. lca. Qed.

Lemma Mscale_0_r : forall {m n : nat} (c : C), c .* Zero == @Zero m n.
Proof. by_cell. lca. Qed.

Lemma Mscale_1_l : forall {m n : nat} (A : Matrix m n), 1 .* A == A.
Proof. by_cell. lca. Qed.

Lemma Mscale_1_r : forall {n : nat} (c : C),
    c .* I n == fun x y => if (x =? y) then c else C0.
Proof.
  intros n c i j _ _.
  unfold I, scale; simpl. 
  destruct (i =? j); lca.
Qed.

Lemma Mscale_assoc : forall {m n : nat} (x y : C) (A : Matrix m n),
  x .* (y .* A) == (x * y) .* A.
Proof. lma. Qed.

Lemma Mscale_plus_dist_l : forall {m n : nat} (x y : C) (A : Matrix m n),
  (x + y) .* A == x .* A .+ y .* A.
Proof. lma. Qed.

Lemma Mscale_plus_dist_r : forall {m n : nat} (x : C) (A B : Matrix m n),
  x .* (A .+ B) == x .* A .+ x .* B.
Proof. lma. Qed.

Lemma Mscale_mult_dist_l : forall {m n o : nat} (x : C) (A : Matrix m n) (B : Matrix n o), 
    ((x .* A) × B) == x .* (A × B).
Proof. 
  intros. intros i j _ _.
  unfold scale, Mmult.
  rewrite Csum_mult_l.
  apply Csum_eq_bounded; intros.
  lca.
Qed.

Lemma Mscale_mult_dist_r : forall {m n o : nat} (x : C) (A : Matrix m n) (B : Matrix n o),
    (A × (x .* B)) == x .* (A × B).
Proof.
  intros. intros i j _ _.
  unfold scale, Mmult.
  rewrite Csum_mult_l.
  apply Csum_eq_bounded; intros.
  lca.
Qed.

Lemma Mscale_kron_dist_l : forall {m n o p : nat} (x : C) (A : Matrix m n) (B : Matrix o p), 
    ((x .* A) ⊗ B) == x .* (A ⊗ B).
Proof. lma. Qed.

Lemma Mscale_kron_dist_r : forall {m n o p : nat} (x : C) (A : Matrix m n) (B : Matrix o p), 
    (A ⊗ (x .* B)) == x .* (A ⊗ B).
Proof. lma. Qed.

Lemma Mscale_trans : forall {m n : nat} (x : C) (A : Matrix m n),
    (x .* A)⊤ == x .* A⊤.
Proof. reflexivity. Qed.

Lemma Mscale_adj : forall {m n : nat} (x : C) (A : Matrix m n),
    (x .* A)† == x^* .* A†.
Proof. lma. Qed.

(* Inverses of square matrices *)

Definition Minv {n : nat} (A B : Square n) : Prop := A × B == I n /\ B × A == I n.

Lemma Minv_unique : forall {n : nat} (A B C : Square n), 
                      Minv A B -> Minv A C -> B == C.
Proof.
  intros n A B C [MAB MBA] [MAC MCA].
  rewrite <- (Mmult_1_r B).
  rewrite <- MAC.  
  rewrite <- (Mmult_1_l C) at 2.
  rewrite <- MBA.  
  rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma Minv_symm : forall {n : nat} (A B : Square n), Minv A B -> Minv B A.
Proof. unfold Minv; intuition. Qed.

(* The left inverse of a square matrix is also its right inverse *)
Axiom Minv_flip : forall {n : nat} (A B : Square n), A × B == I n -> B × A == I n.
  
Lemma Minv_left : forall {n : nat} (A B : Square n), A × B == I n -> Minv A B.
Proof.
  intros n A B H. 
  unfold Minv. split; trivial.
  apply Minv_flip.
  assumption.
Qed.

Lemma Minv_right : forall {n : nat} (A B : Square n), B × A == I n -> Minv A B.
Proof.
  intros n A B H. 
  unfold Minv. split; trivial.
  apply Minv_flip.
  assumption.
Qed.

Local Open Scope nat_scope.

Lemma div_mod : forall (x y z : nat), (x / y) mod z = (x mod (y * z)) / y.
Admitted.

Lemma mod_product : forall x y z, y <> 0 -> z <> 0 -> x mod (y * z) mod z = x mod z.
Proof.
  intros x y z H H0.
  repeat rewrite Nat.mod_eq; trivial.
  2: apply Nat.neq_mul_0; easy.
  rewrite <- Nat.sub_add_distr.
  apply f_equal2; trivial.
  remember (y * z) as yz.
Admitted.

Lemma kron_assoc : forall {m n p q r s : nat}
  (A : Matrix m n) (B : Matrix p q) (C : Matrix r s),
  (A ⊗ B ⊗ C) == A ⊗ (B ⊗ C).                                
Proof.
  intros. intros i j Hi Hj.
  remember (A ⊗ B ⊗ C) as LHS.
  unfold kron.  
  rewrite (mult_comm p r) at 1 2.
  rewrite (mult_comm q s) at 1 2.
  assert (m * p * r <> 0) by lia.
  assert (n * q * s <> 0) by lia.
  apply Nat.neq_mul_0 in H as [Hmp Hr].
  apply Nat.neq_mul_0 in Hmp as [Hm Hp].
  apply Nat.neq_mul_0 in H0 as [Hnq Hs].
  apply Nat.neq_mul_0 in Hnq as [Hn Hq].
  rewrite <- 2 Nat.div_div by assumption.
  rewrite <- 2 div_mod.
  rewrite 2 mod_product by assumption.
  rewrite Cmult_assoc.
  subst.
  reflexivity.
Qed.  

Local Close Scope nat_scope.
  
Lemma kron_mixed_product : forall {m n o p q r : nat} (A : Matrix m n) (B : Matrix p q ) 
  (C : Matrix n o) (D : Matrix q r), (A ⊗ B) × (C ⊗ D) == (A × C) ⊗ (B × D).
Proof.
  intros m n o p q r A B C D i j _ _.
  unfold kron, Mmult.
  destruct q.
  + simpl.
    rewrite mult_0_r.
    simpl.
    rewrite Cmult_0_r.
    reflexivity. 
  + rewrite Csum_product by lia.
    apply Csum_eq_bounded. intros.
    lca.
Qed.

(* Arguments kron_mixed_product [m n o p q r]. *)

(*
(* A more explicit version, for when typechecking fails *)
Lemma kron_mixed_product' : forall (m n n' o p q q' r mp nq or: nat)
    (A : Matrix m n) (B : Matrix p q) (C : Matrix n' o) (D : Matrix q' r),
    n = n' -> q = q' ->    
    mp = m * p -> nq = n * q -> or = o * r ->
  (@Mmult mp nq or (@kron m n p q A B) (@kron n' o q' r C D)) =
  (@kron m o p r (@Mmult m n o A C) (@Mmult p q r B D)).
Proof. intros. subst. apply kron_mixed_product. Qed.
*)

Lemma Mplus_tranpose : forall {m n : nat} (A : Matrix m n) (B : Matrix m n),
  (A .+ B)⊤ == A⊤ .+ B⊤.
Proof. reflexivity. Qed.

Lemma Mmult_tranpose : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o),
      (A × B)⊤ == B⊤ × A⊤.
Proof.
  intros m n o A B i j _ _.
  unfold Mmult, transpose.
  apply Csum_eq_bounded. intros.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma kron_transpose : forall {m n o p : nat} (A : Matrix m n) (B : Matrix o p ),
  (A ⊗ B)⊤ == A⊤ ⊗ B⊤.
Proof. reflexivity. Qed.

Lemma Mplus_adjoint : forall {m n : nat} (A : Matrix m n) (B : Matrix m n),
  (A .+ B)† == A† .+ B†.
Proof. lma. Qed.

Lemma Mmult_adjoint : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o),
      (A × B)† == B† × A†.
Proof. 
  intros m n o A B i j _ _.
  unfold Mmult, adjoint.
  rewrite Csum_conj_distr.
  apply Csum_eq_bounded. intros.
  rewrite Cconj_mult_distr.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma kron_adjoint : forall {m n o p : nat} (A : Matrix m n) (B : Matrix o p),
  (A ⊗ B)† == A† ⊗ B†.
Proof. lma. Qed.

Lemma id_kron : forall {m n : nat},  I m ⊗ I n == I (m * n).
Proof. 
  intros. intros i j Hi Hj.
  unfold I, kron.
  bdestruct (i =? j).
  - subst.
    rewrite <- 2 beq_nat_refl. lca.
  - bdestruct (i / n =? j / n); bdestruct (i mod n =? j mod n); 
      try lca; try lia.
    contradict H.
    assert (n * m <> 0)%nat as Hnm by lia.
    apply Nat.neq_mul_0 in Hnm as [Hn _].
    rewrite (Nat.div_mod i n) by assumption. 
    rewrite (Nat.div_mod j n) by assumption. 
    rewrite H0, H1.
    reflexivity.
Qed.

Lemma outer_product_eq : forall m (φ ψ : Matrix m 1),
 φ == ψ -> outer_product φ φ == outer_product ψ ψ.
Proof. 
  intros m φ ψ H.
  unfold outer_product.
  rewrite H.
  reflexivity.
Qed.

Lemma outer_product_kron : forall m n (φ : Matrix m 1) (ψ : Matrix n 1), 
    outer_product φ φ ⊗ outer_product ψ ψ == outer_product (φ ⊗ ψ) (φ ⊗ ψ).
Proof. lma. Qed.

Hint Rewrite @kron_1_l @kron_1_r @Mmult_1_l @Mmult_1_r @id_kron @id_adjoint_eq
     @Mmult_adjoint @Mplus_adjoint @kron_adjoint @kron_mixed_product
     @id_adjoint_eq @adjoint_involutive : M_db.

(* *)


(**************)
(* Automation *)
(**************)

Ltac unify_matrices := 
  match goal with
  | |- I ?n = I ?n' =>
    try replace n with n' by unify_pows_two;
    reflexivity
  | |- @Mmult ?m ?n ?o ?A ?B = @Mmult ?m' ?n' ?o' ?A ?B => 
    try replace m with m' by unify_pows_two;
    try replace n with n' by unify_pows_two;
    try replace o with o' by unify_pows_two;
    reflexivity
  | |- @kron ?m ?n ?o ?p ?A ?B = @kron ?m' ?n' ?o' ?p' ?A ?B => 
    try replace m with m' by unify_pows_two;
    try replace n with n' by unify_pows_two;
    try replace o with o' by unify_pows_two;
    try replace p with p' by unify_pows_two;
    reflexivity
  | |- @adjoint ?m ?n ?A ?B = @adjoint ?m' ?n' ?A ?B => 
    try replace m with m' by unify_pows_two;
    try replace n with n' by unify_pows_two;
    reflexivity                               
  end.

(* restore_dims: Gives default dimensions to matrix expressions 
   (for concrete dimensions) *)
Ltac restore_dims :=
  repeat match goal with
  | [ |- context[@Mmult ?m ?n ?o ?A ?B]] => progress match type of A with 
                                          | Matrix ?m' ?n' =>
                                            match type of B with 
                                            | Matrix ?n'' ?o' =>
                                              replace (@Mmult m n o A B) with
                                                  (@Mmult m' n' o' A B) by reflexivity 
                                            end
                                          end
  | [ |- context[@kron ?m ?n ?o ?p ?A ?B]] => progress match type of A with 
                                            | Matrix ?m' ?n' =>
                                              match type of B with 
                                              | Matrix ?o' ?p' =>
                                                replace (@kron m n o p A B) with
                                                    (@kron m' n' o' p' A B) by reflexivity 
                                              end
                                            end
  | [ |- context[@adjoint ?m ?n ?A]]       => progress match type of A with
                                            | Matrix ?m' ?n' =>
                                              replace (@adjoint m n A) with (@adjoint m' n' A) by reflexivity
                                            end
         end.


Ltac restore_dims_strong :=
  repeat match goal with
  | [ |- context[@Mmult ?m ?n ?o ?A ?B]] => progress match type of A with 
                                          | Matrix ?m' ?n' =>
                                            match type of B with 
                                            | Matrix ?n'' ?o' =>
                                              replace (@Mmult m n o A B) with
                                                  (@Mmult m' n' o' A B) by unify_matrices 
                                            end
                                          end
  | [ |- context[@kron ?m ?n ?o ?p ?A ?B]] => progress match type of A with 
                                            | Matrix ?m' ?n' =>
                                              match type of B with 
                                              | Matrix ?o' ?p' =>
                                                replace (@kron m n o p A B) with
                                                    (@kron m' n' o' p' A B) by unify_matrices 
                                              end
                                            end
  | [ |- context[@adjoint ?m ?n ?A]]       => progress match type of A with
                                            | Matrix ?m' ?n' =>
                                              replace (@adjoint m n A) with (@adjoint m' n' A) by unify_matrices
                                            end
         end.


Ltac Msimpl := autorewrite with M_db.

(* Neither of these should be needed anymore. 
Ltac Msimpl := 
  repeat match goal with 
  | [ |- context[(?A ⊗ ?B)†]]    => let H := fresh "H" in 
                                  specialize (kron_adjoint _ _ _ _ A B) as H;
                                  simpl in H; rewrite H; clear H
  | [ |- context[(control ?U)†]] => let H := fresh "H" in 
                                  specialize (control_sa _ U) as H;
                                  simpl in H; rewrite H; 
                                  [clear H | Msimpl; reflexivity]
  | [|- context[(?A ⊗ ?B) × (?C ⊗ ?D)]] => 
                                  let H := fresh "H" in 
                                  specialize (kron_mixed_product _ _ _ _ _ _ A B C D);
                                  intros H; simpl in H; rewrite H; clear H
  | _                           => autorewrite with M_db
  end.

(* For when it needs a bit more help on kron_mixed_product (slow!) *)
Ltac Msimpl' := 
  repeat match goal with 
  | [ |- context[(?A ⊗ ?B)†]]    => let H := fresh "H" in 
                                  specialize (kron_adjoint _ _ _ _ A B) as H;
                                  simpl in H; rewrite H; clear H
  | [ |- context[(control ?U)†]] => let H := fresh "H" in 
                                  specialize (control_sa _ U) as H;
                                  simpl in H; rewrite H; 
                                  [clear H | Msimpl; reflexivity]
  | [|- context[(?A ⊗ ?B) × (?C ⊗ ?D)]] => setoid_rewrite kron_mixed_product';
                                         try lia; try unify_pows_two
  | _                           => autorewrite with M_db
  end.
*)




(*********************************************************)
(** Tactics for solving computational matrix equalities **)
(*********************************************************)


(* Construct matrices full of evars *)
Ltac mk_evar t T := match goal with _ => evar (t : T) end.

Ltac evar_list n := 
  match n with 
  | O => constr:(@nil C)
  | S ?n' => let e := fresh "e" in
            let none := mk_evar e C in 
            let ls := evar_list n' in 
            constr:(e :: ls)
            
  end.

Ltac evar_list_2d m n := 
  match m with 
  | O => constr:(@nil (list C))
  | S ?m' => let ls := evar_list n in 
            let ls2d := evar_list_2d m' n in  
            constr:(ls :: ls2d)
  end.

Ltac evar_matrix m n := let ls2d := (evar_list_2d m n) 
                        in constr:(list2D_to_matrix ls2d).   

(* Tactic version of Nat.lt *)
Ltac tac_lt m n := 
  match n with 
  | S ?n' => match m with 
            | O => idtac
            | S ?m' => tac_lt m' n'
            end
  end.

(* Possible TODO: We could have the tactic below use restore_dims instead of 
   simplifying before rewriting. *)
(* Reassociate matrices so that smallest dimensions are multiplied first:
For (m x n) × (n x o) × (o x p):
If m or o is the smallest, associate left
If n or p is the smallest, associate right
(The actual time for left is (m * o * n) + (m * p * o) = mo(n+p) 
                      versus (n * p * o) + (m * p * n) = np(m+o) for right. 
We find our heuristic to be pretty accurate, though.)
*)
Ltac assoc_least := 
  repeat (simpl; match goal with
  | [|- context[@Mmult ?m ?o ?p (@Mmult ?m ?n ?o ?A ?B) ?C]] => tac_lt p o; tac_lt p m; 
       let H := fresh "H" in 
       specialize (Mmult_assoc A B C) as H; simpl in H; rewrite H; clear H
  | [|- context[@Mmult ?m ?o ?p (@Mmult ?m ?n ?o ?A ?B) ?C]] => tac_lt n o; tac_lt n m; 
       let H := fresh "H" in 
       specialize (Mmult_assoc  A B C) as H; simpl in H; rewrite H; clear H
  | [|- context[@Mmult ?m ?n ?p ?A (@Mmult ?n ?o ?p ?B ?C)]] => tac_lt m n; tac_lt m p; 
       let H := fresh "H" in 
       specialize (Mmult_assoc A B C) as H; simpl in H; rewrite <- H; clear H
  | [|- context[@Mmult ?m ?n ?p ?A (@Mmult ?n ?o ?p ?B ?C)]] => tac_lt o n; tac_lt o p; 
       let H := fresh "H" in 
       specialize (Mmult_assoc A B C) as H; simpl in H; rewrite <- H; clear H
  end).

(* Unify A × B with list (list (evars)) *)
(* We convert the matrices back to functional representation for 
   unification. Simply comparing the matrices may be more efficient,
   however. *)

Ltac crunch_matrix := 
                    match goal with 
                      | [|- ?G ] => idtac "Crunching:" G
                      end;
                      repeat match goal with
                             | [ c : C |- _ ] => cbv [c]; clear c (* 'unfold' hangs *)
                             end; 
                      simpl;
                      unfold list2D_to_matrix;    
                      autounfold with M_db;
                      by_cell;
                      simpl;
                      Csimpl; (* basic rewrites only *) 
                      try reflexivity.

Ltac compound M := 
  match M with
  | ?A × ?B  => idtac
  | ?A .+ ?B => idtac 
  | ?A †     => compound A
  end.

(* Reduce inner matrices first *)
Ltac reduce_aux M := 
  match M with 
  | ?A .+ ?B     => compound A; reduce_aux A
  | ?A .+ ?B     => compound B; reduce_aux B
  | ?A × ?B      => compound A; reduce_aux A
  | ?A × ?B      => compound B; reduce_aux B
  | @Mmult ?m ?n ?o ?A ?B      => let M' := evar_matrix m o in
                                 replace M with M';
                                 [| crunch_matrix ] 
  | @Mplus ?m ?n ?A ?B         => let M' := evar_matrix m n in
                                 replace M with M';
                                 [| crunch_matrix ] 
  end.

Ltac reduce_matrix := match goal with 
                       | [ |- ?M = _] => reduce_aux M
                       | [ |- _ = ?M] => reduce_aux M
                       end;
                       repeat match goal with 
                              | [ |- context[?c :: _ ]] => cbv [c]; clear c
                              end.

(* Reduces matrices anywhere they appear *)
Ltac reduce_matrices := assoc_least;
                        match goal with 
                        | [ |- context[?M]] => reduce_aux M
                        end;
                        repeat match goal with 
                               | [ |- context[?c :: _ ]] => cbv [c]; clear c
                               end.


Ltac solve_matrix := assoc_least;
                     repeat reduce_matrix; try crunch_matrix;
                     (* handle out-of-bounds *)
                     unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; try lca.
       
(* Tactics to show implicit arguments *)
Definition kron' := @kron.      
Lemma kron_shadow : @kron = kron'. Proof. reflexivity. Qed.

Definition Mmult' := @Mmult.
Lemma Mmult_shadow : @Mmult = Mmult'. Proof. reflexivity. Qed.

Ltac show_dimensions := try rewrite kron_shadow in *; 
                        try rewrite Mmult_shadow in *.
Ltac hide_dimensions := try rewrite <- kron_shadow in *; 
                        try rewrite <- Mmult_shadow in *.
