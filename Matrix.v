Require Import Program. 
Require Import Reals.
Require Import Coquelicot.Complex.
Require Import Psatz.
Require Import Omega.
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

Lemma c_proj_eq : forall (c1 c2 : C), fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.  
Proof. intros c1 c2 H1 H2. destruct c1, c2. simpl in *. subst. reflexivity. Qed.

Ltac clra := eapply c_proj_eq; simpl; lra.

(** Matrix Definitions **)

Definition Matrix (m n : nat) := nat -> nat -> C. 

Definition WF_Matrix {m n: nat} (A : Matrix m n) : Prop := 
  forall x y, x >= m \/ y >= n -> A x y = C0. 

(* I won't be using this much, but it can ensure the matrix bounds *)
Definition get {m n} (A : Matrix m n) (a : nat | a < m) (b : nat | b < n) := 
  A (`a) (`b).

Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop := 
  forall (x : nat | x < m) (y : nat | y < n), (A (`x) (`y)) = (B (`x) (`y)).

Lemma mat_equiv_eq : forall {m n : nat} (A B : Matrix m n),
  WF_Matrix A -> 
  WF_Matrix B -> 
  mat_equiv A B ->
  A = B.
Proof.
  intros m n A B WFA WFB Eq.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold mat_equiv in Eq.
  destruct (x <? m) eqn:Hx.
  destruct (y <? n) eqn:Hy.
  + apply Nat.ltb_lt in Hx.
    apply Nat.ltb_lt in Hy.    
    specialize (Eq (exist _ x Hx) (exist _ y Hy)).
    apply Eq.
  + apply Nat.ltb_nlt in Hy.    
    rewrite WFA, WFB; trivial; right; try omega.
  + apply Nat.ltb_nlt in Hx.    
    rewrite WFA, WFB; trivial; left; try omega.
Qed.    
    
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
  | _ => C0
  end.

Definition M23' : Matrix 2 3 := 
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

(** Operands and Operations **)

Definition Zero (m n : nat) : Matrix m n := fun x y => 0%R.

Definition Id (n : nat) : Matrix n n := 
  fun x y => if (x =? y) && (x <? n) then C1 else C0.
(*if (x =? y) then 1%R else 0%R. *)

(* sum to n exclusive *)
Fixpoint Rsum_to_n (f : nat -> C) (n : nat) : C := 
  match n with
  | 0 => C0
  | S n' => (Rsum_to_n f n' +  f n')%C
  end.

Definition trace {n : nat} (A : Matrix n n) := 
  Rsum_to_n (fun x => A x x) n.

Definition scale {m n : nat} (r : C) (A : Matrix m n) : Matrix m n := 
  fun x y => (r * A x y)%C.

Definition dot {n : nat} (A : Matrix 1 n) (B : Matrix n 1) : C :=
  Rsum_to_n (fun x => A O x * B x O)%C n.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun x y => (A x y + B x y)%C.

Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o := 
  fun x z => Rsum_to_n (fun y => A x y * B y z )%C n.

(* Only well-defined when o and p are non-zero *)
Definition kron {m n o p : nat} (A : Matrix m n) (B : Matrix o p) : 
  Matrix (m*o) (n*p) :=
  fun x y => Cmult (A (x / o) (y / p)) (B (x mod o) (y mod p)).

Definition transpose {m n} (A : Matrix m n) : Matrix n m := fun x y => A y x. 

Definition conj_transpose {m n} (A : Matrix m n) : Matrix n m := 
  fun x y => Cconj (A y x). 

Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Infix ".+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix ".*" := scale (at level 50, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Infix "≡" := mat_equiv (at level 100) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope. 
Notation "A †" := (conj_transpose A) (at level 0) : matrix_scope. 
Notation "Σ^ n f" := (Rsum_to_n f n) (at level 90) : matrix_scope.
Open Scope matrix_scope.

(** Well-Formedness **)

Lemma WF_Zero : forall {m n : nat}, WF_Matrix (Zero m n).
Proof. intros m n. unfold WF_Matrix. reflexivity. Qed.

Lemma WF_Id : forall {n : nat}, WF_Matrix (Id n). 
Proof. 
  unfold WF_Matrix, Id. intros n x y H.
  destruct H. 
  + replace (x <? n) with false by (symmetry; rewrite Nat.ltb_nlt; omega).
    destruct (x =? y); simpl; reflexivity.
  + destruct (x =? y) eqn:Eq.
    apply Nat.eqb_eq in Eq; subst.
    replace (y <? n) with false by (symmetry; rewrite Nat.ltb_nlt; omega).
    reflexivity.
    reflexivity.
Qed.

Lemma WF_scale : forall {m n : nat} (r : C) (A : Matrix m n), 
  WF_Matrix A -> WF_Matrix (scale r A).
Proof.
  unfold WF_Matrix, scale.
  intros m n r A H x y H0.
  rewrite H; trivial.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

Lemma WF_plus : forall {m n} (A B : Matrix m n), 
  WF_Matrix A -> WF_Matrix B -> WF_Matrix (A .+ B).
Proof.
  unfold WF_Matrix, Mplus.
  intros m n A B H H0 x y H1.
  rewrite H, H0; trivial.
  rewrite Cplus_0_l.
  reflexivity.
Qed.

Lemma WF_mult : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o), 
  WF_Matrix A -> WF_Matrix B -> WF_Matrix (A × B).
Proof.
  unfold WF_Matrix, Mmult.
  intros m n o A B H H0 x y H1.
  destruct H1.
  + assert (forall y, A x y = 0%R) as H'. intros. apply H. auto. clear H H0 H1.
    induction n.
    simpl. reflexivity.
    simpl.
    rewrite IHn, H'; auto.
    rewrite Cplus_0_l, Cmult_0_l; reflexivity.
  + assert (forall x, B x y = 0%R) as H'. intros. apply H0. auto. clear H H0 H1.
    induction n.
    simpl. reflexivity.
    simpl.
    rewrite IHn, H'; auto.
    rewrite Cplus_0_l, Cmult_0_r; reflexivity.
Qed.

(* Should the non-zero assumptions be here? *)
Lemma WF_kron : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o), 
                  n <> 0 -> o <> 0 ->
                  WF_Matrix A -> WF_Matrix B -> WF_Matrix (A ⊗ B).
Proof.
  unfold WF_Matrix, kron.
  intros m n o A B Nn No H H0 x y H1.
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

Lemma WF_transpose : forall {m n : nat} (A : Matrix m n), WF_Matrix A -> WF_Matrix A⊤. 
Proof. unfold WF_Matrix, transpose. intros m n A H x y H0. apply H. 
       destruct H0; auto. Qed.

Lemma WF_conj_transpose : forall {m n : nat} (A : Matrix m n), WF_Matrix A -> WF_Matrix A†. 
Proof. unfold WF_Matrix, conj_transpose, Cconj. intros m n A H x y H0. rewrite H. 
       clra. omega. Qed.

(** Basic Matrix Lemmas **)

Lemma Mplus_0_l : forall {m n : nat} (A : Matrix m n), Zero m n .+ A = A.
Proof.
  intros m n A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  clra.
Qed.

Lemma Mplus_0_r : forall {m n : nat} (A : Matrix m n), A .+ Zero m n = A.
Proof.
  intros m n A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  clra.
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
    rewrite Cmult_0_l.
    rewrite Cplus_0_r.
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
    rewrite Cmult_0_r.
    rewrite Cplus_0_r.
    apply IHn.
Qed.    

(* using <= because our form Rsum_to_n is exclusive. *)
Lemma Mmult_1_l_gen: forall {m n : nat} (A : Matrix m n) (x z k : nat), 
  k <= m ->
  (k <= x -> Rsum_to_n (fun y : nat => (Id m x y * A y z)%C) k = C0) /\
  (k > x -> Rsum_to_n (fun y : nat => (Id m x y * A y z)%C) k = A x z).
Proof.  
  intros m n A x z k B.
  induction k.
  simpl. split. reflexivity. omega.
  destruct IHk as [IHl IHr]. omega.  
  split.
  + intros leSkx.
    simpl.
    unfold Id.
    replace (x =? k) with false by (symmetry; apply Nat.eqb_neq; omega).
    rewrite Cmult_0_l, Cplus_0_r.
    apply IHl.
    omega.
  + intros gtSkx.
    simpl. 
    unfold Id in *.
    destruct (x =? k) eqn:Eqxk.
    - apply Nat.eqb_eq in Eqxk; subst.
      replace (k <? m) with true in * by (symmetry; apply Nat.ltb_lt; omega).
      rewrite Cmult_1_l.
      rewrite IHl; try omega.
      rewrite Cplus_0_l.     
      reflexivity.
    - apply Nat.eqb_neq in Eqxk; subst.
      rewrite Cmult_0_l.
      rewrite Cplus_0_r.
      apply IHr.
      omega.
Qed.

Lemma Mmult_1_l_mat_eq : forall {m n : nat} (A : Matrix m n), Id m × A ≡ A.
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

Lemma Mmult_1_l: forall {m n : nat} (A : Matrix m n), 
  WF_Matrix A -> Id m × A = A.
Proof.
  intros m n A H.
  apply mat_equiv_eq; trivial.
  apply WF_mult; trivial.
  apply WF_Id.
  apply Mmult_1_l_mat_eq.
Qed.

Lemma Mmult_1_r_gen: forall {m n : nat} (A : Matrix m n) (x z k : nat), 
  k <= n ->
  (k <= z -> Rsum_to_n (fun y : nat => (A x y * Id n y z)%C) k = C0) /\
  (k > z -> Rsum_to_n (fun y : nat => (A x y * Id n y z)%C) k = A x z).
Proof.  
  intros m n A x z k B.
  induction k.
  simpl. split. reflexivity. omega.
  destruct IHk as [IHl IHr].
  omega.
  split.
  + intros leSkz.
    simpl.
    unfold Id.
    replace (k =? z) with false by (symmetry; apply Nat.eqb_neq; omega).
    rewrite Cmult_0_r, Cplus_0_r.
    apply IHl.
    omega.
  + intros gtSkz.
    simpl. 
    unfold Id in *.
    destruct (k =? z) eqn:Eqxk.
    - apply Nat.eqb_eq in Eqxk; subst.
      replace (z <? n) with true in * by (symmetry; apply Nat.ltb_lt; omega).
      rewrite Cmult_1_r.
      rewrite IHl; try omega.
      rewrite Cplus_0_l.     
      reflexivity.
    - apply Nat.eqb_neq in Eqxk; subst.
      rewrite Cmult_0_r.
      rewrite Cplus_0_r.
      apply IHr.
      omega.
Qed.

Lemma Mmult_1_r_mat_eq : forall {m n : nat} (A : Matrix m n), A × Id n ≡ A.
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

Lemma Mmult_1_r: forall {m n : nat} (A : Matrix m n), 
  WF_Matrix A -> A × Id n = A.
Proof.
  intros m n A H.
  apply mat_equiv_eq; trivial.
  apply WF_mult; trivial.
  apply WF_Id.
  apply Mmult_1_r_mat_eq.
Qed.

Lemma kron_1_r : forall {m n : nat} (A : Matrix m n), A ⊗ Id 1 = A.
Proof.
  intros m n A.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold Id, kron.
  rewrite 2 Nat.div_1_r.
  rewrite 2 Nat.mod_1_r.
  simpl.
  clra.
Qed.

(* This side is much more limited/annoying *)
Lemma kron_1_l : forall {m n : nat} (A : Matrix m n), 
  m > 0 -> n > 0 -> WF_Matrix A -> Id 1 ⊗ A = A.
Proof.
  intros m n A H1 H2 WF.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold Id, kron.
  destruct (x / m <? 1) eqn:Eq1. 
  destruct (x / m =? y / n) eqn:Eq2. 
  all: simpl.
  + apply Nat.ltb_lt in Eq1.
    rewrite Nat.eqb_eq in Eq2.
    assert (x / m = 0) by omega. clear Eq1. rename H into Eq1.
    rewrite Eq1 in Eq2.     
    symmetry in Eq2.
    rewrite Nat.div_small_iff in Eq2 by omega.
    rewrite Nat.div_small_iff in Eq1 by omega.
    rewrite 2 Nat.mod_small; trivial.
    clra.
  + apply Nat.ltb_lt in Eq1.
    rewrite Nat.eqb_neq in Eq2.
    assert (x / m = 0) by omega. clear Eq1.
    rewrite H in Eq2. clear H.
    assert (y / n <> 0) by omega. clear Eq2.
    rewrite Nat.div_small_iff in H by omega.
    rewrite WF with (x := x) (y := y) by omega. 
    clra.
  + rewrite andb_false_r.
    apply Nat.ltb_nlt in Eq1.
    assert (x / m <> 0) by omega. clear Eq1.
    rewrite Nat.div_small_iff in H by omega.
    rewrite WF with (x := x) (y := y) by omega.
    clra.
Qed.

Theorem transpose_involutive : forall {m n : nat} (A : Matrix m n), (A⊤)⊤ = A.
Proof. reflexivity. Qed. (* Wow *)

Lemma conj_involutive : forall (c : C), Cconj (Cconj c) = c.
Proof. intros c. clra. Qed.

Theorem conj_transpose_involutive : forall {m n : nat} (A : Matrix m n), (A†)† = A.
Proof. 
  intros m n A. unfold conj_transpose. 
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.       
  apply conj_involutive.
Qed.  

Lemma id_transpose_eq : forall n, (Id n)⊤ = (Id n).
Proof.
  intros n.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold Id, transpose; simpl.
  destruct (y =? x) eqn:Eq.
  + apply Nat.eqb_eq in Eq; subst.
    rewrite Nat.eqb_refl.
    reflexivity.
  + rewrite Nat.eqb_sym. rewrite Eq.
    reflexivity.    
Qed.

Lemma id_conj_transpose_eq : forall n, (Id n)† = (Id n).
Proof.
  intros n.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  unfold Id, conj_transpose; simpl.
  destruct (y =? x) eqn:Eq.
  + apply Nat.eqb_eq in Eq; subst.
    rewrite Nat.eqb_refl.
    destruct (x <? n); simpl; clra.
  + rewrite Nat.eqb_sym. rewrite Eq.
    simpl. 
    clra.
Qed.

Theorem Mplus_comm : forall {m n : nat} (A B : Matrix m n), A .+ B = B .+ A.
Proof.
  unfold Mplus. 
  intros m n A B.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  apply Cplus_comm.
Qed.

Theorem Mplus_assoc : forall {m n : nat} (A B C : Matrix m n), A .+ B .+ C = A .+ (B .+ C).
Proof.
  unfold Mplus. 
  intros m n A B C.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  rewrite Cplus_assoc.
  reflexivity.
Qed.

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
    simpl. rewrite IHo. clra.
  + simpl. 
    rewrite <- IHn.
    simpl.
Admitted.

(* Inverses *)

Definition Minv {n} (A B : Matrix n n) := A × B = Id n /\ B × A = Id n.

Lemma Minv_unique : forall {n} (A B C : Matrix n n), 
                      WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
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
  
Lemma Minv_left : forall {n} (A B : Matrix n n), A × B = Id n -> Minv A B.
Proof.
  intros n A B H. 
  unfold Minv. split; trivial.
  + apply functional_extensionality; intros x.
    apply functional_extensionality; intros y.
    rewrite <- H.
    unfold Mmult, Id.
Admitted.

(* Not generally true, just like sum_sum wasn't.
   A general sum_n_to_m function might have better properties. 
Theorem sum_product : forall (p q : nat) (f : nat -> R), 
  Rsum_to_n f (p * q) = ((Rsum_to_n f p) * (Rsum_to_n f q))%R.
Proof. 
  intros p q f.
  induction p. simpl. lra.
  simpl.
  *)


(*    
Theorem kron_mixed_product : forall {m n o p q r : nat} (A : Matrix m n) (B : Matrix p q ) 
  (C : Matrix n o) (D : Matrix q r), (A ⊗ B) × (C ⊗ D) = (A × C) ⊗ (B × D).
Proof.
  intros m n o p q r A B C D.
  unfold kron, Mmult.
  apply functional_extensionality; intros x.
  apply functional_extensionality; intros y.
  induction n. simpl. lra.
  simpl.
  
  
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
*)


(* *)