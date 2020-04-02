Require Import Psatz.
Require Import String.
Require Import Program.
Require Export Complex.
Require Import List.


(* TODO: Use matrix equality everywhere, declare equivalence relation *)
(* TODO: Make all nat arguments to matrix lemmas implicit *)

(*******************************************)
(** Matrix Definitions and Infrastructure **)
(*******************************************)

Declare Scope matrix_scope.
Delimit Scope matrix_scope with M.
Open Scope matrix_scope.

Local Open Scope nat_scope.

Definition Matrix (m n : nat) := nat -> nat -> C.

(* Definition Vector (n : nat) := Matrix n 1. *)

Definition WF_Matrix {m n: nat} (A : Matrix m n) : Prop := 
  forall x y, x >= m \/ y >= n -> A x y = C0. 

Notation Vector n := (Matrix n 1).

Notation Square n := (Matrix n n).

(* Showing equality via functional extensionality *)
Ltac prep_matrix_equality :=
  let x := fresh "x" in 
  let y := fresh "y" in 
  apply functional_extensionality; intros x;
  apply functional_extensionality; intros y.

(* Matrix Equivalence *)
Definition get {m n} (A : Matrix m n) (a : nat | a < m) (b : nat | b < n) := 
  A (`a) (`b).

Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop := 
  forall (x : nat | x < m) (y : nat | y < n), get A x y = get B x y.

Lemma mat_equiv_refl : forall m n (A : Matrix m n), mat_equiv A A.
Proof. unfold mat_equiv; reflexivity. Qed.

Lemma mat_equiv_eq : forall {m n : nat} (A B : Matrix m n),
  WF_Matrix A -> 
  WF_Matrix B -> 
  mat_equiv A B ->
  A = B.
Proof.
  intros m n A' B' WFA WFB Eq.
  prep_matrix_equality.
  unfold mat_equiv in Eq.
  bdestruct (x <? m).
  bdestruct (y <? n).
  + specialize (Eq (exist _ x H) (exist _ y H0)). apply Eq.
  + rewrite WFA, WFB; trivial; right; try lia.
  + rewrite WFA, WFB; trivial; left; try lia.
Qed.

(* Printing *)

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

(* 2D List Representation *)
    
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

(* Example *)
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

(*****************************)
(** Operands and Operations **)
(*****************************)

Definition Zero {m n : nat} : Matrix m n := fun x y => 0%R.

Definition I (n : nat) : Square n := 
  (fun x y => if (x =? y) && (x <? n) then C1 else C0).

(* Optional coercion to scalar (should be limited to 1 × 1 matrices):
Definition to_scalar (m n : nat) (A: Matrix m n) : C := A 0 0.

Coercion to_scalar : Matrix >-> C.
 *)


  (*
Definition I (n : nat) : Square n := 
  (fun x y => if (x =? y) && (x <? n) then C1 else C0).
Definition I1 := I (2^0).
Notation "I  n" := (I n) (at level 10).
*)

(* This isn't used, but is interesting *)
Definition I__inf := fun x y => if x =? y then C1 else C0.
Notation "I∞" := I__inf : matrix_scope.

(* sum to n exclusive *)
Fixpoint Csum (f : nat -> C) (n : nat) : C := 
  match n with
  | 0 => C0
  | S n' => (Csum f n' +  f n')%C
  end.

Definition trace {n : nat} (A : Square n) := 
  Csum (fun x => A x x) n.

Definition scale {m n : nat} (r : C) (A : Matrix m n) : Matrix m n := 
  fun x y => (r * A x y)%C.

Definition dot {n : nat} (A : Vector n) (B : Vector n) : C :=
  Csum (fun x => A x 0  * B x 0)%C n.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun x y => (A x y + B x y)%C.

Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o := 
  fun x z => Csum (fun y => A x y * B y z)%C n.

(* Only well-defined when o and p are non-zero *)
Definition kron {m n o p : nat} (A : Matrix m n) (B : Matrix o p) : 
  Matrix (m*o) (n*p) :=
  fun x y => Cmult (A (x / o) (y / p)) (B (x mod o) (y mod p)).

Definition transpose {m n} (A : Matrix m n) : Matrix n m := 
  fun x y => A y x.

Definition adjoint {m n} (A : Matrix m n) : Matrix n m := 
  fun x y => (A y x)^*.

Definition inner_product {n} (u v : Vector n) : C := 
  Mmult (adjoint u) (v) 0 0.

Definition outer_product {n} (u v : Vector n) : Square n := 
  Mmult u (adjoint v).

(* Kronecker of n copies of A *)
Fixpoint kron_n n {m1 m2} (A : Matrix m1 m2) : Matrix (m1^n) (m2^n) :=
  match n with
  | 0    => I 1
  | S n' => kron (kron_n n' A) A
  end.

(* Kronecker product of a list *)
Fixpoint big_kron {m n} (As : list (Matrix m n)) : 
  Matrix (m^(length As)) (n^(length As)) := 
  match As with
  | [] => I 1
  | A :: As' => kron A (big_kron As')
  end.

Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Infix ".+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix ".*" := scale (at level 40, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Infix "≡" := mat_equiv (at level 70) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope. 
Notation "A †" := (adjoint A) (at level 0) : matrix_scope. 
Notation "Σ^ n f" := (Csum f n) (at level 60) : matrix_scope.
Notation "n ⨂ A" := (kron_n n A) (at level 30, no associativity) : matrix_scope.
Notation "⨂ A" := (big_kron A) (at level 60): matrix_scope.
Hint Unfold Zero I trace dot Mplus scale Mmult kron mat_equiv transpose 
            adjoint : U_db.
  
Ltac destruct_m_1 :=
  match goal with
  | [ |- context[match ?x with 
                 | 0   => _
                 | S _ => _
                 end] ] => is_var x; destruct x
  end.
Ltac destruct_m_eq := repeat (destruct_m_1; simpl).

Ltac lma := 
  autounfold with U_db;
  prep_matrix_equality;
  destruct_m_eq; 
  lca.

(******************************)
(** Proofs about finite sums **)
(******************************)

Local Close Scope nat_scope.

Lemma Csum_0 : forall f n, (forall x, f x = C0) -> Csum f n = 0. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, H. 
    lca.
Qed.

Lemma Csum_1 : forall f n, (forall x, f x = C1) -> Csum f n = INR n. 
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

Lemma Csum_unique : forall k (f : nat -> C) n, 
  (exists x, (x < n)%nat /\ f x = k /\ (forall x', x <> x' -> f x' = 0)) ->
  Csum f n = k.
Proof.                    
  intros k f n [x [L [Eq Unique]]].
  induction n; try lia.
  Search Csum.
  rewrite <- Csum_extend_r.
  destruct (Nat.eq_dec x n).
  - subst. 
    rewrite Csum_0_bounded.
    lca.
    intros.
    apply Unique.
    lia.
  - rewrite Unique by easy.
    Csimpl.
    apply IHn.
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



(**********************************)
(** Proofs about Well-Formedness **)
(**********************************)

Local Open Scope nat_scope.

Lemma WF_Zero : forall m n : nat, WF_Matrix (@Zero m n).
Proof. intros m n. unfold WF_Matrix. reflexivity. Qed.

Lemma WF_I : forall n : nat, WF_Matrix (I n). 
Proof. 
  unfold WF_Matrix, I. intros n x y H. simpl.
  destruct H; bdestruct (x =? y); bdestruct (x <? n); trivial; lia.
Qed.

Lemma WF_I1 : WF_Matrix (I 1). Proof. apply WF_I. Qed.

Lemma WF_scale : forall {m n : nat} (r : C) (A : Matrix m n), 
  WF_Matrix A -> WF_Matrix (scale r A).
Proof.
  unfold WF_Matrix, scale.
  intros m n r A H x y H0. simpl.
  rewrite H; trivial.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

Lemma WF_plus : forall {m n} (A B : Matrix m n), 
  WF_Matrix A -> WF_Matrix B -> WF_Matrix (A .+ B).
Proof.
  unfold WF_Matrix, Mplus.
  intros m n A B H H0 x y H1. simpl.
  rewrite H, H0; trivial.
  rewrite Cplus_0_l.
  reflexivity.
Qed.

Lemma WF_mult : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o), 
  WF_Matrix A -> WF_Matrix B -> WF_Matrix (A × B).
Proof.
  unfold WF_Matrix, Mmult.
  intros m n o A B H H0 x y D. simpl.
  apply Csum_0.
  destruct D; intros z.
  + rewrite H; [lca | auto].
  + rewrite H0; [lca | auto].
Qed.

Lemma WF_kron : forall {m n o p q r : nat} (A : Matrix m n) (B : Matrix o p), 
                  q = m * o -> r = n * p -> 
                  WF_Matrix A -> WF_Matrix B -> @WF_Matrix q r (A ⊗ B).
Proof.
  unfold WF_Matrix, kron.
  intros m n o p q r A B Nn No H H0 x y H1. subst.
  bdestruct (o =? 0). rewrite H0; [lca|lia]. 
  bdestruct (p =? 0). rewrite H0; [lca|lia]. 
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


(* More succinct but sometimes doesn't succeed 
Lemma WF_kron : forall {m n o p: nat} (A : Matrix m n) (B : Matrix o p), 
                  WF_Matrix A -> WF_Matrix B -> WF_Matrix (A ⊗ B).
Proof.
  unfold WF_Matrix, kron.
  intros m n o p A B WFA WFB x y H.
  bdestruct (o =? 0). rewrite WFB; [lca|lia]. 
  bdestruct (p =? 0). rewrite WFB; [lca|lia].  
  rewrite WFA.
  rewrite Cmult_0_l; reflexivity.
  destruct H.
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

Lemma WF_transpose : forall {m n : nat} (A : Matrix m n), 
                     WF_Matrix A -> WF_Matrix A⊤. 
Proof. unfold WF_Matrix, transpose. intros m n A H x y H0. apply H. 
       destruct H0; auto. Qed.

Lemma WF_adjoint : forall {m n : nat} (A : Matrix m n), 
      WF_Matrix A -> WF_Matrix A†. 
Proof. unfold WF_Matrix, adjoint, Cconj. intros m n A H x y H0. simpl. 
rewrite H. lca. lia. Qed.

Lemma WF_outer_product : forall {n} (u v : Vector n),
    WF_Matrix u ->
    WF_Matrix v ->
    WF_Matrix (outer_product u v).
Proof. intros. apply WF_mult; [|apply WF_adjoint]; assumption. Qed.

Lemma WF_kron_n : forall n {m1 m2} (A : Matrix m1 m2),
   WF_Matrix A ->  WF_Matrix (kron_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply WF_I.
  - apply WF_kron; try lia; assumption. 
Qed.

Lemma WF_big_kron : forall n m (l : list (Matrix m n)) (A : Matrix m n), 
                        (forall i, WF_Matrix (nth i l A)) ->
                         WF_Matrix (⨂ l). 
Proof.                         
  intros n m l A H.
  induction l.
  - simpl. apply WF_I.
  - simpl. apply WF_kron; trivial. apply (H O).
    apply IHl. intros i. apply (H (S i)).
Qed.

Local Close Scope nat_scope.

(***************************************)
(* Tactics for showing well-formedness *)
(***************************************)

Local Open Scope nat.
Local Open Scope R.
Local Open Scope C.

(*
Ltac show_wf := 
  repeat match goal with
  | [ |- WF_Matrix _ _ (?A × ?B) ]  => apply WF_mult 
  | [ |- WF_Matrix _ _ (?A .+ ?B) ] => apply WF_plus 
  | [ |- WF_Matrix _ _ (?p .* ?B) ] => apply WF_scale
  | [ |- WF_Matrix _ _ (?A ⊗ ?B) ]  => apply WF_kron
  | [ |- WF_Matrix _ _ (?A⊤) ]      => apply WF_transpose 
  | [ |- WF_Matrix _ _ (?A†) ]      => apply WF_adjoint 
  | [ |- WF_Matrix _ _ (I _) ]     => apply WF_I
  end;
  trivial;
  unfold WF_Matrix;
  let x := fresh "x" in
  let y := fresh "y" in
  let H := fresh "H" in
  intros x y [H | H];
    repeat (destruct x; try reflexivity; try lia);
    repeat (destruct y; try reflexivity; try lia).
*)

(* Much less awful *)
Ltac show_wf := 
  unfold WF_Matrix;
  let x := fresh "x" in
  let y := fresh "y" in
  let H := fresh "H" in
  intros x y [H | H];
  apply le_plus_minus in H; rewrite H;
  cbv;
  destruct_m_eq;
  try lca.

(* Create HintDb wf_db. *)
Hint Resolve WF_Zero WF_I WF_I1 WF_mult WF_plus WF_scale WF_transpose 
     WF_adjoint WF_outer_product WF_big_kron WF_kron_n WF_kron : wf_db.
Hint Extern 2 (_ = _) => unify_pows_two : wf_db.


(** Basic Matrix Lemmas **)

Lemma WF0_Zero_l :forall (n : nat) (A : Matrix 0%nat n), WF_Matrix A -> A = Zero.
Proof.
  intros n A WFA.
  prep_matrix_equality.
  rewrite WFA.
  reflexivity.
  lia.
Qed.

Lemma WF0_Zero_r :forall (n : nat) (A : Matrix n 0%nat), WF_Matrix A -> A = Zero.
Proof.
  intros n A WFA.
  prep_matrix_equality.
  rewrite WFA.
  reflexivity.
  lia.
Qed.

Lemma WF0_Zero :forall (A : Matrix 0%nat 0%nat), WF_Matrix A -> A = Zero.
Proof.
  apply WF0_Zero_l.
Qed.

Lemma I0_Zero : I 0 = Zero.
Proof.
  apply WF0_Zero.
  apply WF_I.
Qed.

Lemma trace_plus_dist : forall (n : nat) (A B : Square n), 
    trace (A .+ B) = (trace A + trace B)%C. 
Proof. 
  intros.
  unfold trace, Mplus.
  induction n.
  - simpl. lca.
  - simpl. rewrite IHn. lca.
Qed.

Lemma trace_mult_dist : forall n p (A : Square n), trace (p .* A) = (p * trace A)%C. 
Proof.
  intros.
  unfold trace, scale.
  induction n.
  - simpl. lca.
  - simpl. rewrite IHn. lca.
Qed.

Lemma Mplus_0_l : forall (m n : nat) (A : Matrix m n), Zero .+ A = A.
Proof. intros. lma. Qed.

Lemma Mplus_0_r : forall (m n : nat) (A : Matrix m n), A .+ Zero = A.
Proof. intros. lma. Qed.
    
Lemma Mmult_0_l : forall (m n o : nat) (A : Matrix n o), @Zero m n × A = Zero.
Proof.
  intros m n o A. 
  unfold Mmult, Zero.
  prep_matrix_equality.
  induction n.
  + simpl. reflexivity.
  + simpl in *.
    autorewrite with C_db.
    apply IHn.
Qed.    

Lemma Mmult_0_r : forall (m n o : nat) (A : Matrix m n), A × @Zero n o = Zero.
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

(* using <= because our form Csum is exclusive. *)
Lemma Mmult_1_l_gen: forall (m n : nat) (A : Matrix m n) (x z k : nat), 
  (k <= m)%nat ->
  ((k <= x)%nat -> Csum (fun y : nat => I m x y * A y z) k = 0) /\
  ((k > x)%nat -> Csum (fun y : nat => I m x y * A y z) k = A x z).
Proof.  
  intros m n A x z k B.
  induction k.
  * simpl. split. reflexivity. lia.
  * destruct IHk as [IHl IHr]. lia.  
    split.
    + intros leSkx.
      simpl.
      unfold I.
      bdestruct (x =? k); try lia.
      autorewrite with C_db.
      apply IHl.
      lia.
    + intros gtSkx.
      simpl in *.
      unfold I in *.
      bdestruct (x =? k); bdestruct (x <? m); subst; try lia.
      rewrite IHl by lia; simpl; lca.
      rewrite IHr by lia; simpl; lca.
Qed.

Lemma Mmult_1_l_mat_eq : forall (m n : nat) (A : Matrix m n), I m × A ≡ A.
Proof.
  intros m n A x y.
  destruct x as [x Px], y as [y Py].
  simpl. 
  unfold Mmult.
  edestruct (@Mmult_1_l_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  unfold get.
  apply Hr.
  simpl in *.
  lia.
Qed.  

Lemma Mmult_1_l: forall (m n : nat) (A : Matrix m n), 
  WF_Matrix A -> I m × A = A.
Proof.
  intros m n A H.
  apply mat_equiv_eq; trivial.
  auto with wf_db.
  apply Mmult_1_l_mat_eq.
Qed.

Lemma Mmult_1_r_gen: forall (m n : nat) (A : Matrix m n) (x z k : nat), 
  (k <= n)%nat ->
  ((k <= z)%nat -> Csum (fun y : nat => A x y * (I n) y z) k = 0) /\
  ((k > z)%nat -> Csum (fun y : nat => A x y * (I n) y z) k = A x z).
Proof.  
  intros m n A x z k B.
  induction k.
  simpl. split. reflexivity. lia.
  destruct IHk as [IHl IHr].
  lia.
  split.
  + intros leSkz.
    simpl in *.
    unfold I.
    bdestruct (k =? z); try lia.
    autorewrite with C_db.
    apply IHl; lia.
  + intros gtSkz.
    simpl in *.
    unfold I in *.
    bdestruct (k =? z); subst.
    - bdestruct (z <? n); try lia.
      rewrite IHl by lia; lca.
    - rewrite IHr by lia; simpl; lca.
Qed.

Lemma Mmult_1_r_mat_eq : forall (m n : nat) (A : Matrix m n), A × I n ≡ A.
Proof.
  intros m n A x y.
  destruct x as [x Px], y as [y Py].
  simpl. 
  unfold Mmult.
  edestruct (@Mmult_1_r_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  unfold get; simpl.
  apply Hr.
  lia.
Qed.  

Lemma Mmult_1_r: forall (m n : nat) (A : Matrix m n), 
  WF_Matrix A -> A × I n = A.
Proof.
  intros m n A H.
  apply mat_equiv_eq; trivial.
  auto with wf_db.
  apply Mmult_1_r_mat_eq.
Qed.

(* Cool facts about I∞, not used in the development *) 
Lemma Mmult_inf_l : forall(m n : nat) (A : Matrix m n),
  WF_Matrix A -> I∞ × A = A.
Proof. 
  intros m n A H.
  prep_matrix_equality.
  unfold Mmult.
  edestruct (@Mmult_1_l_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  bdestruct (m <=? x).
  rewrite H by auto.
  apply Csum_0_bounded.
  intros z L. 
  unfold I__inf, I.
  bdestruct (x =? z). lia. lca.  
  unfold I__inf, I in *.
  erewrite Csum_eq.
  apply Hr.
  assumption.
  bdestruct (x <? m); [|lia]. 
  apply functional_extensionality. intros. rewrite andb_true_r. reflexivity.
Qed.

Lemma Mmult_inf_r : forall(m n : nat) (A : Matrix m n),
  WF_Matrix A -> A × I∞ = A.
Proof. 
  intros m n A H.
  prep_matrix_equality.
  unfold Mmult.
  edestruct (@Mmult_1_r_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  bdestruct (n <=? y).
  rewrite H by auto.
  apply Csum_0_bounded.
  intros z L. 
  unfold I__inf, I.
  bdestruct (z =? y). lia. lca.  
  unfold I__inf, I in *.
  erewrite Csum_eq.
  apply Hr.
  assumption.
  apply functional_extensionality. intros z. 
  bdestruct (z =? y); bdestruct (z <? n); simpl; try lca; try lia. 
Qed.

Lemma kron_0_l : forall (m n o p : nat) (A : Matrix o p), 
  @Zero m n ⊗ A = Zero.
Proof.
  intros m n o p A.
  prep_matrix_equality.
  unfold Zero, kron.
  rewrite Cmult_0_l.
  reflexivity.
Qed.

Lemma kron_0_r : forall (m n o p : nat) (A : Matrix m n), 
   A ⊗ @Zero o p = Zero.
Proof.
  intros m n o p A.
  prep_matrix_equality.
  unfold Zero, kron.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

Lemma kron_1_r : forall (m n : nat) (A : Matrix m n), A ⊗ I 1 = A.
Proof.
  intros m n A.
  prep_matrix_equality.
  unfold I, kron.
  rewrite 2 Nat.div_1_r.
  rewrite 2 Nat.mod_1_r.
  simpl.
  autorewrite with C_db.
  reflexivity.
Qed.

(* This side is more limited *)
Lemma kron_1_l : forall (m n : nat) (A : Matrix m n), 
  WF_Matrix A -> I 1 ⊗ A = A.
Proof.
  intros m n A WF.
  prep_matrix_equality.
  unfold kron.
  unfold I, kron.
  bdestruct (m =? 0). rewrite 2 WF by lia. lca. 
  bdestruct (n =? 0). rewrite 2 WF by lia. lca.
  bdestruct (x / m <? 1); rename H1 into Eq1.
  bdestruct (x / m =? y / n); rename H1 into Eq2; simpl.
  + assert (x / m = 0)%nat by lia. clear Eq1. rename H1 into Eq1.
    rewrite Eq1 in Eq2.     
    symmetry in Eq2.
    rewrite Nat.div_small_iff in Eq2 by lia.
    rewrite Nat.div_small_iff in Eq1 by lia.
    rewrite 2 Nat.mod_small; trivial.
    lca.
  + assert (x / m = 0)%nat by lia. clear Eq1.
    rewrite H1 in Eq2. clear H1.
    assert (y / n <> 0)%nat by lia. clear Eq2.
    rewrite Nat.div_small_iff in H1 by lia.
    rewrite Cmult_0_l.
    destruct WF with (x := x) (y := y). lia.
    reflexivity.
  + rewrite andb_false_r.
    assert (x / m <> 0)%nat by lia. clear Eq1.
    rewrite Nat.div_small_iff in H1 by lia.
    rewrite Cmult_0_l.
    destruct WF with (x := x) (y := y). lia.
    reflexivity.
Qed.

Theorem transpose_involutive : forall (m n : nat) (A : Matrix m n), (A⊤)⊤ = A.
Proof. reflexivity. Qed.

Theorem adjoint_involutive : forall (m n : nat) (A : Matrix m n), A†† = A.
Proof. intros. lma. Qed.  

Lemma id_transpose_eq : forall n, (I n)⊤ = (I n).
Proof.
  intros n. unfold transpose, I.
  prep_matrix_equality.
  bdestruct (y =? x); bdestruct (x =? y); bdestruct (y <? n); bdestruct (x <? n);
    trivial; lia.
Qed.

Lemma zero_transpose_eq : forall m n, (@Zero m n)⊤ = @Zero m n.
Proof. reflexivity. Qed.

Lemma id_adjoint_eq : forall n, (I n)† = (I n).
Proof.
  intros n.
  unfold adjoint, I.
  prep_matrix_equality.
  bdestruct (y =? x); bdestruct (x =? y); bdestruct (y <? n); bdestruct (x <? n);
    try lia; lca.
Qed.

Lemma zero_adjoint_eq : forall m n, (@Zero m n)† = @Zero n m.
Proof. unfold adjoint, Zero. rewrite Cconj_0. reflexivity. Qed.

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


Theorem Mmult_assoc : forall {m n o p : nat} (A : Matrix m n) (B : Matrix n o) 
  (C: Matrix o p), A × B × C = A × (B × C).
Proof.
  intros m n o p A B C.
  unfold Mmult.
  prep_matrix_equality.
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

Lemma Mmult_plus_distr_l : forall (m n o : nat) (A : Matrix m n) (B C : Matrix n o), 
                           A × (B .+ C) = A × B .+ A × C.
Proof. 
  intros m n o A B C.
  unfold Mplus, Mmult.
  prep_matrix_equality.
  rewrite <- Csum_plus.
  apply Csum_eq.
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
  rewrite <- Csum_plus.
  apply Csum_eq.
  apply functional_extensionality. intros z.
  rewrite Cmult_plus_distr_r. 
  reflexivity.
Qed.

Lemma kron_plus_distr_l : forall (m n o p : nat) (A : Matrix m n) (B C : Matrix o p), 
                           A ⊗ (B .+ C) = A ⊗ B .+ A ⊗ C.
Proof. 
  intros m n o p A B C.
  unfold Mplus, kron.
  prep_matrix_equality.
  rewrite Cmult_plus_distr_l.
  easy.
Qed.

Lemma kron_plus_distr_r : forall (m n o p : nat) (A B : Matrix m n) (C : Matrix o p), 
                           (A .+ B) ⊗ C = A ⊗ C .+ B ⊗ C.
Proof. 
  intros m n o p A B C.
  unfold Mplus, kron.
  prep_matrix_equality.
  rewrite Cmult_plus_distr_r. 
  reflexivity.
Qed.

Lemma Mscale_0_l : forall (m n : nat) (A : Matrix m n), C0 .* A = Zero.
Proof.
  intros m n A.
  prep_matrix_equality.
  unfold Zero, scale.
  rewrite Cmult_0_l.
  reflexivity.
Qed.

Lemma Mscale_0_r : forall (m n : nat) (c : C), c .* @Zero m n = Zero.
Proof.
  intros m n c.
  prep_matrix_equality.
  unfold Zero, scale.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

Lemma Mscale_1_l : forall (m n : nat) (A : Matrix m n), C1 .* A = A.
Proof.
  intros m n A.
  prep_matrix_equality.
  unfold scale.
  rewrite Cmult_1_l.
  reflexivity.
Qed.

Lemma Mscale_1_r : forall (n : nat) (c : C),
    c .* I n = fun x y => if (x =? y) && (x <? n) then c else C0.
Proof.
  intros n c.
  prep_matrix_equality.
  unfold scale, I.
  destruct ((x =? y) && (x <? n)).
  rewrite Cmult_1_r; reflexivity.
  rewrite Cmult_0_r; reflexivity.
Qed.

Lemma Mscale_assoc : forall (m n : nat) (x y : C) (A : Matrix m n),
  x .* (y .* A) = (x * y) .* A.
Proof.
  intros. unfold scale. prep_matrix_equality.
  rewrite Cmult_assoc; reflexivity.
Qed.

Lemma Mscale_plus_distr_l : forall (m n : nat) (x y : C) (A : Matrix m n),
  (x + y) .* A = x .* A .+ y .* A.
Proof.
  intros. unfold Mplus, scale. prep_matrix_equality. apply Cmult_plus_distr_r.
Qed.

Lemma Mscale_plus_distr_r : forall (m n : nat) (x : C) (A B : Matrix m n),
  x .* (A .+ B) = x .* A .+ x .* B.
Proof.
  intros. unfold Mplus, scale. prep_matrix_equality. apply Cmult_plus_distr_l.
Qed.

Lemma Mscale_mult_dist_l : forall (m n o : nat) (x : C) (A : Matrix m n) (B : Matrix n o), 
    ((x .* A) × B) = x .* (A × B).
Proof.
  intros m n o x A B.
  unfold scale, Mmult.
  prep_matrix_equality.
  rewrite Csum_mult_l.
  apply Csum_eq.
  apply functional_extensionality. intros z.
  rewrite Cmult_assoc.
  reflexivity.
Qed.

Lemma Mscale_mult_dist_r : forall (m n o : nat) (x : C) (A : Matrix m n) (B : Matrix n o),
    (A × (x .* B)) = x .* (A × B).
Proof.
  intros m n o x A B.
  unfold scale, Mmult.
  prep_matrix_equality.
  rewrite Csum_mult_l.
  apply Csum_eq.
  apply functional_extensionality. intros z.
  repeat rewrite Cmult_assoc.
  rewrite (Cmult_comm _ x).
  reflexivity.
Qed.

Lemma Mscale_kron_dist_l : forall (m n o p : nat) (x : C) (A : Matrix m n) (B : Matrix o p), 
    ((x .* A) ⊗ B) = x .* (A ⊗ B).
Proof.
  intros m n o p x A B.
  unfold scale, kron.
  prep_matrix_equality.
  rewrite Cmult_assoc.
  reflexivity.
Qed.

Lemma Mscale_kron_dist_r : forall (m n o p : nat) (x : C) (A : Matrix m n) (B : Matrix o p), 
    (A ⊗ (x .* B)) = x .* (A ⊗ B).
Proof.
  intros m n o p x A B.
  unfold scale, kron.
  prep_matrix_equality.
  rewrite Cmult_assoc.  
  rewrite (Cmult_comm (A _ _) x).
  rewrite Cmult_assoc.  
  reflexivity.
Qed.

Lemma Mscale_trans : forall (m n : nat) (x : C) (A : Matrix m n),
    (x .* A)⊤ = x .* A⊤.
Proof. reflexivity. Qed.

Lemma Mscale_adj : forall (m n : nat) (x : C) (A : Matrix m n),
    (x .* A)† = x^* .* A†.
Proof.
  intros m n x A.
  unfold scale, adjoint.
  prep_matrix_equality.
  rewrite Cconj_mult_distr.          
  reflexivity.
Qed.

(* Inverses of square matrices *)

Definition Minv {n : nat} (A B : Square n) : Prop := A × B = I n /\ B × A = I n.

Lemma Minv_unique : forall (n : nat) (A B C : Square n), 
                      WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
                      Minv A B -> Minv A C -> B = C.
Proof.
  intros n A B C WFA WFB WFC [HAB HBA] [HAC HCA].
  replace B with (B × I n) by (apply Mmult_1_r; assumption).
  rewrite <- HAC.  
  replace C with (I n × C) at 2 by (apply Mmult_1_l; assumption).
  rewrite <- HBA.  
  rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma Minv_symm : forall (n : nat) (A B : Square n), Minv A B -> Minv B A.
Proof. unfold Minv; intuition. Qed.

(* The left inverse of a square matrix is also its right inverse *)
Axiom Minv_flip : forall (n : nat) (A B : Square n), A × B = I n -> B × A = I n.
  
Lemma Minv_left : forall (n : nat) (A B : Square n), A × B = I n -> Minv A B.
Proof.
  intros n A B H. 
  unfold Minv. split; trivial.
  apply Minv_flip.
  assumption.
Qed.

Lemma Minv_right : forall (n : nat) (A B : Square n), B × A = I n -> Minv A B.
Proof.
  intros n A B H. 
  unfold Minv. split; trivial.
  apply Minv_flip.
  assumption.
Qed.

Local Open Scope nat_scope.

(*
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
  p <> 0 -> q <> 0 -> r <> 0 -> s <> 0 -> 
  (A ⊗ B ⊗ C) = A ⊗ (B ⊗ C).                                
Proof.
  intros m n p q r s A B C Hp Hq Hr Hs.
  remember (A ⊗ B ⊗ C) as LHS.
  prep_matrix_equality.
  rename x into i, y into j.
  unfold kron.  
  rewrite (mult_comm p r) at 1 2.
  rewrite (mult_comm q s) at 1 2.
  rewrite <- 2 Nat.div_div by assumption.
  rewrite <- 2 div_mod.
  rewrite 2 mod_product by assumption.
  rewrite Cmult_assoc.
  subst.
  reflexivity.
Qed.  
*)
  
Axiom kron_assoc : forall {m n p q r s : nat}
  (A : Matrix m n) (B : Matrix p q) (C : Matrix r s),
  (A ⊗ B ⊗ C) = A ⊗ (B ⊗ C).                                

Lemma kron_mixed_product : forall {m n o p q r : nat} (A : Matrix m n) (B : Matrix p q ) 
  (C : Matrix n o) (D : Matrix q r), (A ⊗ B) × (C ⊗ D) = (A × C) ⊗ (B × D).
Proof.
  intros m n o p q r A B C D.
  unfold kron, Mmult.
  prep_matrix_equality.
  destruct q.
  + simpl.
    rewrite mult_0_r.
    simpl.
    rewrite Cmult_0_r.
    reflexivity. 
  + rewrite Csum_product.
    apply Csum_eq.
    apply functional_extensionality.
    intros; lca.
    lia.
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

Lemma Mplus_tranpose : forall (m n : nat) (A : Matrix m n) (B : Matrix m n),
  (A .+ B)⊤ = A⊤ .+ B⊤.
Proof. reflexivity. Qed.

Lemma Mmult_tranpose : forall (m n o : nat) (A : Matrix m n) (B : Matrix n o),
      (A × B)⊤ = B⊤ × A⊤.
Proof.
  intros m n o A B.
  unfold Mmult, transpose.
  prep_matrix_equality.
  apply Csum_eq.  
  apply functional_extensionality. intros z.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma kron_transpose : forall (m n o p : nat) (A : Matrix m n) (B : Matrix o p ),
  (A ⊗ B)⊤ = A⊤ ⊗ B⊤.
Proof. reflexivity. Qed.


Lemma Mplus_adjoint : forall (m n : nat) (A : Matrix m n) (B : Matrix m n),
  (A .+ B)† = A† .+ B†.
Proof.  
  intros m n A B.
  unfold Mplus, adjoint.
  prep_matrix_equality.
  rewrite Cconj_plus_distr.
  reflexivity.
Qed.

Lemma Mmult_adjoint : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o),
      (A × B)† = B† × A†.
Proof.
  intros m n o A B.
  unfold Mmult, adjoint.
  prep_matrix_equality.
  rewrite Csum_conj_distr.
  apply Csum_eq.  
  apply functional_extensionality. intros z.
  rewrite Cconj_mult_distr.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma kron_adjoint : forall {m n o p : nat} (A : Matrix m n) (B : Matrix o p),
  (A ⊗ B)† = A† ⊗ B†.
Proof. 
  intros. unfold adjoint, kron. 
  prep_matrix_equality.
  rewrite Cconj_mult_distr.
  reflexivity.
Qed.

Lemma id_kron : forall (m n : nat),  I m ⊗ I n = I (m * n).
Proof.
  intros.
  unfold I, kron.
  prep_matrix_equality.
  bdestruct (x =? y); rename H into Eq; subst.
  + repeat rewrite <- beq_nat_refl; simpl.
    destruct n.
    - simpl.
      rewrite mult_0_r.
      bdestruct (y <? 0); try lia.
      autorewrite with C_db; reflexivity.
    - bdestruct (y mod S n <? S n). 
      2: specialize (Nat.mod_upper_bound y (S n)); intros; lia. 
      rewrite Cmult_1_r.
      destruct (y / S n <? m) eqn:L1, (y <? m * S n) eqn:L2; trivial.
      * apply Nat.ltb_lt in L1. 
        apply Nat.ltb_nlt in L2. 
        contradict L2. 
        (* Why doesn't this lemma exist??? *)
        destruct m.
        lia.
        apply Nat.div_small_iff; try lia.
        apply Nat.div_small in L1.
        rewrite Nat.div_div in L1; try lia.
        rewrite mult_comm.
        assumption.
      * apply Nat.ltb_nlt in L1. 
        apply Nat.ltb_lt in L2. 
        contradict L1. 
        apply Nat.div_lt_upper_bound. lia.
        rewrite mult_comm.
        assumption.
  + simpl.
    bdestruct (x / n =? y / n); simpl; try lca.
    bdestruct (x mod n =? y mod n); simpl; try lca.
    destruct n; try lca.    
    contradict Eq.
    rewrite (Nat.div_mod x (S n)) by lia.
    rewrite (Nat.div_mod y (S n)) by lia.
    rewrite H, H0; reflexivity.
Qed.

Lemma outer_product_eq : forall m (φ ψ : Matrix m 1),
 φ = ψ -> outer_product φ φ = outer_product ψ ψ.
Proof. congruence. Qed.

Lemma outer_product_kron : forall m n (φ : Matrix m 1) (ψ : Matrix n 1), 
    outer_product φ φ ⊗ outer_product ψ ψ = outer_product (φ ⊗ ψ) (φ ⊗ ψ).
Proof. 
  intros. unfold outer_product. 
  specialize (kron_adjoint φ ψ) as KT. 
  simpl in *. rewrite KT.
  specialize (kron_mixed_product φ ψ (φ†) (ψ†)) as KM. 
  simpl in *. rewrite KM.
  reflexivity.
Qed.

(* Useful kron_n identities. *)
Lemma kron_n_assoc :
  forall n {m1 m2} (A : Matrix m1 m2), WF_Matrix A -> (S n) ⨂ A = A ⊗ (n ⨂ A).
Proof.
  intros. induction n.
  - simpl. 
    rewrite kron_1_r. 
    rewrite kron_1_l; try assumption.
    reflexivity.
  - simpl.
    replace (m1 * (m1 ^ n)) with ((m1 ^ n) * m1) by apply Nat.mul_comm.
    replace (m2 * (m2 ^ n)) with ((m2 ^ n) * m2) by apply Nat.mul_comm.
    rewrite <- kron_assoc.
    rewrite <- IHn.
    reflexivity.
Qed.

Lemma kron_n_adjoint : forall n {m1 m2} (A : Matrix m1 m2),
  WF_Matrix A -> (n ⨂ A)† = n ⨂ A†.
Proof.
  intros. induction n.
  - simpl. apply id_adjoint_eq.
  - simpl.
    replace (m1 * (m1 ^ n)) with ((m1 ^ n) * m1) by apply Nat.mul_comm.
    replace (m2 * (m2 ^ n)) with ((m2 ^ n) * m2) by apply Nat.mul_comm.
    rewrite kron_adjoint, IHn.
    reflexivity.
Qed.

(* Note on "using [tactics]": Most generated subgoals will be of the form 
   WF_Matrix M, where auto with wf_db will work.
   Occasionally WF_Matrix M will rely on rewriting to match an assumption in the 
   context, here we recursively autorewrite (which adds time). 
   kron_1_l requires proofs of (n > 0)%nat, here we use lia. *)

(* *)

(*******************************)
(* Restoring Matrix Dimensions *)
(*******************************)

(** Restoring Matrix dimensions *)
Ltac is_nat n := match type of n with nat => idtac end.

Ltac is_nat_equality :=
  match goal with 
  | |- ?A = ?B => is_nat A
  end.

Ltac unify_matrix_dims tac := 
  try reflexivity; 
  repeat (apply f_equal_gen; try reflexivity; 
          try (is_nat_equality; tac)).

Ltac restore_dims_rec A :=
   match A with
(* special cases *)
  | ?A × I _          => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (I n'))
                        end
  | I _ × ?B          => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (I n')  B')
                        end
  | ?A × @Zero ?n ?n  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (@Zero n' n'))
                        end
  | @Zero ?n ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero n' n') B')
                        end
  | ?A × @Zero ?n ?o  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' o A' (@Zero n' o))
                        end
  | @Zero ?m ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero m n') B')
                        end
  | ?A .+ @Zero ?m ?n => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mplus m' n' A' (@Zero m' n'))
                        end
  | @Zero ?m ?n .+ ?B => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?m' ?n' => constr:(@Mplus m' n' (@Zero m' n') B')
                        end
(* general cases *)
  | ?A = ?B  => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' => constr:(@eq (Matrix m' n') A' B')
                  end
  | ?A × ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' =>
                  match type of B' with 
                  | Matrix ?n'' ?o' => constr:(@Mmult m' n' o' A' B')
                  end
                end 
  | ?A ⊗ ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' =>
                  match type of B' with 
                  | Matrix ?o' ?p' => constr:(@kron m' n' o' p' A' B')
                  end
                end
  | ?A †      => let A' := restore_dims_rec A in 
                match type of A' with
                | Matrix ?m' ?n' => constr:(@adjoint m' n' A')
                end
  | ?A .+ ?B => let A' := restore_dims_rec A in 
               let B' := restore_dims_rec B in 
               match type of A' with 
               | Matrix ?m' ?n' =>
                 match type of B' with 
                 | Matrix ?m'' ?n'' => constr:(@Mplus m' n' A' B')
                 end
               end
  | ?c .* ?A => let A' := restore_dims_rec A in 
               match type of A' with
               | Matrix ?m' ?n' => constr:(@scale m' n' c A')
               end
  (* For predicates (eg. WF_Matrix, Mixed_State) on Matrices *)
  | ?P ?m ?n ?A => match type of P with
                  | nat -> nat -> Matrix _ _ -> Prop =>
                    let A' := restore_dims_rec A in 
                    match type of A' with
                    | Matrix ?m' ?n' => constr:(P m' n' A')
                    end
                  end
  | ?P ?n ?A => match type of P with
               | nat -> Matrix _ _ -> Prop =>
                 let A' := restore_dims_rec A in 
                 match type of A' with
                 | Matrix ?m' ?n' => constr:(P m' A')
                 end
               end
  (* Handle functions applied to matrices *)
  | ?f ?A    => let f' := restore_dims_rec f in 
               let A' := restore_dims_rec A in 
               constr:(f' A')
  (* default *)
  | ?A       => A
   end.

Ltac restore_dims tac := 
  match goal with
  | |- ?A      => let A' := restore_dims_rec A in 
                replace A with A' by unify_matrix_dims tac
  end.

Tactic Notation "restore_dims" tactic(tac) := restore_dims tac.

Tactic Notation "restore_dims" := restore_dims (try ring; unify_pows_two; simpl; lia).

(*************************)
(* Matrix Simplification *)
(*************************)

(* Old: 
Hint Rewrite kron_1_l kron_1_r Mmult_1_l Mmult_1_r id_kron id_adjoint_eq
     @Mmult_adjoint Mplus_adjoint @kron_adjoint @kron_mixed_product
     id_adjoint_eq adjoint_involutive using 
     (auto 100 with wf_db; autorewrite with M_db; auto 100 with wf_db; lia) : M_db.
*)

(* eauto will cause major choking... *)
Hint Rewrite  @kron_1_l @kron_1_r @Mmult_1_l @Mmult_1_r @Mscale_1_l 
     @id_adjoint_eq @id_transpose_eq using (auto 100 with wf_db) : M_db_light.
Hint Rewrite @kron_0_l @kron_0_r @Mmult_0_l @Mmult_0_r @Mplus_0_l @Mplus_0_r
     @Mscale_0_l @Mscale_0_r @zero_adjoint_eq @zero_transpose_eq using (auto 100 with wf_db) : M_db_light.

(* I don't like always doing restore_dims first, but otherwise sometimes leaves 
   unsolvable WF_Matrix goals. *)
Ltac Msimpl_light := try restore_dims; autorewrite with M_db_light.

Hint Rewrite @Mmult_adjoint @Mplus_adjoint @kron_adjoint @kron_mixed_product
     @adjoint_involutive using (auto 100 with wf_db) : M_db.

Ltac Msimpl := try restore_dims; autorewrite with M_db_light M_db.

(** Distribute addition to the outside of matrix expressions. *)

Ltac distribute_plus :=
  repeat match goal with 
  | |- context [?a × (?b .+ ?c)] => rewrite (Mmult_plus_distr_l _ _ _ a b c)
  | |- context [(?a .+ ?b) × ?c] => rewrite (Mmult_plus_distr_r _ _ _ a b c)
  | |- context [?a ⊗ (?b .+ ?c)] => rewrite (kron_plus_distr_l _ _ _ _ a b c)
  | |- context [(?a .+ ?b) ⊗ ?c] => rewrite (kron_plus_distr_r _ _ _ _ a b c)
  end.

(** Distribute scaling to the outside of matrix expressions *)

Ltac distribute_scale := 
  repeat
   match goal with
   | |- context [ (?c .* ?A) × ?B   ] => rewrite (Mscale_mult_dist_l _ _ _ c A B)
   | |- context [ ?A × (?c .* ?B)   ] => rewrite (Mscale_mult_dist_r _ _ _ c A B)
   | |- context [ (?c .* ?A) ⊗ ?B   ] => rewrite (Mscale_kron_dist_l _ _ _ _ c A B)
   | |- context [ ?A ⊗ (?c .* ?B)   ] => rewrite (Mscale_kron_dist_r _ _ _ _ c A B)
   | |- context [ ?c .* (?c' .* ?A) ] => rewrite (Mscale_assoc _ _ c c' A)
   end.


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


(* Helper function for crunch_matrix *)
Ltac solve_out_of_bounds := 
  repeat match goal with 
  | [H : WF_Matrix ?M |- context[?M ?a ?b] ] => 
      rewrite (H a b) by (left; simpl; lia) 
  | [H : WF_Matrix ?M |- context[?M ?a ?b] ] => 
      rewrite (H a b) by (right; simpl; lia) 
  end;
  autorewrite with C_db; auto.


Lemma divmod_eq : forall x y n z, 
  fst (Nat.divmod x y n z) = (n + fst (Nat.divmod x y 0 z))%nat.
Proof.
  induction x.
  + intros. simpl. lia.
  + intros. simpl. 
    destruct z.
    rewrite IHx.
    rewrite IHx with (n:=1%nat).
    lia.
    rewrite IHx.
    reflexivity.
Qed.

Lemma divmod_S : forall x y n z, 
  fst (Nat.divmod x y (S n) z) = (S n + fst (Nat.divmod x y 0 z))%nat.
Proof. intros. apply divmod_eq. Qed.

Ltac destruct_m_1' :=
  match goal with
  | [ |- context[match ?x with 
                 | 0   => _
                 | S _ => _
                 end] ] => is_var x; destruct x
  | [ |- context[match fst (Nat.divmod ?x _ _ _) with 
                 | 0   => _
                 | S _ => _
                 end] ] => is_var x; destruct x
  end.

Lemma divmod_0q0 : forall x q, fst (Nat.divmod x 0 q 0) = (x + q)%nat. 
Proof.
  induction x.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite IHx. lia.
Qed.

Lemma divmod_0 : forall x, fst (Nat.divmod x 0 0 0) = x. 
Proof. intros. rewrite divmod_0q0. lia. Qed.

Ltac destruct_m_eq' := repeat 
  (progress (try destruct_m_1'; try rewrite divmod_0; try rewrite divmod_S; simpl)).

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
                      autounfold with U_db;
                      prep_matrix_equality;
                      simpl;
                      destruct_m_eq';
                      simpl;
                      Csimpl; (* basic rewrites only *) 
                      try reflexivity;
                      try solve_out_of_bounds. 

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

(*********************************************************)
(**                         Gridify                     **)
(*********************************************************)

(** Gridify: Turns an matrix expression into a normal form with 
    plus on the outside, then tensor, then matrix multiplication.
    Eg: ((..×..×..)⊗(..×..×..)⊗(..×..×..)) .+ ((..×..)⊗(..×..))
*)

Local Open Scope nat_scope.

Lemma repad_lemma1_l : forall (a b d : nat),
  a < b -> d = (b - a - 1) -> b = a + 1 + d.
Proof. intros. subst. lia. Qed. 

Lemma repad_lemma1_r : forall (a b d : nat),
  a < b -> d = (b - a - 1) -> b = d + 1 + a.
Proof. intros. subst. lia. Qed.

Lemma repad_lemma2 : forall (a b d : nat),
  a <= b -> d = (b - a) -> b = a + d.
Proof. intros. subst. lia. Qed.

Lemma le_ex_diff_l : forall a b, a <= b -> exists d, b = d + a. 
Proof. intros. exists (b - a). lia. Qed.

Lemma le_ex_diff_r : forall a b, a <= b -> exists d, b = a + d. 
Proof. intros. exists (b - a). lia. Qed.  

Lemma lt_ex_diff_l : forall a b, a < b -> exists d, b = d + 1 + a. 
Proof. intros. exists (b - a - 1). lia. Qed.

Lemma lt_ex_diff_r : forall a b, a < b -> exists d, b = a + 1 + d. 
Proof. intros. exists (b - a - 1). lia. Qed.

Ltac bdestruct_all :=
  repeat match goal with
  | |- context[?a <? ?b] => bdestruct (a <? b)
  | |- context[?a <=? ?b] => bdestruct (a <=? b)                                       
  | |- context[?a =? ?b] => bdestruct (a =? b)
  end; try (exfalso; lia).

(* Remove _ < _ from hyps, remove _ - _  from goal *)
Ltac remember_differences :=
  repeat match goal with
  | H : ?a < ?b |- context[?b - ?a - 1] => 
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a - 1) as d eqn:R ;
    apply (repad_lemma1_l a b d) in H; trivial;
    clear R;
    try rewrite H in *;
    try clear b H
  | H:?a <= ?b  |- context [ ?b - ?a ] =>
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a) as d eqn:R ;
    apply (repad_lemma2 a b d) in H; trivial;
    clear R;
    try rewrite H in *;
    try clear b H
  end.

(* gets the exponents of the dimensions of the given matrix expression *)
(* assumes all matrices are square *)
Ltac get_dimensions M :=
  match M with
  | ?A ⊗ ?B  => let a := get_dimensions A in
               let b := get_dimensions B in
               constr:(a + b)
  | ?A .+ ?B => get_dimensions A
  | _        => match type of M with
               | Matrix 2 2 => constr:(1)
               | Matrix 4 4 => constr:(2)
               | Matrix (2^?a) (2^?a) => constr:(a)
(*             | Matrix ?a ?b => idtac "bad dims";
                                idtac M;
                                constr:(a) *)
               end
  end.

(* not necessary in this instance - produced hypothesis is H1 *)
(* This is probably fragile and should be rewritten *)
(*
Ltac hypothesize_dims :=
  match goal with
  | |- ?A × ?B = _ => let a := get_dimensions A in
                    let b := get_dimensions B in
                    assert(a = b) by lia
  | |- _ = ?A × ?B => let a := get_dimensions A in
                    let b := get_dimensions B in
                    assert(a = b) by lia
  end.
*)

(* Hopefully always grabs the outermost product. *)
Ltac hypothesize_dims :=
  match goal with
  | |- context[?A × ?B] => let a := get_dimensions A in
                         let b := get_dimensions B in
                         assert(a = b) by lia
  end.

(* Unifies an equation of the form `a + 1 + b + 1 + c = a' + 1 + b' + 1 + c'`
   (exact symmetry isn't required) by filling in the holes *) 
Ltac fill_differences :=
  repeat match goal with 
  | R : _ < _ |- _           => let d := fresh "d" in
                              destruct (lt_ex_diff_r _ _ R);
                              clear R; subst
  | H : _ = _ |- _           => rewrite <- plus_assoc in H
  | H : ?a + _ = ?a + _ |- _ => apply Nat.add_cancel_l in H; subst
  | H : ?a + _ = ?b + _ |- _ => destruct (lt_eq_lt_dec a b) as [[?|?]|?]; subst
  end; try lia.

Ltac repad := 
  (* remove boolean comparisons *)
  bdestruct_all; Msimpl_light; try reflexivity;
  (* remove minus signs *) 
  remember_differences;
  (* put dimensions in hypothesis [will sometimes exist] *)
  try hypothesize_dims; clear_dups;
  (* where a < b, replace b with a + 1 + fresh *)
  fill_differences.

Ltac gridify :=
  (* remove boolean comparisons *)
  bdestruct_all; Msimpl_light; try reflexivity;
  (* remove minus signs *) 
  remember_differences;
  (* put dimensions in hypothesis [will sometimes exist] *)
  try hypothesize_dims; clear_dups;
  (* where a < b, replace b with a + 1 + fresh *)
  fill_differences;
  (* distribute *)  
  restore_dims; distribute_plus;
  repeat rewrite Nat.pow_add_r;
  repeat rewrite <- id_kron; simpl;
  repeat rewrite mult_assoc;
  restore_dims; repeat rewrite <- kron_assoc;
  restore_dims; repeat rewrite kron_mixed_product;
  (* simplify *)
  Msimpl_light.

(**************************************)
(* Tactics to show implicit arguments *)
(**************************************)

Definition kron' := @kron.      
Lemma kron_shadow : @kron = kron'. Proof. reflexivity. Qed.

Definition Mmult' := @Mmult.
Lemma Mmult_shadow : @Mmult = Mmult'. Proof. reflexivity. Qed.

Ltac show_dimensions := try rewrite kron_shadow in *; 
                        try rewrite Mmult_shadow in *.
Ltac hide_dimensions := try rewrite <- kron_shadow in *; 
                        try rewrite <- Mmult_shadow in *.
