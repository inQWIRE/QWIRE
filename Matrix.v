Require Import Reals.
Require Import Complex.
Require Import Psatz.
Require Import String.

Require Export Prelim.

Open Scope R_scope.
Open Scope C_scope.
Open Scope nat_scope.

Bind Scope nat_scope with nat.
Bind Scope R_scope with R.
Bind Scope C_scope with C.

(*******************************************)
(** Matrix Definitions and infrastructure **)
(*******************************************)

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

(* List Representation *)
    
Definition list2D_to_matrix (l : list (list C)) : 
  Matrix (length l) (length (hd [] l)) :=
  (fun x y => nth y (nth x l []) 0%R).


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

Definition Zero (m n : nat) : Matrix m n := fun x y => 0%R.

Definition Id (n : nat) : Square n := 
  (fun x y => if (x =? y) && (x <? n) then C1 else C0).
Definition I1 := Id (2^0).
Notation "'I_ n" := (Id n) (at level 10).
Definition I__inf := fun x y => if x =? y then C1 else C0.
Notation "I∞" := I__inf.

(* sum to n exclusive *)
Fixpoint Csum (f : nat -> C) (n : nat) : C := 
  match n with
  | 0 => C0
  | S n' => (Csum f n' +  f n')%C
  end.

Definition trace {n : nat} (A : Square n) := 
  Csum (fun x => A x x) n.

Definition scale {m n : nat} (r : C) (A : Matrix m n) : Matrix m n := 
  (fun x y => (r * A x y)%C).

Definition dot {n : nat} (A : Matrix 1 n) (B : Matrix n 1) : C :=
  Csum (fun x => A O x  * B x O)%C n.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  (fun x y => (A x y + B x y)%C).


Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o := 
  (fun x z => Csum (fun y => A x y * B y z)%C n).


(* Only well-defined when o and p are non-zero *)
Definition kron {m n o p : nat} (A : Matrix m n) (B : Matrix o p) : 
  Matrix (m*o) (n*p) :=
  (fun x y => Cmult (A (x / o) (y / p)) (B (x mod o) (y mod p))).

Definition transpose {m n} (A : Matrix m n) : Matrix n m := 
    (fun x y => A y x).

Definition conj_transpose {m n} (A : Matrix m n) : Matrix n m := 
  (fun x y => Cconj (A y x)).

Definition outer_product {m} (v : Matrix m 1) : Square m := 
  Mmult v (conj_transpose v).

(* Kronecker of n copies of A *)
Fixpoint kron_n n {m1 m2} (A : Matrix m1 m2) : Matrix (m1^n) (m2^n) :=
  match n with
  | 0    => 'I_1
  | S n' => kron A (kron_n n' A)
  end.

(* Kronecker product of a list *)
Fixpoint big_kron {m n} (As : list (Matrix m n)) : 
  Matrix (m^(length As)) (n^(length As)) := 
  match As with
  | [] => 'I_1
  | A :: As' => kron A (big_kron As')
  end.

Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Infix ".+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix ".*" := scale (at level 40, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Infix "≡" := mat_equiv (at level 70) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope. 
Notation "A †" := (conj_transpose A) (at level 0) : matrix_scope. 
Notation "Σ^ n f" := (Csum f n) (at level 60) : matrix_scope.
Notation "n ⨂ A" := (kron_n n A) (at level 30, no associativity) : matrix_scope.
Notation "⨂ A" := (big_kron A) (at level 60): matrix_scope.
Hint Unfold Zero Id trace dot Mplus scale Mmult kron mat_equiv transpose 
            conj_transpose : M_db.

Open Scope matrix_scope.
Delimit Scope matrix_scope with M.
  
Ltac destruct_m_1 :=
  match goal with
  | [ |- context[match ?x with 
                 | 0   => _
                 | S _ => _
                 end] ] => is_var x; destruct x
  end.
Ltac destruct_m_eq := repeat (destruct_m_1; simpl).

Ltac mlra := 
  autounfold with M_db;
  prep_matrix_equality;
  destruct_m_eq; 
  clra.

(******************************)
(** Proofs about finite sums **)
(******************************)

Close Scope nat_scope.

Lemma Csum_0 : forall f n, (forall x, f x = C0) -> Csum f n = 0. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, H. 
    clra.
Qed.

Lemma Csum_1 : forall f n, (forall x, f x = C1) -> Csum f n = INR n. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, H. 
    destruct n; clra.    
Qed.

Lemma Csum_constant : forall c n, Csum (fun x => c) n = INR n * c.
Proof.
  intros c n.
  induction n.
  + simpl; clra.
  + simpl.
    rewrite IHn.
    destruct n; clra.
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
    clra.
    omega.
    intros.
    apply H.
    omega.
Qed.

Lemma Csum_eq_bounded : forall f g n, (forall x, (x < n)%nat -> f x = g x) -> Csum f n = Csum g n.
Proof. 
  intros f g n H. 
  induction n.
  + simpl. reflexivity.
  + simpl. 
    rewrite H by omega.
    rewrite IHn by (intros; apply H; omega).
    reflexivity.
Qed.

Lemma Csum_plus : forall f g n, Csum (fun x => f x + g x) n = Csum f n + Csum g n.
Proof.
  intros f g n.
  induction n.
  + simpl. clra.
  + simpl. rewrite IHn. clra.
Qed.

Lemma Csum_mult_l : forall c f n, c * Csum f n = Csum (fun x => c * f x) n.
Proof.
  intros c f n.
  induction n.
  + simpl; clra.
  + simpl.
    rewrite Cmult_plus_distr_l.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Csum_mult_r : forall c f n, Csum f n * c = Csum (fun x => f x * c) n.
Proof.
  intros c f n.
  induction n.
  + simpl; clra.
  + simpl.
    rewrite Cmult_plus_distr_r.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Csum_conj_distr : forall f n, (Csum f n) ^* = Csum (fun x => (f x)^*) n.
Proof. 
  intros f n.
  induction n.
  + simpl; clra.
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
  + simpl; clra.
  + simpl.
    rewrite Cplus_assoc.
    rewrite IHn.
    simpl.
    reflexivity.
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
    Focus 2. apply Csum_eq. subst. apply functional_extensionality.
    intros; rewrite <- plus_n_Sm. reflexivity.
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
  + simpl; clra.
  + simpl.      
    rewrite Cmult_plus_distr_r.
    rewrite IHm. clear IHm.
    rewrite Csum_mult_l.    
    remember ((fun x : nat => f (x / n)%nat * g (x mod n)%nat)) as h.
    replace (Csum (fun x : nat => f m * g x) n) with
            (Csum (fun x : nat => h ((m * n) + x)%nat) n). 
    Focus 2.
      subst.
      apply Csum_eq_bounded.
      intros x Hx.
      rewrite Nat.div_add_l by assumption.
      rewrite Nat.div_small; trivial.
      rewrite plus_0_r.
      rewrite Nat.add_mod by assumption.
      rewrite Nat.mod_mul by assumption.
      rewrite plus_0_l.
      repeat rewrite Nat.mod_small; trivial.
    rewrite <- Csum_sum.
    rewrite plus_comm.
    reflexivity.
Qed.


(**********************************)
(** Proofs about Well-Formedness **)
(**********************************)

Open Scope nat_scope.

Lemma WF_Zero : forall {m n : nat}, WF_Matrix m n (Zero m n).
Proof. intros m n. unfold WF_Matrix. reflexivity. Qed.

Lemma WF_Id : forall {n : nat}, WF_Matrix n n (Id n). 
Proof. 
  unfold WF_Matrix, Id. intros n x y H.
  simpl.
  destruct H; bdestruct (x =? y); bdestruct (x <? n); trivial; omega.
Qed.

Lemma WF_I1 : WF_Matrix 1 1 I1. Proof. apply WF_Id. Qed.

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
  intros m n o A B H H0 x y D. simpl.
  apply Csum_0.
  destruct D; intros z.
  + rewrite H; [clra | auto].
  + rewrite H0; [clra | auto].
Qed.

Lemma WF_kron : forall {m n o p q r : nat} (A : Matrix m n) (B : Matrix o p), 
                  q = m * o -> r = n * p -> 
                  WF_Matrix m n A -> WF_Matrix o p B -> WF_Matrix q r (A ⊗ B).
Proof.
  unfold WF_Matrix, kron.
  intros m n o p q r A B Nn No H H0 x y H1. subst.
  bdestruct (o =? 0). rewrite H0; [clra|omega]. 
  bdestruct (p =? 0). rewrite H0; [clra|omega]. 
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

Lemma WF_outer_product : forall {n} (v : Matrix n 1), WF_Matrix n 1 v ->
                                                 WF_Matrix n n (outer_product v).
Proof. intros. apply WF_mult; [|apply WF_conj_transpose]; assumption. Qed.

Lemma WF_big_kron : forall n m (l : list (Matrix m n)) (A : Matrix m n), 
                        (forall i, WF_Matrix m n (nth i l A)) ->
                         WF_Matrix (m^(length l)) (n^(length l)) (⨂ l). 
Proof.                         
  intros n m l A H.
  induction l.
  - simpl. apply WF_Id.
  - simpl. apply WF_kron; trivial. apply (H O).
    apply IHl. intros i. apply (H (S i)).
Qed.

(***************************************)
(* Tactics for showing well-formedness *)
(***************************************)

Ltac show_wf := 
  repeat match goal with
  | [ |- WF_Matrix _ _ (?A × ?B) ]  => apply WF_mult 
  | [ |- WF_Matrix _ _ (?A .+ ?B) ] => apply WF_plus 
  | [ |- WF_Matrix _ _ (?p .* ?B) ] => apply WF_scale
  | [ |- WF_Matrix _ _ (?A ⊗ ?B) ]  => apply WF_kron
  | [ |- WF_Matrix _ _ (?A⊤) ]      => apply WF_transpose 
  | [ |- WF_Matrix _ _ (?A†) ]      => apply WF_conj_transpose 
  | [ |- WF_Matrix _ _ (Id _) ]     => apply WF_Id
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
Hint Resolve WF_Zero WF_Id WF_I1 WF_mult WF_plus WF_scale WF_transpose 
     WF_conj_transpose WF_outer_product WF_big_kron WF_kron : wf_db.
Hint Extern 2 (_ = _) => unify_pows_two : wf_db.


(** Basic Matrix Lemmas **)

Lemma trace_plus_dist : forall (n : nat) (A B : Square n), 
    trace (A .+ B) = (trace A + trace B)%C. 
Proof. 
  intros.
  unfold trace, Mplus.
  induction n.
  - simpl. clra.
  - simpl. rewrite IHn. clra.
Qed.

Lemma trace_mult_dist : forall n p (A : Square n), trace (p .* A) = (p * trace A)%C. 
  intros.
  unfold trace, scale.
  induction n.
  - simpl. clra.
  - simpl. rewrite IHn. clra.
Qed.

Lemma Mplus_0_l : forall (m n : nat) (A : Matrix m n), Zero m n .+ A = A.
Proof. intros. mlra. Qed.

Lemma Mplus_0_r : forall (m n : nat) (A : Matrix m n), A .+ Zero m n = A.
Proof. intros. mlra. Qed.
    
Lemma Mmult_0_l : forall (m n o : nat) (A : Matrix n o), (Zero m n) × A = Zero m o.
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

Lemma Mmult_0_r : forall (m n o : nat) (A : Matrix m n), A × Zero n o = Zero m o.
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
  k <= m ->
  (k <= x -> Csum (fun y : nat => ((Id m) x y * A y z)%C) k = C0) /\
  (k > x -> Csum (fun y : nat => ((Id m) x y * A y z)%C) k = A x z).
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
  (k <= z -> Csum (fun y : nat => (A x y * (Id n) y z)%C) k = C0) /\
  (k > z -> Csum (fun y : nat => (A x y * (Id n) y z)%C) k = A x z).
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

(* Cool facts about I∞, not used in the development *) 
Lemma Mmult_inf_l : forall(m n : nat) (A : Matrix m n),
  WF_Matrix m n A -> I∞ × A = A.
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
  unfold I__inf, Id.
  bdestruct (x =? z). omega. clra.  
  unfold I__inf, Id in *.
  erewrite Csum_eq.
  apply Hr.
  assumption.
  bdestruct (x <? m); [|omega]. 
  apply functional_extensionality. intros. rewrite andb_true_r. reflexivity.
Qed.

Lemma Mmult_inf_r : forall(m n : nat) (A : Matrix m n),
  WF_Matrix m n A -> A × I∞ = A.
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
  unfold I__inf, Id.
  bdestruct (z =? y). omega. clra.  
  unfold I__inf, Id in *.
  erewrite Csum_eq.
  apply Hr.
  assumption.
  apply functional_extensionality. intros z. 
  bdestruct (z =? y); bdestruct (z <? n); simpl; try clra; try omega. 
Qed.

Lemma kron_0_l : forall (m n o p : nat) (A : Matrix o p), 
  Zero m n ⊗ A = Zero (m * o) (n * p).
Proof.
  intros m n o p A.
  prep_matrix_equality.
  unfold Zero, kron.
  rewrite Cmult_0_l.
  reflexivity.
Qed.

Lemma kron_0_r : forall (m n o p : nat) (A : Matrix m n), 
   A ⊗ Zero o p = Zero (m * o) (n * p).
Proof.
  intros m n o p A.
  prep_matrix_equality.
  unfold Zero, kron.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

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
  WF_Matrix m n A -> Id 1 ⊗ A = A.
Proof.
  intros m n A WF.
  prep_matrix_equality.
  unfold Id, kron.
  bdestruct (m =? 0). rewrite 2 WF by omega. clra.
  bdestruct (n =? 0). rewrite 2 WF by omega. clra.
  bdestruct (x / m <? 1); rename H1 into Eq1.
  bdestruct (x / m =? y / n); rename H1 into Eq2; simpl.
  + assert (x / m = 0) by omega. clear Eq1. rename H1 into Eq1.
    rewrite Eq1 in Eq2.     
    symmetry in Eq2.
    rewrite Nat.div_small_iff in Eq2 by omega.
    rewrite Nat.div_small_iff in Eq1 by omega.
    rewrite 2 Nat.mod_small; trivial.
    clra.
  + assert (x / m = 0) by omega. clear Eq1.
    rewrite H1 in Eq2. clear H1.
    assert (y / n <> 0) by omega. clear Eq2.
    rewrite Nat.div_small_iff in H1 by omega.
    rewrite Cmult_0_l.
    destruct WF with (x := x) (y := y). omega.
    reflexivity.
  + rewrite andb_false_r.
    assert (x / m <> 0) by omega. clear Eq1.
    rewrite Nat.div_small_iff in H1 by omega.
    rewrite Cmult_0_l.
    destruct WF with (x := x) (y := y). omega.
    reflexivity.
Qed.

Theorem transpose_involutive : forall (m n : nat) (A : Matrix m n), (A⊤)⊤ = A.
Proof. reflexivity. Qed.

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

(*
Lemma kron_assoc : forall (m n o p q r : nat) (A : Matrix m n) (B : Matrix o p) 
  (C : Matrix q r), (A ⊗ B ⊗ C) = A ⊗ (B ⊗ C).
Proof.
  intros m n o p q r A B C.
  unfold kron.
  prep_matrix_equality.
  Search (_ / _ / _)%nat.
  repeat rewrite Nat.div_div.
  rewrite (mult_comm q o).
  rewrite (mult_comm r p).
  Search Nat.modulo.
  Search (_ mod (_ * _))%nat.

Lemma mod_product : forall x y z, y <> 0 -> x mod (y * z) mod z = x mod z.
Proof.  
  induction z.
  - intros. simpl. reflexivity.
  - intros. simpl.
    unfold Nat.modulo in IHz.
*)    

Lemma kron_mixed_product : forall (m n o p q r : nat) (A : Matrix m n) (B : Matrix p q ) 
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
    intros; clra.
    omega.
Qed.  


Theorem kron_transpose : forall (m n o p : nat) (A : Matrix m n) (B : Matrix o p ),
  (A ⊗ B)⊤ = A⊤ ⊗ B⊤.
Proof. reflexivity. Qed.
  
Lemma Mmult_conj_transpose : forall (m n o : nat) (A : Matrix m n) (B : Matrix n o),
      (A × B)† = B† × A†.
Proof.
  intros m n o A B.
  unfold Mmult, conj_transpose.
  prep_matrix_equality.
  rewrite Csum_conj_distr.
  apply Csum_eq.  
  apply functional_extensionality. intros z.
  rewrite Cconj_mult_distr.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma kron_conj_transpose : forall (m n o p : nat) (A : Matrix m n) (B : Matrix o p ),
  (A ⊗ B)† = A† ⊗ B†.
Proof. 
  intros. unfold conj_transpose, kron. 
  prep_matrix_equality.
  rewrite Cconj_mult_distr.
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

Lemma outer_product_eq : forall m (φ ψ : Matrix m 1), φ = ψ -> 
                                                 outer_product φ = outer_product ψ.
Proof. congruence. Qed.

Lemma outer_product_kron : forall m n (φ : Matrix m 1) (ψ : Matrix n 1), 
    outer_product φ ⊗ outer_product ψ = outer_product (φ ⊗ ψ).
Proof. 
  intros. unfold outer_product. 
  specialize (kron_conj_transpose _ _ _ _ φ ψ) as KT. 
  simpl in *. rewrite KT.
  specialize (kron_mixed_product _ _ _ _ _ _ φ ψ (φ†) (ψ†)) as KM. 
  simpl in *. rewrite KM.
  reflexivity.
Qed.

Hint Rewrite kron_1_l kron_1_r Mmult_1_l Mmult_1_r id_conj_transpose_eq
     Mmult_conj_transpose kron_conj_transpose
     id_conj_transpose_eq conj_transpose_involutive using 
     (auto 100 with wf_db; autorewrite with M_db; auto 100 with wf_db; omega) : M_db.

(* Note on "using [tactics]": Most generated subgoals will be of the form 
   WF_Matrix M, where auto with wf_db will work.
   Occasionally WF_Matrix M will rely on rewriting to match an assumption in the 
   context, here we recursively autorewrite (which adds time). 
   kron_1_l requires proofs of (n > 0)%nat, here we use omega. *)

(* *)



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
       specialize (Mmult_assoc _ _ _ _ A B C) as H; simpl in H; rewrite H; clear H
  | [|- context[@Mmult ?m ?o ?p (@Mmult ?m ?n ?o ?A ?B) ?C]] => tac_lt n o; tac_lt n m; 
       let H := fresh "H" in 
       specialize (Mmult_assoc _ _ _ _ A B C) as H; simpl in H; rewrite H; clear H
  | [|- context[@Mmult ?m ?n ?p ?A (@Mmult ?n ?o ?p ?B ?C)]] => tac_lt m n; tac_lt m p; 
       let H := fresh "H" in 
       specialize (Mmult_assoc _ _ _ _ A B C) as H; simpl in H; rewrite <- H; clear H
  | [|- context[@Mmult ?m ?n ?p ?A (@Mmult ?n ?o ?p ?B ?C)]] => tac_lt o n; tac_lt o p; 
       let H := fresh "H" in 
       specialize (Mmult_assoc _ _ _ _ A B C) as H; simpl in H; rewrite <- H; clear H
  end).

(* Helper function for crunch_matrix *)
Ltac solve_out_of_bounds := 
  repeat match goal with 
  | [H : WF_Matrix _ _ ?M |- context[?M ?a ?b] ] => 
      rewrite (H a b) by (left; simpl; omega) 
  | [H : WF_Matrix _ _ ?M |- context[?M ?a ?b] ] => 
      rewrite (H a b) by (right; simpl; omega) 
  end;
  autorewrite with C_db; auto.


Lemma divmod_eq : forall x y n z, 
  fst (Nat.divmod x y n z) = (n + fst (Nat.divmod x y 0 z))%nat.
Proof.
  induction x.
  + intros. simpl. omega.
  + intros. simpl. 
    destruct z.
    rewrite IHx.
    rewrite IHx with (n:=1%nat).
    omega.
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
  - intros. simpl. rewrite IHx. omega.
Qed.

Lemma divmod_0 : forall x, fst (Nat.divmod x 0 0 0) = x. 
Proof. intros. rewrite divmod_0q0. omega. Qed.

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
                      autounfold with M_db;
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
Ltac reduce_matrices := match goal with 
                        | [ |- context[?M]] => reduce_aux M
                        end;
                        repeat match goal with 
                               | [ |- context[?c :: _ ]] => cbv [c]; clear c
                               end.


Ltac solve_matrix := assoc_least;
                     repeat reduce_matrix; try crunch_matrix;
                     Csimpl; try clra.
       
(* Tactics to show implicit arguments *)
Definition kron' := @kron.      
Lemma kron_shadow : @kron = kron'. reflexivity. Qed.

Definition Mmult' := @Mmult.
Lemma Mmult_shadow : @Mmult = Mmult'. reflexivity. Qed.

Ltac show_dimensions := try rewrite kron_shadow in *; 
                        try rewrite Mmult_shadow in *.
Ltac hide_dimensions := try rewrite <- kron_shadow in *; 
                        try rewrite <- Mmult_shadow in *.