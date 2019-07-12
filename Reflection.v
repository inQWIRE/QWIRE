Require Import Matrix.
Require Import Quantum.
Close Scope C_scope.
Open Scope nat_scope.

Require Import Monad. 

(* TODO:
   RMatrix_simpl is a transformation over RMatrix's (below).
   The idea is to normalize this structure to a semi-canonical form
*)

(* The cateogry FdHilb is...
   - monoidal
   - has finite biproducts
   - is dagger compact

   - × is composition
   - 1 is the identity morphism
   - ⊗ is the monoid
   - + is the addition
   - 0 is the unit of addition

  Category:
    (A × B) × C = A × (B × C)             (associativity) 
    1 × A = A                             (left identity)
    A × 1 = A                             (right identity)

  Monoidal:
    (A ⊗ B) ⊗ C = A ⊗ (B ⊗ C)             (associativity)
    1_1 ⊗ A = A                           (left identity)
    A ⊗ 1_1 = A                           (right identity)
    (A ⊗ B) × C 

    (A ⊗ C) × (B ⊗ D) = (A × B) ⊗ (C × D) (functorial)
      i.e. If A : Matrix m n   and B : Matrix n o
              C : Matrix m' n' and D : Matrix n' o'

    If C : Matrix 1 n, then C × (B ⊗ D) = B ⊗ (C × D).
    If A : Matrix n 1, then A × (B ⊗ D) = (A × B) ⊗ D.
    If B : Matrix n 1, then (A ⊗ C) × B = (A × B) ⊗ C.
    If D : Matrix 1 n, then (A ⊗ C) × D = A ⊗ (C × D).

  Symmetry:
    SWAP × (A ⊗ B) = B ⊗ A

  Dagger:
    (A × B)† = B† × A†
    (A ⊗ B)† = A† ⊗ B†
    

  Finite biproducts:
    (A .+ B)† = A† 

  Scalar:


*)


(* Composition and addition form a non-commutative field

  (associativity)
  (A + B) + C = A + (B + C)
  (A × B) × C = A × (B × C)

  (symmetry)
  A + B = B + A

  (identity)
  Zero + A = A
  A + Zero = A
  I × B = B
  B × I = B
  A × Zero = Zero
  Zero × A = Zero

  (additive inverse)
  A + -1.*A = Zero

  (multiplicative inverse)
  B <> Zero -> B × B† = I
  B <> Zero -> B† × B = I

  (distributativity)
  A × (B + C) = A × B + A × C
  (A + B) × C = A × C + B × C
*)

(* TODO: classify the rest of the rules *)

(* Produce something of the form
   
*)



Inductive RMatrix :=
  | MPrim {m n : nat} : Matrix m n -> RMatrix
  | MZero (m n : nat) : RMatrix
  | MI    (n : nat)   : RMatrix
  | MPlus             : RMatrix -> RMatrix -> RMatrix
  | MMult             : RMatrix -> nat (* intermediate dimension *) -> RMatrix -> RMatrix
  | MKron             : nat -> nat -> RMatrix -> nat -> nat -> RMatrix -> RMatrix
  | MScale            : C -> RMatrix -> RMatrix
  | MAdjoint          : RMatrix -> RMatrix
.



Inductive RMatrix_Type : RMatrix -> nat -> nat -> Set :=
  | tPrim m n (A : Matrix m n) : RMatrix_Type (MPrim A) m n
  | tZero m n : RMatrix_Type (MZero m n) m n
  | tI n : RMatrix_Type (MI n) n n
  | tScale c M m n : RMatrix_Type M m n -> RMatrix_Type (MScale c M) m n
  | tPlus M N m n : RMatrix_Type M m n -> RMatrix_Type N m n -> RMatrix_Type (MPlus M N) m n
  | tMult M1 M2 m n o : RMatrix_Type M1 m n -> RMatrix_Type M2 n o ->
                        RMatrix_Type (MMult M1 n M2) m o
  | tKron M1 M2 m1 n1 m2 n2 : RMatrix_Type M1 m1 n1 ->
                              RMatrix_Type M2 m2 n2 ->
                              RMatrix_Type (MKron m1 n1 M1 m2 n2 M2) (m1*m2) (n1*n2)
  | tAdjoint M m n : RMatrix_Type M m n -> RMatrix_Type (MAdjoint M) n m
.
Hint Constructors RMatrix_Type : rtype.


Fixpoint RMatrix_size (M : RMatrix) : option (nat*nat) :=
  match M with
  | @MPrim m n _ => Some (m,n)
  | MZero m n => Some (m,n)
  | MI n => Some (n,n)
  | MScale _ M => RMatrix_size M
  | MPlus M1 M2 => do x1 ← RMatrix_size M1;
                   do x2 ← RMatrix_size M2;
                   if ((fst x1 =? fst x2) && (snd x1 =? snd x2))
                   then Some x1
                   else None
  | MMult M1 o M2 => 
                   do x ← RMatrix_size M1;
                   do y ← RMatrix_size M2;
                   if (snd x =? o) && (o =? fst y)
                   then Some (fst x,snd y)
                   else None
  | MKron m1 n1 M1 m2 n2 M2 =>
                   do x1 ← RMatrix_size M1;
                   do x2 ← RMatrix_size M2;
                   if (fst x1 =? m1) && (snd x1 =? n1) && (fst x2 =? m2) && (snd x2 =? n2)
                   then Some (m1*m2,n1*n2)
                   else None
  | MAdjoint M => do x ← RMatrix_size M;
                   Some (snd x, fst x)
  end.


Ltac inversion_option :=
  match goal with
  | [H : None = Some _ |- _] => inversion H
  | [H : Some _ = None |- _] => inversion H
  | [H : Some _ = Some _ |- _] => inversion H; clear H
  end.


Ltac reduce_beq :=
  repeat match goal with
  | [ H : (_ =? _) = true |- _] => repeat rewrite H; apply beq_nat_true in H; subst
  | [ H : (_ =? _) = false |- _] => repeat rewrite H; apply beq_nat_false in H
  | _ => rewrite Nat.eqb_refl in *
  | [ H : context[?a =? ?b] |- _] => 
      let H' := fresh "H" in
      destruct (a =? b) eqn:H'; simpl in *; try inversion_option
  end.


Lemma RMatrix_size_Type : forall M m n, RMatrix_size M = Some (m,n) -> RMatrix_Type M m n.
Proof.
  induction M; intros m' n' H;
     try destruct IHM as [m [n IHM]];
     try destruct IHM1 as [m1 [n1 IHM1]];
     try destruct IHM2 as [m2 [n2 IHM2]].
  - (* Prim *)
    simpl in *. inversion H. constructor.
  - (* Zero *)
    simpl in *. inversion H. constructor.
  - (* I *)
    simpl in *. inversion H. constructor.  
  - (* Plus *)
    simpl in *. 
    destruct (RMatrix_size M1) as [[m1 n1] | ]; [ | inversion H].
    destruct (RMatrix_size M2) as [[m2 n2] | ]; [ | inversion H].
    simpl in *.
    reduce_beq.
    constructor; [apply IHM1 | apply IHM2]; auto.
  - (* Mult *)
    simpl in *. 
    destruct (RMatrix_size M1) as [[m1 n1] | ]; [ | inversion H].
    destruct (RMatrix_size M2) as [[m2 n2] | ]; [ | inversion H].
    simpl in *.
    reduce_beq.
    constructor; [apply IHM1 | apply IHM2]; auto.
  - (* Kron *)
    simpl in *. 
    destruct (RMatrix_size M1) as [[m1' n1'] | ]; [ | inversion H].
    destruct (RMatrix_size M2) as [[m2' n2'] | ]; [ | inversion H].
    simpl in *.
    reduce_beq.
    constructor; [apply IHM1 | apply IHM2]; reflexivity.
  - (* Scale *)
    simpl in *. constructor. apply IHM; auto.
  - (* Adjoint *)
    simpl in *. 
    destruct (RMatrix_size M) as [[m n] | ]; [ | inversion H].
    simpl in *.
    inversion H; subst.
    constructor; apply IHM; reflexivity.
Qed.

Lemma RMatrix_Type_size : forall M m n, RMatrix_Type M m n -> RMatrix_size M = Some (m,n).
Proof. 
  induction 1; 
    try (auto; fail);
    try (simpl; 
         try rewrite IHRMatrix_Type1;
         try rewrite IHRMatrix_Type2;
         try rewrite IHRMatrix_Type;
         simpl; repeat rewrite Nat.eqb_refl; reflexivity).
Qed.

Fixpoint reflect_RMatrix' (M : RMatrix) (m n : nat) :
         Matrix m n :=
  match M with 
  | MPrim A                 => A
  | MZero _ _               => Zero
  | MI n'                   => I n'
  | MPlus M1 M2             => reflect_RMatrix' M1 m n .+ reflect_RMatrix' M2 m n
  | MMult M1 o M2           => reflect_RMatrix' M1 m o ×  reflect_RMatrix' M2 o n
  | MKron m1 n1 M1 m2 n2 M2 => reflect_RMatrix' M1 m1 n1 ⊗  reflect_RMatrix' M2 m2 n2
  | MScale c M'             => c .* reflect_RMatrix' M' m n
  | MAdjoint M'             => (reflect_RMatrix' M' n m)†
  end.


Definition reflect_RMatrix (M : RMatrix) m n :
           RMatrix_size M = Some (m,n) ->
           Matrix m n :=
  fun _ => reflect_RMatrix' M m n.

(* Definition RMatrixEq (m n : nat) (M1 M2 : RMatrix) := reflect_RMatrix' M1 m n == reflect_RMatrix' M2 m n. *)
Notation "M1 ==_{ m , n } M2" := (reflect_RMatrix' M1 m n == reflect_RMatrix' M2 m n)
    (at level 20).

Lemma RMatrixEq_refl : forall m n (M : RMatrix), M ==_{m,n} M.
Proof.
  intros m n M.
  reflexivity.
Qed.
Lemma RMatrixEq_sym : forall m n (M1 M2 : RMatrix), M1 ==_{m,n} M2 -> M2 ==_{m,n} M1.
Proof.
  intros. symmetry. auto.
Qed.
Lemma RMatrixEq_trans : forall m n (M1 M2 M3 : RMatrix),
    M1 ==_{m,n} M2 -> M2 ==_{m,n} M3 -> M1 ==_{m,n} M3.
Proof.
  intros. transitivity (reflect_RMatrix' M2 m n); auto.
Qed.
  
(*
Add Parametric Relation (m n : nat) : (RMatrix) (RMatrixEq m n)
  reflexivity proved by (RMatrixEq_refl m n)
  symmetry proved by (RMatrixEq_sym m n)
  transitivity proved by (RMatrixEq_trans m n)
  as RMatrix_rel.
*)

(*******************************************************************)
(* Rules for solving the symmetric monoidal structure of unitaries *)
(*******************************************************************)


Lemma kron_dist_l : forall m n o p q
      (A : Matrix m n) (B : Matrix n o) (C : Matrix p q),
  (A × B) ⊗ C == (A ⊗ C) × (B ⊗ I q).
Proof.
  intros.
  rewrite kron_mixed_product.
  rewrite Mmult_1_r.
  reflexivity.
Qed.
Lemma kron_dist_r : forall m n o p q
      (A : Matrix m n) (B : Matrix o p) (C : Matrix p q),
  A ⊗ (B × C) == (A ⊗ B) × (I n ⊗ C).

Proof.
  intros.
  rewrite kron_mixed_product.
  rewrite Mmult_1_r.
  reflexivity.
Qed.

(* flatten to:
   sum_over (mult_over (kron_over Prim))
  where
*)

(* Interpret as: A_Scale .* (A_Mat)^A_Adjoint *)
Inductive Prim :=
  | IPrim m n (padl : nat) (padr : nat) : Matrix m n -> Prim
  | APrim m n (padl : nat) (padr : nat) : Matrix m n -> Prim
.

Definition A_dimx (P : Prim) : nat :=
  match P with
  | @IPrim m n padl padr _ => padl * m * padr
  | @APrim m n padl padr _ => padl * n * padr
  end.
Definition A_dimy (P : Prim) : nat :=
  match P with
  | @IPrim m n padl padr _ => padl * n * padr
  | @APrim m n padl padr _ => padl * m * padr
  end.

Inductive KronList :=
  | LUnit (n : nat) : C (* scaling factor *) -> KronList
  | LKron : Prim -> (* dimensions of 2nd kronlist *) nat -> nat -> KronList -> KronList
.
Inductive MultList :=
  | LI (n : nat) : C (* scaling factor*) -> MultList
  | LMult : KronList -> nat (* inner dimension *) -> MultList -> MultList
.
Inductive SumList :=
  | LZero (m n : nat) : SumList
  | LPlus : MultList -> SumList -> SumList
.
(* Robert: Should be Sum -> Kron -> Mult -> Prim *)


Definition RPad m n padl padr (R : RMatrix) : RMatrix :=
    MKron padl padl (MI padl) (m*padr) (n*padr) (MKron m n R padr padr (MI padr)).
Definition reflect_Prim (P : Prim) : RMatrix :=
  match P with
  | IPrim m n padl padr A => RPad m n padl padr (MPrim A)
  | APrim m n padl padr A => MAdjoint (RPad m n padl padr (MPrim A))
  end.
Fixpoint reflect_KronList (K : KronList) : RMatrix :=
  match K with
  | LUnit n c => MScale c (MI n)
  | LKron x mK nK K' => MKron (A_dimx x) (A_dimy x) (reflect_Prim x) mK nK (reflect_KronList K')
  end.
Fixpoint reflect_MultList (M : MultList) : RMatrix :=
  match M with
  | LI n c => MScale c (MI n)
  | LMult K o M' => MMult (reflect_KronList K) o (reflect_MultList M')
  end.
Fixpoint reflect_SumList (S : SumList) : RMatrix :=
  match S with
  | LZero m n => MZero m n
  | LPlus M S' => MPlus (reflect_MultList M) (reflect_SumList S')
  end.
Coercion reflect_Prim : Prim >-> RMatrix.
Coercion reflect_KronList : KronList >-> RMatrix.
Coercion reflect_MultList : MultList >-> RMatrix.
Coercion reflect_SumList : SumList >-> RMatrix.


(* Prim *)


Definition KPrim {m n} (A : Matrix m n) : KronList :=
  LKron (IPrim m n 1 1 A) 1 1 (LUnit 1 C1).
Definition MultPrim {m n} (A : Matrix m n) : MultList :=
  LMult (KPrim A) n (LI n C1).
Definition SPrim  {m n} (A : Matrix m n) : SumList :=
  LPlus (MultPrim A) (LZero m n).


Lemma SPrim_correct : forall {m n} (A : Matrix m n),
    reflect_SumList (SPrim A) ==_{m,n} MPrim A.
Proof.
  intros m n A.
  simpl.
  rewrite Mplus_0_r.

  rewrite (Mscale_1_l (I n)).

  rewrite Mmult_1_r.
  assert (H : I 1 ⊗ (A ⊗ I 1) ⊗ (1%R .* I 1) == A ⊗ I 1 ⊗ I 1).
  {
    rewrite Mscale_1_l.
    autorewrite with M_db.
    reflexivity.
  } 
  
    repeat rewrite <- mult_assoc in *.
    repeat rewrite mult_1_r in *.
    repeat rewrite mult_1_l in *.
    rewrite H.
  clear H.

    set (H' := kron_assoc A (I 1) (I 1)).

    repeat rewrite <- mult_assoc in *.
    repeat rewrite mult_1_l in *.
    repeat rewrite mult_1_r in *.
  rewrite H'; clear H'.

  assert (H : A ⊗ (I 1 ⊗ I 1) == A ⊗ I 1).
  { Search (I _ ⊗ I _).
    rewrite id_kron.
    rewrite mult_1_l.
    reflexivity.
  }
  rewrite (kron_1_r A) in H.

    repeat rewrite <- mult_assoc in *.
    repeat rewrite mult_1_l in *.
    repeat rewrite mult_1_r in *.
  rewrite H.
  reflexivity.
Qed.

  
(* Scale *)

Fixpoint KScale (c : C) (K : KronList) : KronList :=
  match K with
  | LUnit n c' => LUnit n (c*c')
  | LKron P mK nK  K' => (* c .* (P ⊗ K) == P ⊗ c.*K *)
    LKron P mK nK (KScale c K')
  end.
Fixpoint MultScale (c : C) (M : MultList) : MultList :=
  match M with
  | LI n c'  => LI n (c*c')
  | LMult K o  M' => (* c .* (K × M') == K × c .* M' *)
    LMult K o (MultScale c M')
  end.
Fixpoint SScale (c : C) (S : SumList) : SumList :=
  match S with
  | LZero m n  => LZero m n
  | LPlus M S' => (* c .* (M + S') == (c.*M) + (c.*S') *)
    LPlus (MultScale c M) (SScale c S')
  end.

Lemma KScale_Type : forall K c m n,
    RMatrix_Type (reflect_KronList K) m n ->
    RMatrix_Type (reflect_KronList (KScale c K)) m n.
Proof.
  induction K as [n0 c' | P mK nK K']; intros c m n H.
  - simpl in *.
    dependent destruction H.
    dependent destruction H.
    constructor.
    constructor.
  - simpl in *.
    dependent destruction H.
    constructor; auto.
Qed.
Hint Resolve KScale_Type : rtype.

Lemma MultScale_Type : forall M c m n,
    RMatrix_Type (reflect_MultList M) m n ->
    RMatrix_Type (reflect_MultList (MultScale c M)) m n.
Proof.
  induction M; intros c0 m0 n0 HTyped.
  * simpl in *. inversion HTyped; subst. constructor; auto.
  * simpl in *. inversion HTyped; subst.
    econstructor; eauto.
Qed.
Hint Resolve MultScale_Type : rtype.

Lemma SScale_Type : forall S c m n,
    RMatrix_Type (reflect_SumList S) m n ->
    RMatrix_Type (reflect_SumList (SScale c S)) m n.
  induction S; intros c0 m0 n0 HTyped;
    simpl; inversion HTyped; subst; auto with rtype.
Qed.
Hint Resolve SScale_Type : rtype.

Lemma KScaleEq : forall (K : KronList) c m n,
    RMatrix_Type (reflect_KronList K) m n ->
    reflect_KronList (KScale c K) ==_{m,n} MScale c (reflect_KronList K).
Proof.
  induction K as [n0 c0 | M' m1 n1 K']; intros c m n H.
  * simpl; repeat dependent destruction H.
    rewrite Mscale_assoc.
    reflexivity.
  * simpl. dependent destruction H. 
    rewrite IHK'; auto.
    rewrite <- Mscale_kron_dist_r.
    reflexivity.
Qed.
Lemma MultScaleEq : forall (M : MultList) c m n,
    RMatrix_Type (reflect_MultList M) m n ->
    reflect_MultList (MultScale c M) ==_{m,n} MScale c (reflect_MultList M).
Proof.
  induction M; intros c0 m0 n0 H0;
    dependent destruction H0; simpl.
  * autorewrite with M_db. solve_matrix.
  * rewrite IHM; auto.
    simpl.
    rewrite <- Mscale_mult_dist_r.
    reflexivity.
Qed.
Lemma SScaleEq : forall (S : SumList) c m n,
    RMatrix_Type (reflect_SumList S) m n ->
    reflect_SumList (SScale c S) ==_{m,n} MScale c (reflect_SumList S).
Proof.
  induction S; intros c0 m0 n0 H0.
  * simpl.  solve_matrix.
  * inversion H0; subst.
    simpl.
    rewrite MultScaleEq; auto.
    rewrite IHS; auto.
    simpl.
    rewrite Mscale_plus_dist_r.
    reflexivity.
Qed.

(**********)
(** Plus **)
(**********)

Fixpoint SPlus (S1 : SumList) (S2 : SumList) :=
  match  S1 with
  | LZero m n => S2
  | LPlus M S1' => LPlus M (SPlus S1' S2)
  end.
Lemma SPlus_Type : forall S1 S2 m n,
    RMatrix_Type (reflect_SumList S1) m n ->
    RMatrix_Type (reflect_SumList S2) m n ->
    RMatrix_Type (reflect_SumList (SPlus S1 S2)) m n.
Proof.
  induction S1; intros S2 m0 n0 H1 H2.
  * simpl in *. auto with rtype.
  * simpl in *. inversion H1; subst.
    auto with rtype.
Qed.
Hint Resolve SPlus_Type : rtype.

Lemma SPlusEq : forall S1 S2 m n,
    RMatrix_Type (reflect_SumList S1) m n ->
    RMatrix_Type (reflect_SumList S2) m n ->
             reflect_SumList (SPlus S1 S2) 
    ==_{m,n} MPlus (reflect_SumList S1) (reflect_SumList S2).
Proof.
  induction S1 as [m1 n1 | M1 S1'];
    intros S2 m n H1 H2.
  * simpl in *.
    inversion H1; subst.
    repeat erewrite RMatrix_Type_size; eauto.
    rewrite Mplus_0_l.
    reflexivity.
  * simpl in *.
    inversion H1; subst.
    repeat erewrite RMatrix_Type_size; eauto.
    repeat (simpl; rewrite Nat.eqb_refl).
    rewrite IHS1'; auto.
    repeat erewrite RMatrix_Type_size; eauto.
    repeat (simpl; rewrite Nat.eqb_refl).
    rewrite Mplus_assoc.
    reflexivity.
Qed.


(**********)
(** Mult **)
(**********)

Fixpoint MLMult (M1 M2 : MultList) : MultList :=
  match M1 with
  | LI n c => (* (c .* I) × M2 = c .* M2 *) 
              MultScale c M2
  | LMult K1 o M1' => LMult K1 o (MLMult M1' M2)
  end.
Fixpoint MSMult (M : MultList) (S : SumList) (m n : nat) : SumList :=
  match S with
  | LZero _ _ => LZero m n
  | LPlus M' S' => LPlus (MLMult M M') (MSMult M S' m n)
  end.
Fixpoint SMult (S1 S2 : SumList) (m n : nat) : SumList :=
  match S1 with
  | LZero _ _    => LZero m n
  | LPlus M1 S1' => (* (M1 + S1') × S2 = (M1 × S2) + (S1' × S2) *)
    SPlus (MSMult M1 S2 m n) (SMult S1' S2 m n)
  end.

Lemma MLMult_Type : forall M1 M2 m n o,
    RMatrix_Type (reflect_MultList M1) m n ->
    RMatrix_Type (reflect_MultList M2) n o ->
    RMatrix_Type (reflect_MultList (MLMult M1 M2)) m o.
Proof.
  induction M1 as [n1 c1 | K1 o1 M1']; intros M2 m n o H1 H2.
  - repeat dependent destruction H1.
    simpl.
    auto with rtype.
  - repeat dependent destruction H1.
    simpl.
    constructor; auto.
    eapply IHM1'; eauto.
Qed.
Hint Resolve MLMult_Type : rtype.
Lemma MSMult_Type : forall M1 S2 m n o,
    RMatrix_Type (reflect_MultList M1) m n ->
    RMatrix_Type (reflect_SumList S2) n o ->
    RMatrix_Type (reflect_SumList (MSMult M1 S2 m o)) m o.
Proof.
  induction S2 as [m2 n2 | M2 S2']; intros m n o H1 H2;
    repeat dependent destruction H2.
  - constructor.
  - simpl. constructor; auto.
    * eapply MLMult_Type; eauto.
    * eapply IHS2'; eauto.
Qed.
Hint Resolve MSMult_Type : rtype.
Lemma SMult_Type : forall S1 S2 m n o,
    RMatrix_Type (reflect_SumList S1) m n ->
    RMatrix_Type (reflect_SumList S2) n o ->
    RMatrix_Type (reflect_SumList (SMult S1 S2 m o)) m o.
Proof.
  induction S1 as [m1 n1 | M1 S1']; intros S2 m n o H1 H2;
    repeat dependent destruction H1;
    simpl;
    eauto with rtype.
Qed.
Hint Resolve SMult_Type : rtype.


Lemma MLMultEq : forall M1 M2 m n o,
    RMatrix_Type (reflect_MultList M1) m n ->
    RMatrix_Type (reflect_MultList M2) n o -> 
             reflect_MultList (MLMult M1 M2) 
    ==_{m,o} MMult (reflect_MultList M1) n (reflect_MultList M2).
Proof.
  induction M1 as [n1 c1 | K1 M1']; intros M2 m n o HM1 HM2.
  * simpl in *.
    dependent destruction HM1. dependent destruction HM1.
    rewrite MultScaleEq; auto.
    simpl.
    rewrite Mscale_mult_dist_l.
    rewrite <- Mscale_mult_dist_r.
    rewrite Mmult_1_l.
    reflexivity.
  * dependent destruction HM1. 
    simpl in *.
    rewrite IHM1; eauto.
    rewrite Mmult_assoc.
    reflexivity.
Qed.
Lemma MSMultEq : forall M1 S2 m n o,
    RMatrix_Type (reflect_MultList M1) m n ->
    RMatrix_Type (reflect_SumList S2) n o ->
             reflect_SumList (MSMult M1 S2 m o) 
    ==_{m,o} MMult (reflect_MultList M1) n (reflect_SumList S2).
Proof.
  induction S2 as [m2 n2 | M2 S2']; intros m n o H1 H2;
    repeat dependent destruction H2; simpl.
  * rewrite  Mmult_0_r.
    reflexivity.
  * rewrite IHS2'; eauto.
    rewrite MLMultEq; eauto.
    simpl.
    rewrite Mmult_plus_dist_l.
    reflexivity.
Qed.
Lemma SMultEq : forall S1 S2 m n o,
    RMatrix_Type (reflect_SumList S1) m n ->
    RMatrix_Type (reflect_SumList S2) n o ->
             reflect_SumList (SMult S1 S2 m o) 
    ==_{m,o} MMult (reflect_SumList S1) n (reflect_SumList S2).
Proof.
  induction S1 as [m1 n1 | M1 S1']; intros S2 m n o H1 H2;
    dependent destruction H1; simpl.
  * rewrite Mmult_0_l. reflexivity.
  * rewrite SPlusEq; eauto with rtype. 
    simpl.
    rewrite MSMultEq; eauto.
    simpl.
    rewrite Mmult_plus_dist_r.
    rewrite IHS1'; eauto.
    reflexivity.
Qed.

(*********)
(** Pad **)
(*********)

Print KronList. Print Prim.
Fixpoint PPad (lpad rpad : nat) (P : Prim) : Prim :=
  match P with
  | IPrim m n lpad' rpad' A => IPrim m n (lpad*lpad') (rpad'*rpad) A
  | APrim m n lpad' rpad' A => APrim m n (lpad*lpad') (rpad'*rpad) A
  end.
Lemma PPad_Type : forall X lpad rpad m n,
    RMatrix_Type (reflect_Prim X) m n ->
    RMatrix_Type (reflect_Prim (PPad lpad rpad X)) (lpad*m*rpad) (lpad*n*rpad).
Proof.
Admitted.
Hint Resolve PPad_Type.

Lemma PPadEq : forall X lpad rpad m n,
    RMatrix_Type (reflect_Prim X) m n ->
    reflect_Prim (PPad lpad rpad X)
 ==_{lpad*m*rpad,lpad*m*rpad} RPad m n lpad rpad (reflect_Prim X).
Admitted.

Search (_ ⊗ (_ ⊗ _)).
Fixpoint KPad (lpad rpad : nat) (K : KronList) : KronList :=
  match K with
  | LUnit n c => (* I lpad ⊗ I n ⊗ I rpad == I (lpad*n*rpad) *)
                 LUnit (lpad*n*rpad) c
  | LKron X mK' nK' K' => (* I lpad ⊗ (X ⊗ K') ⊗ I rpad
                          == (I lpad ⊗ X) ⊗ (K' ⊗ I rpad)
                          *)
    LKron (PPad lpad 1 X) (mK'*rpad) (nK'*rpad) (KPad 1 rpad K')
  end.
Lemma KPad_Type : forall K lpad rpad mM nM,
    RMatrix_Type (reflect_KronList K) mM nM ->
    RMatrix_Type (reflect_KronList (KPad lpad rpad K)) (lpad*mM*rpad) (lpad*nM*rpad).
Proof.
Admitted.
Hint Resolve KPad_Type.
Lemma KPadEq : forall K lpad rpad m n,
    RMatrix_Type (reflect_KronList K) m n ->
    reflect_KronList (KPad lpad rpad K)
 ==_{lpad*m*rpad,lpad*n*rpad} RPad m n lpad rpad (reflect_KronList K).
Admitted.

Search (_ ⊗ (_ × _)).
(* Produce I n ⊗ M  where M : Matrix mM nM *)
Fixpoint MPad (lpad rpad : nat) (M : MultList) : MultList :=
  match M with
  | LI n' c    => (* I lpad ⊗ I n' ⊗ I rpad == I (lpad*n'*rpad) *)
    LI (lpad*n'*rpad) c
  | LMult K oM M' => (* I lpad ⊗ (K × M') ⊗ I rpad
                     == ((I lpad ⊗ K) × (I lpad ⊗ M')) ⊗ I rpad
                     == (I lpad ⊗ K ⊗ I rpad) × (I lpad ⊗ M' ⊗ I rpad)
                     *)
    LMult (KPad lpad rpad K) (lpad*oM*rpad) (MPad lpad rpad M')
  end.
Lemma MPad_Type : forall M lpad rpad m n,
    RMatrix_Type (reflect_MultList M) m n ->
    RMatrix_Type (reflect_MultList (MPad lpad rpad M)) (lpad*m*rpad) (lpad*n*rpad).
Proof.
(*  intros M n mM nM H.
  dependent induction M; simpl; dependent destruction H;
    auto with rtype.
  * dependent destruction H; auto with rtype.*)
Admitted.
Hint Resolve MPad_Type : rtype.
Lemma MPadEq : forall M lpad rpad m n,
    RMatrix_Type (reflect_MultList M) m n ->
    reflect_MultList (MPad lpad rpad M)
 ==_{lpad*m*rpad,lpad*n*rpad} RPad m n lpad rpad (reflect_MultList M).
Proof.
  intros M n mM nM H.
Admitted.

Print SumList. Search (_ ⊗ (_ .+ _)).
Fixpoint SPad (lpad rpad : nat) (S : SumList) : SumList :=
  match S with
  | LZero m n  => LZero (lpad*m*rpad) (lpad*m*rpad)
  | LPlus M S' => LPlus (MPad lpad rpad M) (SPad lpad rpad S')
  end.
Lemma SPad_Type : forall S lpad rpad m n,
    RMatrix_Type (reflect_SumList S) m n ->
    RMatrix_Type (reflect_SumList (SPad lpad rpad S)) (lpad*m*rpad) (lpad*n*rpad).
Proof.
(*  intros M n mM nM H.
  dependent induction M; simpl; dependent destruction H;
    auto with rtype.
  * dependent destruction H; auto with rtype.*)
Admitted.
Hint Resolve SPad_Type : rtype.
Lemma SPadEq : forall S lpad rpad m n,
    RMatrix_Type (reflect_SumList S) m n ->
    reflect_SumList (SPad lpad rpad S)
 ==_{lpad*m*rpad,lpad*n*rpad} RPad m n lpad rpad (reflect_SumList S).
Proof.
Admitted.



(**********)
(** Kron **)
(**********)

Fixpoint KKron (K1 : KronList) (mK2 nK2 : nat) (K2 : KronList) : KronList :=
  match K1 with
  | LUnit n c => KPad n 1 (KScale c K2)
  | LKron X1 mK1 nK1 K1' => (* (X ⊗ K1') ⊗ K2 = X ⊗ (K1' ⊗ K2) *)
    LKron X1 (mK1*mK2) (nK1*nK2) (KKron K1' mK2 nK2 K2)
  end.

Lemma KKron_Type : forall K1 K2 m1 n1 m2 n2,
    RMatrix_Type (reflect_KronList K1) m1 n1 ->
    RMatrix_Type (reflect_KronList K2) m2 n2 ->
    RMatrix_Type (reflect_KronList (KKron K1 m2 n2 K2)) (m1*m2) (n1*n2).
Proof.
  induction K1 as [c1 | X1 mK1 nK1 K1']; intros K2 m1 n1 m2 n2 H1 H2;
    repeat dependent destruction H1.
  * simpl.
Admitted.
Hint Resolve KKron_Type : rtype.
Lemma KKronEq : forall K1 K2 m1 n1 m2 n2,
    RMatrix_Type (reflect_KronList K1) m1 n1 ->
    RMatrix_Type (reflect_KronList K2) m2 n2 ->
    reflect_KronList (KKron K1 m2 n2 K2)
 ==_{m1*m2,n1*n2} MKron m1 n1 (reflect_KronList K1) m2 n2 (reflect_KronList K2).
Proof.
  induction K1 as [c1 | X1 mK1 nK1 K1']; intros K2 m1 n1 m2 n2 H1 H2;
    repeat dependent destruction H1; simpl;
    repeat rewrite <- Nat.mul_assoc.
  * assert (H2' : RMatrix_Type (KScale c K2) m2 n2) by auto with rtype.
    set (H := KPadEq (KScale c K2) c1 1 m2 n2 H2').
    simpl in H; repeat rewrite mult_1_r in H; rewrite H; clear H.
    rewrite Mscale_kron_dist_l.
    rewrite <- Mscale_kron_dist_r.
    apply kron_compat; [reflexivity | ].
    set (H := KScaleEq K2 c m2 n2 H2); simpl in H; rewrite <- H; clear H.
    set (H := kron_1_r (reflect_RMatrix' (KScale c K2) m2 n2));
      repeat rewrite mult_1_r in H;
      apply H.
  * rewrite IHK1'; auto.
    simpl.
    repeat rewrite Nat.mul_assoc.
    rewrite kron_assoc.
    reflexivity.
Qed.

Require Import Omega.
(* K1 is an m1×n1 matrix, for some m1 *)
(* M2 is an m2×n2 matrix *)
(* K1 ⊗ M2 *)
Definition KMKron (n1 : nat) (K1 : KronList) (m2 n2 : nat) (M2 : MultList) : MultList :=
  match M2 with
  | LI n c => (* K1 ⊗ (c .* I n) = c .* (K1 ⊗ I n) = (K1 × I n) × (c .* I (n1*n)) *)
    LMult (KPad 1 n K1) (n1*n) (LI (n1*n) c)
  | LMult K2 o2 M2' => (* K1 ⊗ (K2 × M2') = (K1 ⊗ K2) × (I n1 ⊗ M2') *)
    LMult (KKron K1 m2 o2 K2) (n1*o2) (MPad n1 1 M2')
  end.
Lemma KMKron_Type : forall m1 n1 (K1 : KronList) m2 n2 (M2 : MultList),
    RMatrix_Type K1 m1 n1 ->
    RMatrix_Type M2 m2 n2 ->
    RMatrix_Type (KMKron n1 K1 m2 n2 M2) (m1*m2) (n1*n2).
Proof.
  dependent destruction M2; intros H1 H2;
    repeat dependent destruction H2;
    simpl; auto with rtype.
  * constructor; auto with rtype.
    replace (m1 * n) with (1 * m1 * n) by (rewrite mult_1_l; reflexivity).
    replace (n1 * n) with (1 * n1 * n) by (rewrite mult_1_l; reflexivity).
    apply KPad_Type; auto.
  * constructor; auto with rtype.
    replace (n1 * n) with (n1 * n * 1) by (rewrite mult_1_r; reflexivity).
    replace (n1 * o) with (n1 * o * 1) by (rewrite mult_1_r; reflexivity).
    apply MPad_Type; auto.
Qed.
Hint Resolve KMKron_Type : rtype.
Lemma KMKronEq : forall m1 n1 (K1 : KronList) m2 n2 (M2 : MultList),
    RMatrix_Type K1 m1 n1 ->
    RMatrix_Type M2 m2 n2 ->
    KMKron n1 K1 m2 n2 M2 ==_{m1*m2,n1*n2} MKron m1 n1 K1 m2 n2 M2.
Proof.
  dependent destruction M2; intros H1 H2;
    repeat dependent destruction H2;
    simpl.
  - replace (m1 * n) with (1 * m1 * n) by (rewrite mult_1_l; reflexivity).
    replace (n1 * n) with (1 * n1 * n) by (rewrite mult_1_l; reflexivity).
    rewrite KPadEq; auto; simpl.
    set (H := kron_1_l (reflect_RMatrix' K1 m1 n1 ⊗ I n));
      simpl in H;
      repeat rewrite Nat.add_0_r in *;
      rewrite H; clear H.

    rewrite <- id_kron.
    rewrite <- Mscale_kron_dist_r.
    rewrite kron_mixed_product.
    rewrite Mmult_1_r.
    rewrite Mmult_1_l.
    reflexivity.
  - rewrite KKronEq; auto.
    replace (n1 * n) with (n1 * n * 1) by (rewrite mult_1_r; reflexivity).
    replace (n1 * o) with (n1 * o * 1) by (rewrite mult_1_r; reflexivity).
    rewrite MPadEq; auto.
    simpl.
    set (H := @kron_1_r _ _ (reflect_RMatrix' M2 n o));
      repeat rewrite mult_1_r in *;
      rewrite H;
      clear H.
    rewrite kron_dist_r.
    reflexivity.
Qed.



Definition MLKron (m1 n1 : nat) (M1 : MultList) (m2 n2 : nat) (M2 : MultList) : MultList :=
  match M1 with
  | LI n c => (* I n ⊗ M1 *)
    MultScale c (MPad n 1 M2)
  | LMult K1 o1 M1' => (* (K1 × M1') ⊗ M2 = (K1 ⊗ M2) × (M1' ⊗ I n2) *)
    MLMult (KMKron o1 K1 m2 n2 M2) (MPad 1 n2 M1')
  end.
Lemma MLKron_Type : forall m1 n1 (M1 : MultList) m2 n2 (M2 : MultList),
    RMatrix_Type M1 m1 n1 ->
    RMatrix_Type M2 m2 n2 ->
    RMatrix_Type (MLKron m1 n1 M1 m2 n2 M2) (m1*m2) (n1*n2).
Proof.
  destruct M1 as [n c | K' o' M']; intros m2 n2 M2 H1 H2;
    repeat dependent destruction H1;
    simpl; eauto with rtype.
  - apply MultScale_Type.
    replace (n*m2) with (n*m2*1) by (rewrite mult_1_r; reflexivity).
    replace (n*n2) with (n*n2*1) by (rewrite mult_1_r; reflexivity).
    auto with rtype.
  - eapply MLMult_Type; eauto with rtype.
    replace (o'*n2) with (1*o'*n2) by (rewrite mult_1_l; reflexivity).
    replace (o*n2) with (1*o*n2) by (rewrite mult_1_l; reflexivity).
    auto with rtype.
Qed.
Hint Resolve MLKron_Type : rtype.
Lemma MLKronEq : forall m1 n1 (M1 : MultList) m2 n2 (M2 : MultList),
    RMatrix_Type M1 m1 n1 ->
    RMatrix_Type M2 m2 n2 ->
    MLKron m1 n1 M1 m2 n2 M2 ==_{m1*m2,n1*n2} MKron m1 n1 M1 m2 n2 M2.
Proof.
  destruct M1 as [n c | K' o' M']; intros m2 n2 M2 H1 H2;
    repeat dependent destruction H1;
    simpl.
  -
    replace (n*m2) with (n*m2*1) by (rewrite mult_1_r; reflexivity).
    replace (n*n2) with (n*n2*1) by (rewrite mult_1_r; reflexivity).
    rewrite MultScaleEq; auto with rtype.
    simpl.
    rewrite MPadEq; [ | auto].
    simpl.
    set (H := kron_1_r (reflect_RMatrix' M2 m2 n2));
      repeat rewrite mult_1_r in *;
      rewrite H; clear H.
    rewrite Mscale_kron_dist_l.
    reflexivity.
  - 
    rewrite MLMultEq; eauto with rtype;
      replace (o*n2) with (1*o*n2) by (rewrite mult_1_l; reflexivity);
      replace (o'*n2) with (1*o'*n2) by (rewrite mult_1_l; reflexivity);
      auto with rtype.

    simpl.
    repeat rewrite Nat.add_0_r in *.
    rewrite KMKronEq; auto.
    simpl.
      replace (o*n2) with (1*o*n2) by (rewrite mult_1_l; reflexivity);
      replace (o'*n2) with (1*o'*n2) by (rewrite mult_1_l; reflexivity).

    rewrite MPadEq; auto.
    simpl.
    set (H := kron_1_l (reflect_RMatrix' M' o' o ⊗ I n2));
      repeat rewrite mult_1_l in *;
      repeat rewrite Nat.add_0_r in *;
      rewrite H; clear H.
    rewrite kron_mixed_product.
    rewrite Mmult_1_r.
    reflexivity.
Qed.


Fixpoint MSKron (m1 n1 : nat) (M1 : MultList) (m2 n2 : nat) (S2 : SumList) : SumList :=
  match S2 with
  | LZero _ _    => (* M1 ⊗ Zero = Zero *) LZero (m1*m2) (n1*n2)
  | LPlus M2 S2' => (* M1 ⊗ (M2 + S2') = (M1⊗M2) + (M1 ⊗ S2') *)
    LPlus (MLKron m1 n1 M1 m2 n2 M2) (MSKron m1 n1 M1 m2 n2 S2')
  end.
Lemma MSKron_Type : forall m1 n1 (M1 : MultList) m2 n2 (S2 : SumList),
    RMatrix_Type M1 m1 n1 ->
    RMatrix_Type S2 m2 n2 ->
    RMatrix_Type (MSKron m1 n1 M1 m2 n2 S2) (m1*m2) (n1*n2).
Proof.
  dependent induction S2; intros H1 H2;
    repeat dependent destruction H2; simpl;
    auto with rtype.
Qed.
Hint Resolve MSKron_Type : rtype.
Lemma MSKronEq : forall m1 n1 (M1 : MultList) m2 n2 (S2 : SumList),
    RMatrix_Type M1 m1 n1 ->
    RMatrix_Type S2 m2 n2 ->
    MSKron m1 n1 M1 m2 n2 S2 ==_{m1*m2,n1*n2} MKron m1 n1 M1 m2 n2 S2.
Proof.
  dependent induction S2; intros H1 H2;
    repeat dependent destruction H2; simpl.
  - rewrite kron_0_r.
    reflexivity.
  - rewrite MLKronEq; auto with rtype; simpl.
    rewrite IHS2; auto with rtype; simpl.
    rewrite <- kron_plus_distr_l.
    reflexivity.
Qed.
  
Fixpoint SLKron (m1 n1 : nat) (S1 : SumList) (m2 n2 : nat) (S2 : SumList) : SumList :=
  match S1 with
  | LZero _ _    => (* Zero ⊗ S2 = Zero *) LZero (m1*m2) (n1*n2)
  | LPlus M1 S1' => (* (M1 + S1') ⊗ S2 = (M1 ⊗ S2) + (M2 ⊗ S2) *)
    SPlus (MSKron m1 n1 M1 m2 n2 S2) (SLKron m1 n1 S1' m2 n2 S2)
  end.
Lemma SLKron_Type : forall m1 n1 (S1 : SumList) m2 n2 (S2 : SumList),
    RMatrix_Type S1 m1 n1 ->
    RMatrix_Type S2 m2 n2 ->
    RMatrix_Type (SLKron m1 n1 S1 m2 n2 S2) (m1*m2) (n1*n2).
Proof.
  dependent induction S1; intros m2 n2 S2 H1 H2;
    repeat dependent destruction H1; simpl;
    auto with rtype.
Qed.
Hint Resolve SLKron_Type : rtype.
Lemma SLKronEq : forall m1 n1 (S1 : SumList) m2 n2 (S2 : SumList),
    RMatrix_Type S1 m1 n1 ->
    RMatrix_Type S2 m2 n2 ->
    SLKron m1 n1 S1 m2 n2 S2 ==_{m1*m2,n1*n2} MKron m1 n1 S1 m2 n2 S2.
Proof.
  dependent induction S1; intros m2 n2 S2 H1 H2;
    repeat dependent destruction H1; simpl.
  - autorewrite with M_db.
    rewrite kron_0_l.
    reflexivity.
  - rewrite SPlusEq; auto with rtype; simpl.
    rewrite IHS1; auto with rtype; simpl.
    rewrite MSKronEq; auto with rtype; simpl.
    rewrite kron_plus_distr_r.
    reflexivity.
Qed.

Definition PAdjoint (X : Prim) : Prim :=
  match X with
  | IPrim m n padl padr A => APrim m n padl padr A
  | APrim m n padl padr A => IPrim m n padl padr A
  end.
Lemma PAdjoint_Type : forall (X : Prim) m n,
    RMatrix_Type X m n ->
    RMatrix_Type (PAdjoint X) n m.
Proof.
  destruct X as [mA nA padl padr A | mA nA padl padr A]; intros m' n' H;
    dependent destruction H; simpl; auto with rtype.
  * constructor.
    unfold RPad.
    eauto with rtype.
Qed.
Hint Resolve PAdjoint_Type : rtype.
Lemma PAdjointEq : forall (X : Prim) m n,
    RMatrix_Type X m n ->
    PAdjoint X ==_{n,m} MAdjoint X.
Proof.
  destruct X as [mA nA padl padr A | mA nA padl padr A]; intros m' n' H;
    dependent destruction H; simpl.
  - reflexivity.
  - dependent destruction H.
    autorewrite with M_db.
    reflexivity.
Qed.

Lemma PAdjoint_dimx : forall X,
    A_dimx (PAdjoint X) = A_dimy X.
Proof.
  destruct X; auto.
Qed.
Lemma PAdjoint_dimy : forall X,
    A_dimy (PAdjoint X) = A_dimx X.
Proof.
  destruct X; auto.
Qed.


Fixpoint KAdjoint (K : KronList) : KronList :=
  match K with
  | LUnit n c => LUnit n (c^*)
  | LKron X mK' nK' K' => (* (X ⊗ K')† = X† ⊗ K† *)
    LKron (PAdjoint X) nK' mK' (KAdjoint K')
  end.

Lemma KAdjoint_Type : forall (K : KronList) m n,
    RMatrix_Type K m n ->
    RMatrix_Type (KAdjoint K) n m.
Proof.
  induction K as [c | X mK' nK' K']; intros m n H; 
    dependent destruction H; simpl.
  - dependent destruction H. auto with rtype.
  - rewrite PAdjoint_dimx, PAdjoint_dimy.
    auto with rtype.
Qed.
Hint Resolve KAdjoint_Type : rtype.
Lemma KAdjointEq : forall (K : KronList) m n,
    RMatrix_Type K m n ->
    KAdjoint K ==_{n,m} MAdjoint K.
Proof.
  induction K as [c | X mK' nK' K']; intros m n H; 
    dependent destruction H; simpl.
  - dependent destruction H. 
    autorewrite with M_db.
    rewrite Mscale_adj.
    autorewrite with M_db.
    reflexivity.
  - rewrite PAdjoint_dimx, PAdjoint_dimy.
    rewrite PAdjointEq; auto with rtype; simpl.
    rewrite IHK'; auto with rtype; simpl.
    rewrite kron_adjoint.
    reflexivity.
Qed.



Fixpoint MLAdjoint (m n : nat) (M : MultList) : MultList :=
  match M with
  | LI n' c     => LI n' (c^*)
  | LMult K o M' => (* (K × M')† = M'† × K† *)
    MLMult (MLAdjoint o n M') (LMult (KAdjoint K) m (LI m C1))
  end.
Lemma MLAdjoint_Type : forall (M : MultList) m n,
    RMatrix_Type M m n ->
    RMatrix_Type (MLAdjoint m n M) n m.
Proof.
  induction M as [nM c | K' o' M']; intros m n H;
    dependent destruction H; simpl.
  - dependent destruction H. auto with rtype.
  - eapply MLMult_Type; simpl; eauto with rtype.
Qed.
Hint Resolve MLAdjoint_Type : rtype.
Lemma MLAdjointEq : forall (M : MultList) m n,
    RMatrix_Type M m n ->
    MLAdjoint m n M ==_{n,m} MAdjoint M.
Proof.
  induction M as [nM c | K' o' M']; intros m n H;
    dependent destruction H; simpl.
  - dependent destruction H.
    rewrite Mscale_adj.
    rewrite id_adjoint_eq.
    reflexivity.
  - rewrite MLMultEq; auto with rtype; simpl.
    2:{ constructor; auto with rtype. }
    rewrite KAdjointEq; auto with rtype; simpl.
    rewrite IHM'; auto with rtype; simpl.
    autorewrite with M_db.
    rewrite Mscale_1_l.
    rewrite Mmult_1_r.
    reflexivity.
Qed.



Fixpoint SAdjoint (m n : nat) (S : SumList) : SumList :=
  match S with
  | LZero _ _ => LZero n m
  | LPlus M S' => (* (M + S')† = M† + S'† *)
    LPlus (MLAdjoint m n M) (SAdjoint m n S')
  end.
Lemma SAdjoint_Type : forall (S : SumList) m n,
    RMatrix_Type S m n ->
    RMatrix_Type (SAdjoint m n S) n m.
Proof.
  induction S as [mS nS | M' S']; intros m n H;
    dependent destruction H; simpl; auto with rtype.
Qed.
Hint Resolve SAdjoint_Type : rtype.
Lemma SAdjointEq : forall (S : SumList) m n,
    RMatrix_Type S m n ->
    SAdjoint m n S ==_{n,m} MAdjoint S.
Proof.
  induction S as [mS nS | M' S']; intros m n H;
    dependent destruction H; simpl.
  - autorewrite with M_db.
    rewrite zero_adjoint_eq.
    reflexivity.
  - rewrite MLAdjointEq; auto.
    rewrite IHS'; auto.
    autorewrite with M_db.
    reflexivity.
Qed.





Fixpoint reify_SumList (M : RMatrix) (m n : nat): SumList :=
  match M with
  | MPrim A     => SPrim A
  | MZero _ _   => LZero m n
  | MI n        => LPlus (LI n C1) (LZero n n)
  | MPlus M1 M2 => SPlus (reify_SumList M1 m n) (reify_SumList M2 m n)
  | MMult M1 o M2 => SMult (reify_SumList M1 m o) (reify_SumList M2 o n) m n
  | MKron m1 n1 M1 m2 n2 M2 => SLKron m1 n1 (reify_SumList M1 m1 n1) m2 n2 (reify_SumList M2 m2 n2)
  | MScale c M' => SScale c (reify_SumList M' m n)
  | MAdjoint M' => SAdjoint n m (reify_SumList M' n m)
  end.

Lemma reify_SumList_Type : forall M m n,
      RMatrix_Type M m n ->
      RMatrix_Type (reify_SumList M m n) m n.
Proof.
  induction M; intros m' n' H;
    dependent destruction H; simpl; eauto with rtype.
  - repeat constructor.
    replace m with ((1*m*1)*1) at 4 by omega.
    replace n with ((1*n*1)*1) at 4 by omega.
    constructor; auto with rtype.
    unfold RPad.
    repeat rewrite <- mult_assoc.
    auto with rtype.
Qed.
Hint Resolve reify_SumList_Type : rtype.

Lemma reify_SumListEq : forall (M : RMatrix) m n,
      RMatrix_Type M m n ->
      reflect_RMatrix' M m n == reflect_RMatrix' (reify_SumList M m n) m n.
Proof.
  induction M; intros m' n' H;
    dependent destruction H; simpl;
    try (rewrite IHM1; auto with rtype);
    try (rewrite IHM2; auto with rtype);
    try (rewrite IHM; auto with rtype).
  - rewrite Mplus_0_r.
    rewrite (Mscale_1_l (I n)).
    rewrite Mmult_1_r.

    assert (H : I 1 ⊗ (m0 ⊗ I 1) ⊗ (C1 .* I 1) == I 1 ⊗ (m0 ⊗ I 1) ⊗ I 1).
    { rewrite Mscale_1_l. reflexivity. }

    repeat rewrite Nat.add_0_r in *;
    repeat rewrite Nat.mul_1_r in *;
    repeat rewrite Nat.add_0_l in *;
    repeat rewrite Nat.mul_1_l in *.
    rewrite H; clear H.

    set (H := kron_1_r (I 1 ⊗ (m0 ⊗ I 1)));
    repeat rewrite Nat.add_0_r in *;
    repeat rewrite Nat.mul_1_r in *;
    repeat rewrite Nat.add_0_l in *;
    repeat rewrite Nat.mul_1_l in *.
    rewrite H; clear H.

    set (H := kron_1_l (m0 ⊗ I 1));
    repeat rewrite Nat.add_0_r in *;
    repeat rewrite Nat.mul_1_r in *;
    repeat rewrite Nat.add_0_l in *;
    repeat rewrite Nat.mul_1_l in *.
    rewrite H; clear H.

    set (H := kron_1_r m0);
    repeat rewrite Nat.add_0_r in *;
    repeat rewrite Nat.mul_1_r in *;
    repeat rewrite Nat.add_0_l in *;
    repeat rewrite Nat.mul_1_l in *.
    rewrite H; clear H.

    reflexivity.
  - reflexivity.
  - rewrite Mplus_0_r.
    rewrite Mscale_1_l.
    reflexivity.
  - rewrite SPlusEq; auto with rtype; simpl.
    reflexivity.
  - rewrite SMultEq; auto with rtype; simpl.
    reflexivity.
  - rewrite SLKronEq; auto with rtype; simpl.
    reflexivity.
  - rewrite SScaleEq; auto with rtype; simpl.
    reflexivity.
  - rewrite SAdjointEq; auto with rtype; simpl.
    reflexivity.
Qed.





(*
Ltac rewrite_RMatrix_size :=
  repeat rewrite RMatrix_size_simpl in *;
  match goal with
  | [H : RMatrix_Type ?M ?m ?n |- _] =>
    simpl in *;
    erewrite (RMatrix_Type_size _ _ _ H) in *
  | [H : RMatrix_size ?M = Some (?m, ?n) |- _] =>
    rewrite H in *
  end.
Ltac rewrite_RMatrix_size' M :=
  let m := fresh "m" in
  let n := fresh "n" in
  let H := fresh "H" in
  destruct (RMatrix_size M) as [[m n]|] eqn:H; [ | inversion H].
*)




(** Tactics **)



(*

Ltac simplify_RMatrix_size := 
              repeat (simpl in *; (  rewrite_RMatrix_size 
                          || inversion_option 
                          || rewrite Nat.eqb_refl in *
                          ));
              try reflexivity.
*)


(* If e is a matrix expression, produce an RMatrix expression *)
Ltac reify_matrix e := 
  match e with
  | reflect_RMatrix' ?M ?m ?n => constr:(M)
  | reflect_RMatrix ?M ?m ?n _ => constr:(M)
  | @Zero ?m ?n => constr:(MZero m n)
  | I ?n => constr:(MI n)
  | ?A .+ ?B => let M := reify_matrix A in
                let N := reify_matrix B in
                constr:(MPlus M N) 
  | ?A × ?B =>  let M := reify_matrix A in
                let N := reify_matrix B in
                match type of A with
                | Matrix _ ?o => constr:(MMult M o N) 
                end
  | ?A ⊗ ?B => let M := reify_matrix A in
               let N := reify_matrix B in
               match type of A with
               | Matrix ?m1 ?n1 =>
                 match type of B with
                 | Matrix ?m2 ?n2 => constr:(MKron m1 n1 M m2 n2 N)
                 end
               end
  | ?c .* ?A => let M := reify_matrix A in
                constr:(MScale c M)
  | ?A †     => let M := reify_matrix A in
                constr:(MAdjoint M)
  | _ => constr:(MPrim e)
  end.

Ltac rewrite_with_eqb := 
  repeat (simpl; rewrite Nat.eqb_refl); simpl; try reflexivity.
Ltac rewrite_with_eqb_in H := 
  repeat (simpl in H; rewrite Nat.eqb_refl in H); simpl in H.

Ltac reify_matrices :=
  match goal with
  | [ |- ?A == ?B ] => let M := (reify_matrix A) in
                       let N := (reify_matrix B) in
                       match type of A with
                       | Matrix ?m ?n => 
                         transitivity (reflect_RMatrix' M m n);
                            [ rewrite_with_eqb | ]
                       end;
                       match type of B with
                       | Matrix ?m' ?n' => 
                         transitivity (reflect_RMatrix' N m' n'); 
                           [ | rewrite_with_eqb ]
                       end
  end.





Lemma reify_SumListEq' : forall M m n m' n',
      RMatrix_Type M m n ->
      m = m' -> n = n' ->
      @mat_equiv m' n' (reflect_RMatrix' M m n) (reflect_RMatrix' (reify_SumList M m n) m n).
Proof.
  intros M m n m' n' H Hm Hn. subst.
  apply reify_SumListEq; easy.
Qed.


Lemma RMatrix_eq : forall (M1 M2 : RMatrix) m1 n1 m2 n2 m n,
    m = m1 -> m1 = m2 ->
    n = n1 -> n1 = n2 ->
    reify_SumList M1 m1 n1 = reify_SumList M2 m2 n2 ->
    @mat_equiv m n (reflect_RMatrix' M1 m1 n1) (reflect_RMatrix' M2 m2 n2).
Admitted.

Ltac RMatrix_reflection :=
  reify_matrices;
    try (apply RMatrix_eq; simpl; unify_pows_two; try lia; Csimpl; reflexivity).
(*
  rewrite reify_SumListEq; [rewrite_with_eqb | apply RMatrix_size_Type; rewrite_with_eqb].
*)




Lemma foo : ∣0⟩ ⊗ ∣0⟩ == (⟨1∣×∣1⟩).
Proof. 
  reify_matrices. simpl. 
Abort.


Let foo : forall m n o (A : Matrix m n),
      A × (@Zero n o) == Zero.
Proof. 
  intros m n o A.
  RMatrix_reflection.
Qed.

Let foo' : forall m n o p (A : Matrix m n) (B : Matrix n o),
      A × (B × @Zero o p) == Zero.
Proof.
  intros.
  reify_matrices.
  apply RMatrix_eq; try trivial.
Qed.

Definition pad {m} n (A : Square (2^m)) : Square (2^n) := (A ⊗ I (2^ (n - m))).

Lemma pad_nothing_test : forall m A, mat_equiv (@pad m m A) A.
Proof.
  intros.
  unfold pad.
  RMatrix_reflection.
Qed.

(*
(** Symmetry **)


(** Sorted sum lists **)

Print SumList.
(* RemoveMS M S S' holds if S' ≡ M+S *)
Inductive RemoveMS (M : MultList) : SumList -> SumList -> Set :=
| MHere S : RemoveMS M (LPlus M S) S
| MLater M' S' S'' : RemoveMS M S' S'' -> RemoveMS M (LPlus M' S') (LPlus M' S'')
.
Inductive SPermutation : SumList -> SumList -> Set :=
| PZero m n : SPermutation (LZero m n) (LZero m n)
| PCons M S1' S2 S2' : 
          RemoveMS M S2 S2' ->
          SPermutation S1' S2' ->
          SPermutation (LPlus M S1') S2
.
Ltac proveMInS :=
  match goal with
  | [ |- MInS ?M (LPlus ?M ?S) ] => apply (MHere M S)
  | [ |- MInS ?M (LPlus ?M' ?S') ] => apply (MLater M M' S'); proveMInS
  end.




(* Reorder a SumList according to the following metric. There may be different clauses with the same metric. *)
Print KronList.
Fixpoint KronListMetric (K : KronList) : nat :=
  match K with
  | LUnit _ _ => 1
  | LKron _ _ _ K' => 1 + 2*(KronListMetric K')
  end.
Fixpoint MultListMetric (M : MultList) : nat :=
  match M with
  | LI _ _ => 1
  | LMult K o M' => KronListMetric K + 2*(MultListMetric M')
  end.

Print SumList.
Fixpoint insertWithMetric (M : MultList) (S : SumList) : list (list MultList) :=
  match S with
  | LZero m n   => [[M]]
  | LPlus M' S' => if MultListMetric M <? MultListMetric M'
                   then M :: 

LPlus (MultListMetric M) (LPlus (MultListMetric M') S')
                   else LPlus (MultListMetric


(* Instead of RMatrixEq, the reified sumlists should be permutations of each other *)


Print SumList.
Definition MultListEquiv (M1 M2 : MultList) := (M1 = M2).


Inductive RemoveFromSumList (M : MultList) : SumList -> SumList -> Prop :=
| remove_here : forall S, RemoveFromSumList M (LPlus M S) S
| remove_there : forall S S' M', RemoveFromSumList M S S' ->
                                 RemoveFromSumList M (LPlus M' S) (LPlus M' S')
.
Inductive SumListEquiv : SumList -> SumList -> Prop :=
| LZero_equiv : forall m n, SumListEquiv (LZero m n) (LZero m n)
| LPlus_equiv : forall M S1' S2 S2',
    RemoveFromSumList M S2 S2' ->
    SumListEquiv S1' S2' ->
    SumListEquiv (LPlus M S1') S2.


Lemma RMatrix_equiv : forall (M1 M2 : RMatrix) m1 n1 m2 n2 m n,
    m = m1 -> m1 = m2 ->
    n = n1 -> n1 = n2 ->
    SumListEquiv (reify_SumList M1 m1 n1) (reify_SumList M2 m2 n2) ->
    @mat_equiv m n (reflect_RMatrix' M1 m1 n1) (reflect_RMatrix' M2 m2 n2).
Admitted.

    
(* If M occurs in S, produce a pair (S',pf) where S' is a sumlist and pf is a
proof that RemoveFromSumList M S S' holds. *)
Ltac remove_from_SumList M S :=
  match S with
  | LPlus M   ?S' => idtac "Got: " S;
                     constr:((S', remove_here S'))
  | LPlus ?M' ?S' => idtac "Removing " M';
                     match remove_from_SumList M S' with
                     | ((?S'', ?pf)) => constr:((LPlus M' S'', remove_there S' S'' M'))
                     end
  end.

(* If S1 is equivalent to S2, produce a proof of SumListEquiv S1 S2 *)
Ltac SumList_permutation S1 S2 :=
  match S1 with
  | LZero ?m ?n  => match S2 with
                    | LZero m n => constr:(LZero_equiv m n)
                    end
  | LPlus ?M ?S1' => match remove_from_SumList M S2 with
                    | ((?S2', ?pfRm)) => 
                      idtac "Removed " M " from " S2 " got " S2'; 
                      let pfS2' := SumList_permutation S1' S2' in
                       constr:(LPlus_equiv M S1' S2 S2' pfRm pfS2')
                    end
  end.

  


(* Currently does not work on symmetry! *)
Lemma symm_test : forall {m n} (A B : Matrix  m n), A .+ B == B .+ A.
Proof.
  intros.
  intros.
  reify_matrices.
  apply RMatrix_equiv; auto. 
    simpl. repeat unfold MultPrim, SPrim, KPrim.

  match goal with
  | [ |- SumListEquiv ?S1 ?S2 ] => 
    match SumList_permutation S1 S2 with
    | ((_,?pf)) => apply pf
    end
  end.
 

  match SumList_permutation 
  RMatrix_reflection.
    SumList_permutation (MPlus (MPrim A) (MPrim B)) (MPlus (MPrim B) (MPrim A)).
Abort.
*)