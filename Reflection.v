Require Import Matrix.
Require Import Quantum.
Close Scope C_scope.
Open Scope nat_scope.

Require Import Monad. 

(* TODO:
   RMatrix_simpl is a transformation over RMatrix's (below).
   The idea is to normalize this structure to a semi-canonical form
*)

Search "⊗" "×".
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
Search "×" "⊗".


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
  | [ H : (_ =? _) = true |- _] => apply beq_nat_true in H; subst
  | [ H : (_ =? _) = false |- _] => apply beq_nat_false in H
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

Print RMatrix.
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
  | IPrim m n : Matrix m n -> Prim
  | APrim m n : Matrix m n -> Prim
.
Definition A_dimx (P : Prim) : nat :=
  match P with
  | @IPrim m n _ => m
  | @APrim m n _ => n
  end.
Definition A_dimy (P : Prim) : nat :=
  match P with
  | @IPrim m n _ => n
  | @APrim m n _ => m
  end.

Definition reflect_Prim (P : Prim) : RMatrix :=
  match P with
  | IPrim m n A => MPrim A
  | APrim m n A => MAdjoint (MPrim A)
  end.

Inductive KronList :=
  | LUnit : C (* scaling factor *) -> KronList
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

Fixpoint reflect_KronList (K : KronList) : RMatrix :=
  match K with
  | LUnit c => MScale c (MI 1)
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
  LKron (IPrim m n A) 1 1 (LUnit C1).
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


  set (H' := Mscale_1_l (I 1)).
  transitivity (A ⊗ I 1).
  * solve_matrix.
  * 
  set (H'' := kron_1_r A).
  repeat rewrite Nat.mul_1_r in H''.
  apply H''.
Qed.

  
(* Scale *)

Fixpoint KScale (c : C) (K : KronList) : KronList :=
  match K with
  | LUnit c'   => LUnit (c*c')
  | LKron P mK nK  K' => (* c .* (P ⊗ K) == P ⊗ c.*K *)
    LKron P mK nK (KScale c K')
  end.
Search ".+" ".*".
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
  induction K as [c' | P mK nK K']; intros c m n H.
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
  induction K as [c0 | M' m1 n1 K']; intros c m n H.
  * simpl; repeat dependent destruction H.
    Search (_ * _ .* _).
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

Print RMatrix.
Print SumList.
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
    Search (_ .+ _ .+ _).
    rewrite Mplus_assoc.
    reflexivity.
Qed.

Print RMatrix.
Print SumList.
Search ".+" "×".

(**********)
(** Mult **)
(**********)

Print MultList.
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
    Search (I _ × _).
    Search (_ .* (_ × _)).
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
  * Search "×" Zero.
    rewrite  Mmult_0_r.
    reflexivity.
  * rewrite IHS2'; eauto.
    rewrite MLMultEq; eauto.
    simpl.
    Search (_ × (_ .+ _)).
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



(**********)
(** Kron **)
(**********)

Print RMatrix.
Print KronList.
About kron_assoc.
Fixpoint KKron (K1 : KronList) (mK2 nK2 : nat) (K2 : KronList) : KronList :=
  match K1 with
  | LUnit c => KScale c K2
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
    repeat rewrite Nat.add_0_r.
    apply KScale_Type; auto.
  * simpl. Print MKron.
    Print RMatrix_Type.
    replace (A_dimx X1 * mK1 * m2) with (A_dimx X1 * (mK1 * m2)).
    2:{ rewrite Nat.mul_assoc. reflexivity. }
    replace (A_dimy X1 * nK1 * n2) with (A_dimy X1 * (nK1 * n2)).
    2:{ rewrite Nat.mul_assoc. reflexivity. }
    constructor; auto.
Qed.
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
  * rewrite KScaleEq; [ | repeat rewrite Nat.add_0_r; auto].
    simpl. repeat rewrite Nat.add_0_r.
    repeat rewrite Nat.mul_assoc.
    remember (reflect_RMatrix' (reflect_KronList K2) m2 n2) as M.

    set (H := Mscale_kron_dist_l c1 (I 1) M).
    repeat rewrite Nat.mul_1_l in *.
    rewrite H.
    clear H.
    
    set (H := kron_1_l M).
    repeat rewrite Nat.mul_1_l in *.
    rewrite H.
    clear H.

    reflexivity.
  * rewrite IHK1'; auto.
    simpl.
    repeat rewrite Nat.mul_assoc.
    rewrite kron_assoc.
    reflexivity.
Qed.


(* Produce I n ⊗ M  where M : Matrix mM nM *)
Fixpoint MPad_l (n : nat) (mM nM : nat) (M : MultList) : MultList :=
  match M with
  | LI n' c    => (* I n ⊗ I n' = I (n*n') *)
    LI (n*n') c
  | LMult K oM M' => (* I n ⊗ (K × M') = (I n ⊗ K) × (I n ⊗ M') *)
                  LMult (LKron (IPrim n n (I n)) mM oM K) (n*oM) (MPad_l n oM nM M')
  end.
Lemma MPad_l_Type : forall M n mM nM,
    RMatrix_Type (reflect_MultList M) mM nM ->
    RMatrix_Type (reflect_MultList (MPad_l n mM nM M)) (n*mM) (n*nM).
Proof. Print MultList.
  induction M as [n0 c | K o M']; intros n mM nM H. 
  * simpl; repeat dependent destruction H.
    constructor. constructor.
  * dependent destruction H.
    simpl.
    constructor.
    + constructor; auto. constructor.
    + apply IHM'; auto.
Qed.
Hint Resolve MPad_l_Type : rtype.
Lemma MPad_l_Eq : forall M n mM nM,
    RMatrix_Type (reflect_MultList M) mM nM ->
    reflect_MultList (MPad_l n mM nM M)
 ==_{n*mM,n*nM} MKron n n (reflect_MultList (LI n C1)) mM nM (reflect_MultList M).
Proof.
  induction M as [n0 c | K o M']; intros n mM nM H.
  * simpl; repeat dependent destruction H.
    rewrite Mscale_1_l.
    Search I "⊗".
    rewrite <- id_kron.
    Search (_ .* (_ ⊗ _)).
    rewrite <- Mscale_kron_dist_r.
    reflexivity.
  * simpl. dependent destruction H.
    rewrite IHM'; auto.
    simpl.
    rewrite Mscale_1_l.
    Search (_ ⊗ (_ × _)).
    rewrite kron_dist_r.
    reflexivity.
Qed.

(* Produce K ⊗ (I n) *)
Fixpoint KPad_r (K : KronList) (n : nat) : KronList :=
  match K with
  | LUnit c    => LKron (IPrim n n (I n)) 1 1 (LUnit c)
  | LKron X mK nK K' => LKron X (mK*n) (nK*n) (KPad_r K' n)
  end.

Lemma KPad_r_Type : forall (K : KronList) mK nK n,
    RMatrix_Type K mK nK ->
    RMatrix_Type (KPad_r K n) (mK*n) (nK*n).
Proof. 
  induction K as [c | X mK' nK' K']; intros mK nK n H.
  * repeat dependent destruction H.
    simpl.
    replace (n+0) with (n * 1). 2:{ rewrite Nat.add_0_r. rewrite Nat.mul_1_r. reflexivity. }
    constructor; repeat constructor. 
  * dependent destruction H.
    simpl.
    repeat rewrite <- Nat.mul_assoc.
    constructor; auto.
Qed.
Hint Resolve KPad_r_Type : rtype.
Lemma KPad_r_Eq : forall (K : KronList) mK nK n,
    RMatrix_Type K mK nK -> 
    KPad_r K n
 ==_{mK*n,nK*n} MKron mK nK K n n (LI n C1).
Proof.
Print KronList.
  induction K as [c | X mK' nK' K']; intros mK nK n H.
  * simpl; repeat dependent destruction H.
    rewrite Mscale_1_l.
    Search I "⊗". About id_kron.
    set (H := @id_kron 1 n).
    simpl in H.
    rewrite Nat.add_0_r in H.
    set (A := I 1) in *.
    set (B := I n) in *.

    set (H' := Mscale_kron_dist_r c B A).
    rewrite Nat.mul_1_l in *.
    rewrite Nat.mul_1_r in *.
    rewrite H'.
    clear H'.

    set (H' := Mscale_kron_dist_l c A B).
    rewrite Nat.mul_1_l in *.
    rewrite H'.
    clear H'.



    unfold A, B.


    set (H'' := @id_kron n 1).
    rewrite Nat.mul_1_r in *.
    rewrite H''.

    set (H''' := @id_kron 1 n).
    rewrite Nat.mul_1_l in *.
    rewrite H'''.


    reflexivity.    
  * simpl. dependent destruction H.
    specialize (IHK' _ _ n H0).
    simpl in IHK'.
    rewrite Mscale_1_l.
    rewrite kron_assoc.
    Search (_ ⊗ _ == _ ⊗ _).
    repeat rewrite <- mult_assoc.
    rewrite IHK'.
    rewrite Mscale_1_l.
    reflexivity.
Qed.


(* Produce M ⊗ (I n) *)
Fixpoint MPad_r (M : MultList) (n : nat): MultList :=
  match M with
  | LI n' c' => (* I n ⊗ I n' = I (n*n') *)
    LI (n'*n) c'
  | LMult K o M' => (* (K × M') ⊗ I = (K ⊗ I) × (M' ⊗ I) *)
                    LMult (KPad_r K n) (o*n) (MPad_r M' n)
  end.
Lemma MPad_r_Type : forall (M : MultList) mM nM n,
    RMatrix_Type M mM nM ->
    RMatrix_Type (MPad_r M n) (mM * n) (nM * n).
Proof.
    Print MultList.
  induction M as [m c | K' o' M']; intros mM nM n H;
    dependent destruction H.
  - dependent destruction H.
    simpl.
    constructor. constructor.
  - simpl.
    constructor; auto.
    apply KPad_r_Type; auto.
Qed.
Hint Resolve MPad_r_Type : rtype.
Lemma MPad_r_Eq : forall (M : MultList) mM nM n,
    RMatrix_Type M mM nM ->
    MPad_r M n ==_{mM*n,nM*n} MKron mM nM M n n (MI n).
Proof.
  induction M as [m c | K' o' M']; intros mM nM n H;
    dependent destruction H.
  - dependent destruction H.
    simpl.
    Search I kron.
    rewrite <- id_kron.
    rewrite Mscale_kron_dist_l.
    reflexivity.
  - simpl in *.
    rewrite IHM'; auto.
    rewrite KPad_r_Eq; auto.
    rewrite kron_dist_l.
    simpl.
    Search (C1 .* _).
    rewrite Mscale_1_l.
    reflexivity.
Qed.


(* K1 is an m1×n1 matrix, for some m1 *)
(* M2 is an m2×n2 matrix *)
(* K1 ⊗ M2 *)
Definition KMKron (n1 : nat) (K1 : KronList) (m2 n2 : nat) (M2 : MultList) : MultList :=
  match M2 with
  | LI n c => (* K1 ⊗ (c .* I n) = c .* (K1 ⊗ I n) = (K1 × I n) × (c .* I (n1*n)) *)
    LMult (KPad_r K1 n) (n1*n) (LI (n1*n) c)
  | LMult K2 o2 M2' => (* K1 ⊗ (K2 × M2') = (K1 ⊗ K2) × (I n1 ⊗ M2') *)
    LMult (KKron K1 m2 o2 K2) (n1*o2) (MPad_l n1 o2 n2 M2')
  end.
Lemma KMKron_Type : forall m1 n1 (K1 : KronList) m2 n2 (M2 : MultList),
    RMatrix_Type K1 m1 n1 ->
    RMatrix_Type M2 m2 n2 ->
    RMatrix_Type (KMKron n1 K1 m2 n2 M2) (m1*m2) (n1*n2).
Proof.
  dependent destruction M2; intros H1 H2;
    repeat dependent destruction H2;
    simpl; auto with rtype.
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
  - rewrite KPad_r_Eq; auto; simpl.
    rewrite Mscale_1_l.
    Search (_ ⊗ _ × _).
    Search I "⊗".
    rewrite <- id_kron.
    rewrite <- Mscale_kron_dist_r.
    rewrite kron_mixed_product.
    Search (_ × I _).
    rewrite Mmult_1_r.
    rewrite Mmult_1_l.
    reflexivity.
  - rewrite KKronEq; auto.
    rewrite MPad_l_Eq; auto.
    simpl.
    rewrite Mscale_1_l.
    autorewrite with M_db.
    reflexivity.
Qed.

(*    autorewrite with M_db.*)



Definition MLKron (m1 n1 : nat) (M1 : MultList) (m2 n2 : nat) (M2 : MultList) : MultList :=
  match M1 with
  | LI n c => (* I n ⊗ M1 *)
    MultScale c (MPad_l n m2 n2 M2)
  | LMult K1 o1 M1' => (* (K1 × M1') ⊗ M2 = (K1 ⊗ M2) × (M1' ⊗ I n2) *)
    MLMult (KMKron o1 K1 m2 n2 M2) (MPad_r M1' n2)
  end.
Lemma MLKron_Type : forall m1 n1 (M1 : MultList) m2 n2 (M2 : MultList),
    RMatrix_Type M1 m1 n1 ->
    RMatrix_Type M2 m2 n2 ->
    RMatrix_Type (MLKron m1 n1 M1 m2 n2 M2) (m1*m2) (n1*n2).
Proof.
Print MultList.
  destruct M1 as [n c | K' o' M']; intros m2 n2 M2 H1 H2;
    repeat dependent destruction H1;
    simpl; eauto with rtype.
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
  - rewrite MultScaleEq; auto with rtype.
    simpl.
    rewrite MPad_l_Eq; [ | auto].
    simpl.
    Search (C1 .* _).
    rewrite Mscale_1_l.
    Search (_ .* (_ ⊗ _)).
    rewrite Mscale_kron_dist_l.
    reflexivity.
  - rewrite MLMultEq; auto with rtype.
    simpl.
    rewrite KMKronEq; auto.
    simpl.
    rewrite MPad_r_Eq; auto.
    simpl.
    autorewrite with M_db.
    reflexivity.
Qed.

Print SumList.
Search ".+" "⊗".

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
  - Search (_ ⊗ Zero).
    rewrite kron_0_r.
    reflexivity.
  - rewrite MLKronEq; auto with rtype; simpl.
    rewrite IHS2; auto with rtype; simpl.
    Search "⊗" ".+".
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
    Search (Zero ⊗ _).
    rewrite kron_0_l.
    reflexivity.
  - rewrite SPlusEq; auto with rtype; simpl.
    rewrite IHS1; auto with rtype; simpl.
    rewrite MSKronEq; auto with rtype; simpl.
    rewrite kron_plus_distr_r.
    reflexivity.
Qed.


Print RMatrix.

Print MultList.
Print KronList. Search "†" "⊗".

Print Prim.
Definition PAdjoint (X : Prim) : Prim :=
  match X with
  | IPrim m n A => APrim m n A
  | APrim m n A => IPrim m n A
  end.
Lemma PAdjoint_Type : forall (X : Prim) m n,
    RMatrix_Type X m n ->
    RMatrix_Type (PAdjoint X) n m.
Proof.
  destruct X as [mA nA A | mA nA A]; intros m n H;
    dependent destruction H; simpl; auto with rtype.
Qed.
Hint Resolve PAdjoint_Type : rtype.
Lemma PAdjointEq : forall (X : Prim) m n,
    RMatrix_Type X m n ->
    PAdjoint X ==_{n,m} MAdjoint X.
Proof.
  destruct X as [mA nA A | mA nA A]; intros m n H;
    dependent destruction H; simpl.
  - reflexivity.
  - Search "†".
    About adjoint_involutive.
    dependent destruction H.
    
    rewrite (adjoint_involutive A).
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
  | LUnit c    => LUnit (c^*)
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
    Search "†" ".*".
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
  - dependent destruction H. Search (_ .* _)†. 
    rewrite Mscale_adj.
    Search (I _)†.
    rewrite id_adjoint_eq.
    reflexivity.
  - rewrite MLMultEq; auto with rtype; simpl.
    2:{ constructor; auto with rtype. }
    rewrite KAdjointEq; auto with rtype; simpl.
    rewrite IHM'; auto with rtype; simpl.
    autorewrite with M_db.
    Search (C1 .* _).
    rewrite Mscale_1_l.
    rewrite Mmult_1_r.
    reflexivity.
Qed.



Print SumList. Search "†" ".+".
Fixpoint SAdjoint (m n : nat) (S : SumList) : SumList :=
  match S with
  | LZero _ _ => LZero n m
  | LPlus M S' => (* (M + S')† = M† + S'† *)
    LPlus (MLAdjoint m n M) (SAdjoint m n S')
  end.
Lemma SAdjoint_Type : forall (S : SumList) m n,
    RMatrix_Type S m n ->
    RMatrix_Type (SAdjoint m n S) n m.
Print SumList.
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
  - autorewrite with M_db. Search Zero†.
    rewrite zero_adjoint_eq.
    reflexivity.
  - rewrite MLAdjointEq; auto.
    rewrite IHS'; auto.
    autorewrite with M_db.
    reflexivity.
Qed.





Print RMatrix.

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
    assert (H : RMatrix_Type (MKron m n (MPrim m0) 1 1 (MScale 1%R (MI 1))) (m*1) (n*1))
      by auto with rtype.
    repeat rewrite Nat.mul_1_r in H.
    exact H.
Qed.
Hint Resolve reify_SumList_Type : rtype.

Lemma reify_SumListEq : forall M m n,
      RMatrix_Type M m n ->
      M ==_{m,n} reify_SumList M m n.
Proof.
  induction M; intros m' n' H;
    dependent destruction H; simpl;
    try (rewrite IHM1; auto with rtype);
    try (rewrite IHM2; auto with rtype);
    try (rewrite IHM; auto with rtype).
  - rewrite Mplus_0_r.
    rewrite (Mscale_1_l (I n)).
    rewrite Mmult_1_r.
    assert (H : @mat_equiv (m*1) (n*1) m0 (m0 ⊗ (C1 .* I 1))).
    { rewrite Mscale_1_l. Search (_ ⊗ I _).
      rewrite (kron_1_r m0).
      reflexivity.
    }
    repeat rewrite Nat.mul_1_r in H.
    apply H.
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


Print RMatrix.
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
                         replace A with (reflect_RMatrix' M m n);
                            [ | rewrite_with_eqb ]
                       end;
                       match type of B with
                       | Matrix ?m' ?n' => 
                         replace B with (reflect_RMatrix' N m' n'); 
                           [ | rewrite_with_eqb ]
                       end
  end.



Ltac RMatrix_reflection :=
  reify_matrices; 
  rewrite reify_SumListEq; [rewrite_with_eqb | apply RMatrix_size_Type; rewrite_with_eqb].

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
  RMatrix_reflection.
Qed.