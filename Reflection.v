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

Lemma swap_kron : forall (m n : nat) (A : Matrix 2 m) (B : Matrix 2 n),
    swap × (A ⊗ B) == B ⊗ A.
Proof.
    intros m n A B.
    induction m; induction n.
    * rewrite dim0_r. rewrite (dim0_r A). rewrite (dim0_r B).
      rewrite kron_0_r.
      reflexivity.
    * rewrite dim0_r. 
      replace (B ⊗ A) with ((B ⊗ A) : Matrix 2 0) by reflexivity.
      rewrite (dim0_r (B ⊗ A)). reflexivity.
    * set (X := (B ⊗ A) : Matrix 2 0).
Admitted.

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
  | MMult             : RMatrix -> RMatrix -> RMatrix
  | MKron             : RMatrix -> RMatrix -> RMatrix
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
                        RMatrix_Type (MMult M1 M2) m o
  | tKron M1 M2 m1 n1 m2 n2 : RMatrix_Type M1 m1 n1 ->
                              RMatrix_Type M2 m2 n2 ->
                              RMatrix_Type (MKron M1 M2) (m1*m2) (n1*n2)
  | tAdjoint M m n : RMatrix_Type M m n -> RMatrix_Type (MAdjoint M) n m
.


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
  | MMult M1 M2 => do x ← RMatrix_size M1;
                   do y ← RMatrix_size M2;
                   if snd x =? fst y
                   then Some (fst x,snd y)
                   else None
  | MKron M1 M2 => do x1 ← RMatrix_size M1;
                   do x2 ← RMatrix_size M2;
                   Some (fst x1*fst x2, snd x1*snd x2)
  | MAdjoint M => do x ← RMatrix_size M;
                   Some (snd x, fst x)
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
    destruct (m1=?m2) eqn:Hm; [ apply beq_nat_true in Hm | inversion H].
    destruct (n1=?n2) eqn:Hn; [ apply beq_nat_true in Hn | inversion H].
    simpl in *.
    subst.
    inversion H.
    constructor; [apply IHM1 | apply IHM2]; auto.
  - (* Mult *)
    simpl in *. 
    destruct (RMatrix_size M1) as [[m1 n1] | ]; [ | inversion H].
    destruct (RMatrix_size M2) as [[m2 n2] | ]; [ | inversion H].
    simpl in *.
    destruct (n1=?m2) eqn:Hm; inversion H; apply beq_nat_true in Hm; subst.
    econstructor; [apply IHM1 | apply IHM2]; reflexivity.
  - (* Kron *)
    simpl in *. 
    destruct (RMatrix_size M1) as [[m1 n1] | ]; [ | inversion H].
    destruct (RMatrix_size M2) as [[m2 n2] | ]; [ | inversion H].
    simpl in *.
    inversion H; subst.
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


Fixpoint reflect_RMatrix' (M : RMatrix) : forall m n, 
         Matrix m n.
  destruct M as [ m n A
                | m n
                | n
                | M1 M2
                | M1 M2
                | M1 M2
                | c M
                | M ]; intros m' n'; simpl.
  * (* prim *) exact A.
  * (* zero *) exact Zero.
  * (* I *) exact (I n).
  * (* plus *) 
    destruct (RMatrix_size M1) as [[m1 n1] | ] eqn:H1; [ | exact Zero].
    destruct (RMatrix_size M2) as [[m2 n2] | ] eqn:H2; [ | exact Zero].
    set (A1 := reflect_RMatrix' M1 m1 n1).
    set (A2 := reflect_RMatrix' M2 m2 n2).
    exact (A1 .+ A2).
  * (* mult *)
    destruct (RMatrix_size M1) as [[m1 n1]|] eqn:H1; [ | exact Zero].
    destruct (RMatrix_size M2) as [[m2 n2]|] eqn:H2; [ | exact Zero].
    set (A1 := reflect_RMatrix' M1 m1 n1).
    set (A2 := reflect_RMatrix' M2 m2 n2).
    exact (@Mmult m1 n1 n2 A1 A2).
  * (* kron *)
    destruct (RMatrix_size M1) as [[m1 n1]|] eqn:H1; [ | exact Zero].
    destruct (RMatrix_size M2) as [[m2 n2]|] eqn:H2; [ | exact Zero].
    set (A1 := reflect_RMatrix' M1 m1 n1).
    set (A2 := reflect_RMatrix' M2 m2 n2).
    exact (A1 ⊗ A2).
  * (* scale *) 
    destruct (RMatrix_size M) as [[m n] | ] eqn:H; [ | exact Zero].
    set (A := reflect_RMatrix' M m' n').
    exact (c .* A).
  * (* adjoint *)
    destruct (RMatrix_size M) as [[m n]|] eqn:H; [ | exact Zero].
    set (A := reflect_RMatrix' M m n).
    exact (A†).
Defined.


Definition reflect_RMatrix (M : RMatrix) m n :
           RMatrix_size M = Some (m,n) ->
           Matrix m n :=
  fun pf => reflect_RMatrix' M m n.


(*******************************************************************)
(* Rules for solving the symmetric monoidal structure of unitaries *)
(*******************************************************************)


(* flatten to:
   sum_over [IList]
  where
    IList = MMult [IList] | MKron [IList] | Prim
  where
Record Prim := A_Prim 
               { A_dimx : nat
               ; A_dimy : nat
               ; A_Mat : Matrix A_dimx A_dimy
               ; A_Scale : option C
               ; A_Adjoint : bool
               }.

*)




(*
(* result is an RMatrix equivalent to M1 × M2 *)
(* produces a Matrix m n *)
Fixpoint RMult_r (M1 : RMatrix) (M2 : RMatrix) (m n : nat): RMatrix :=
  match M2 with
  | MZero _ _ => MZero m n
  | MI _      => M1
  | MScale c M2' => MScale c (RMult_r M1 M2' m n)
  | MPlus M21 M22 => MPlus (RMult_r M1 M21 m n) (RMult_r M1 M22 m n)
  | _  => MMult M1 M2
  end.

Definition RMult_l (m n o : nat) (M1 M2 : RMatrix) : RMatrix :=
  match M1 with
  | MZero _ _ => MZero m o
  | MI n, _ => return_ M2
  | MScale c M1' => MScale c (RMult_simpl M1' M2)
  | MPlus M11 M12  => MPlus (RMult_simpl M11 M2) (RMult_simpl M12 M2)
  | MMult M11 M12  => RMult_l M11 (MMult M12 M2)
  | _ => RMult_r M1 M2
  end.
*)



Fixpoint RMatrix_simpl (M : RMatrix) : RMatrix :=
  match M with
  | MMult M1 M2 => 
      match RMult_simpl (RMatrix_simpl M1) (RMatrix_simpl M2) with
      | Some M' => M'
      | None    => M
      end
  | _ => M
  end.


Lemma RMatrix_Type_simpl : forall M m n,
    RMatrix_Type M m n -> RMatrix_Type (RMatrix_simpl M) m n.
Admitted.

Lemma RMatrix_size_simpl : forall M,
    RMatrix_size (RMatrix_simpl M) = RMatrix_size M.
Admitted.



Ltac inversion_option :=
  match goal with
  | [H : None = Some _ |- _] => inversion H
  | [H : Some _ = None |- _] => inversion H
  | [H : Some _ = Some _ |- _] => inversion H; clear H
  end.


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




Lemma RMult_simpl_correct : forall M1 M2 m n o M',
    RMatrix_Type M1 m n ->
    RMatrix_Type M2 n o ->
    RMult_simpl M1 M2 = Some M' ->

    reflect_RMatrix' (MMult M1 M2) m o
 == reflect_RMatrix' M' m o.
Proof.
  intros M1 M2 m n o M' T1 T2 HM.
  generalize dependent M'. generalize dependent M2. generalize dependent o.
  induction T1; intros o' M2' T2; dependent induction T2; intros M' HM;
    try (inversion HM; fail);
    try (inversion HM; subst; simpl; (apply Mmult_0_l || apply Mmult_0_r); fail);
    try (
      repeat (simpl in *; (  rewrite_RMatrix_size 
                          || inversion_option 
                          || rewrite Nat.eqb_refl in *
                          ));
         (   apply Mmult_0_l || apply Mmult_0_r
          || apply Mmult_1_l || apply Mmult_1_r
         )).
Qed.

Lemma RMatrix_simpl_correct : forall M m n,
    RMatrix_size M = Some (m,n) ->
    reflect_RMatrix' M m n
 == reflect_RMatrix' (RMatrix_simpl M) m n.
Proof.
  induction M; intros m' n' H;
    try reflexivity.
  - simpl in *.
    rewrite_RMatrix_size' M1.
    rewrite_RMatrix_size' M2.
    simpl in *.
    destruct (n=?m0) eqn:Hm; [ apply beq_nat_true in Hm | inversion H].
    inversion_option.
    subst.
    destruct (RMult_simpl (RMatrix_simpl M1) (RMatrix_simpl M2)) as [M' | ] eqn:HM';
      auto.
    * rewrite IHM1; auto.
      rewrite IHM2; auto.
      replace (reflect_RMatrix' (RMatrix_simpl M1) m' m0 × reflect_RMatrix' (RMatrix_simpl M2) m0 n')
        with  (reflect_RMatrix' (MMult (RMatrix_simpl M1) (RMatrix_simpl M2)) m' n')
        by (simpl; repeat rewrite_RMatrix_size; reflexivity).
      eapply RMult_simpl_correct; auto.
      + apply RMatrix_Type_simpl.
        apply RMatrix_size_Type.
        eauto.
      + apply RMatrix_Type_simpl.
        apply RMatrix_size_Type.
        eauto.
    * simpl. repeat rewrite_RMatrix_size. reflexivity.
    * inversion_option.
    * inversion_option.
Qed.
    


(** Tactics **)





Ltac simplify_RMatrix_size := 
              repeat (simpl in *; (  rewrite_RMatrix_size 
                          || inversion_option 
                          || rewrite Nat.eqb_refl in *
                          ));
              try reflexivity.



Ltac reify_matrix e := 
  match e with
  | reflect_RMatrix' ?M ?m ?n => constr:(M)
  | reflect_RMatrix ?M ?m ?n _ => constr:(M)
  | @Zero ?m ?n => constr:(MZero m n)
  | I ?n => constr:(MI n)
  | ?A × ?B =>  let M := reify_matrix A in
                let N := reify_matrix B in
                constr:(MMult M N)
  | ?A ⊗ ?B => let M := reify_matrix A in
               let N := reify_matrix B in
               constr:(MKron M N)
  | _ => constr:(MPrim _ _ e)
  end.
Ltac reify_matrices :=
  match goal with
  | [ |- ?A == ?B ] => let M := (reify_matrix A) in
                       let N := (reify_matrix B) in
                       match type of A with
                       | Matrix ?m ?n => 
                         replace A with (reflect_RMatrix' M m n);
                            [ | simplify_RMatrix_size]
                       end;
                       match type of B with
                       | Matrix ?m' ?n' => 
                         replace B with (reflect_RMatrix' N m' n'); 
                           [ | simplify_RMatrix_size]
                       end
  end.



Ltac RMatrix_reflection :=
  reify_matrices;
  apply RMatrix_simpl_correct;
  simplify_RMatrix_size.

Lemma foo : ∣0⟩ ⊗ ∣0⟩ == (⟨1∣×∣1⟩).
Proof. 
  reify_matrices. simpl. 

(*
  replace (∣0⟩⊗∣0⟩) with (reflect_RMatrix (MKron (MPrim 2 1 ∣0⟩) (MPrim 2 1 ∣0⟩)))
    by reflexivity.
  replace (⟨1∣×∣1⟩) with (reflect_RMatrix (MMult (MPrim 1 2 ⟨1∣) (MPrim 2 1 ∣1⟩)))
    by reflexivity.
  simpl.
*)
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