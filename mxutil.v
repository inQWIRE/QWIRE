(* (c) Copyright ? *)

(*****************************************************************************
  Some matrix operations and lemmas: column-wise vectorization, Kronecker 
product, Hadamard (element-wise) product, the commutation matrix, etc.

      rvec A == row-wise vectorization of A, synonym of mxvec
       vec A == column-wise vectorization A, reshaping an m x n matrix into 
                a column vector of height n * m
   cvec_mx v == the inverse of vec, reshaping a column vector of height n * m 
                back into an m x n rectangular matrix.
      A *o B == Kronecker product of A and B. Its type is 'M_(m1,n1) -> 
                'M_(m2,n2) -> 'M_(m1*m2,n1*n2). Its characteristic properties are:
                (1) in terms of rvec:
                  kronP : rvec C *m (A *o B) = rvec (A^T *m C *m B) 
                (2) in terms of vec:
                  kronPc : vec (A *m B *m C) = (C^T *o A) *m vec B 
                Another viewpoint of Kronecker product is:
                  | a11 a12 |        | a11*:B  a12*:B |
                  |         | *o B = |                |
                  | a21 a22 |        | a21*:B  a22*:B |
 map2_mx f A B == the pointwise operation of A and B by f, i.e., 
                  (map2_mx f A B) i j = f (A i j) (B i j) for all i and j. 
                  A and B must have the same size.
      A .* B == Hadamard (element-wise) product
         trT == the commutation matrix, whose characteristic properties are:
                (1) in terms of rvec:
                  trTP : rvec A *m trT^T = rvec A^T
                (2) in terms of vec:
                  trTPc : trT *m vec A = vec A^T 

  Some notations:
           I == identity matrix, synonym of 1%:M
      A ^^-1 == the inverse of square matrix A, synonym of (invmx A)
invertible A == square matrix A is invertible, synonym of (A \in unitmx)

******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
From mathcomp Require Import finfun bigop prime binomial.
From mathcomp Require Import matrix.
From mathcomp Require Import ssralg.
Import GRing.Theory.
Open Local Scope ring_scope.

Local Notation I := (1%:M).
Local Notation rvec := mxvec.
Local Notation vec A := (rvec A^T)^T.

Lemma map_vec aT rT (f : aT -> rT) m n (A : 'M_(m,n)) : map_mx f (vec A) = vec (map_mx f A).
Proof.
  by rewrite map_trmx -map_mxvec map_trmx.
Qed.

Section ColumnVectorToMatrix.

Variable E : Type.

(* Reshape a column vector back into a matrix *)
Definition cvec_mx m n (v : 'cV[E]_(n * m)) : 'M_(m,n) := (vec_mx v^T)^T.

Lemma cvec_mxK m n c : vec (@cvec_mx m n c) = c.
Proof.
  by rewrite trmxK vec_mxK trmxK.
Qed.

End ColumnVectorToMatrix.

Section KroneckerProduct.

(* mulmx_linear requires comRing *)
Variable R : comRingType.
Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types B : 'M[R]_(m2,n2).

(* Kronecker product *)
Definition kron A B := lin_mx ((mulmxr B) \o (mulmx A^T)).
Local Notation "A *o B" := (kron A B) (at level 40, left associativity).

(* The characteristic property of Kronecker product, in terms of rvec *)
Lemma kronP A B C : rvec C *m (A *o B) = rvec (A^T *m C *m B).
  by rewrite mul_vec_lin.
Qed.

End KroneckerProduct.

Local Notation "A *o B" := (kron A B) (at level 40, left associativity).

From mathcomp Require Import zmodp.

Section DeltaMxTheory.

Variable R : comRingType.
Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types B : 'M[R]_(m2,n2).

Lemma colE j A : col j A = A *m delta_mx j 0.
Proof.
  apply/colP=> i; rewrite !mxE (bigD1 j) //= mxE !eqxx mulr1.
  by rewrite big1 ?addr0 // => i' ne_i'i; rewrite mxE /= (negbTE ne_i'i) mulr0.
Qed.

Lemma rowcolE i j A B : A *m delta_mx i j *m B = col i A *m row j B.
Proof.
  by rewrite rowE colE !mulmxA -(mulmxA _ (delta_mx i 0)) mul_delta_mx.
Qed.

Lemma cVMrV m n (c : 'cV[R]_m) (r : 'rV_n) i j : (c *m r) i j = c i 0 * r 0 j.
Proof.
  by rewrite !mxE big_ord1.
Qed.

Lemma colMrowP i j A B ii jj : (col j A *m row i B) ii jj = A ii j * B i jj.
Proof.
  by rewrite cVMrV !mxE.
Qed.

End DeltaMxTheory.

Section KroneckerProductTheory.

Variable R : comRingType.

Section KronE.

Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types B : 'M[R]_(m2,n2).

Lemma kronE A B i1 i2 j1 j2 : (A *o B) (mxvec_index i1 i2) (mxvec_index j1 j2) = A i1 j1 * B i2 j2.
Proof.
  by rewrite !mxE /= mxvecE vec_mx_delta rowcolE colMrowP !mxE.
Qed.

End KronE.

Section TrmxKron.

Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types B : 'M[R]_(m2,n2).

Lemma trmx_kron A B : (A *o B)^T = (A^T *o B^T).
Proof.
  apply/matrixP=> i j.
  case/mxvec_indexP: i => n1i n2i.
  case/mxvec_indexP: j => m1i m2i.
  by rewrite mxE !kronE !mxE.
Qed.

Lemma kron0mx A : (0 : 'M_(m2,n2)) *o A = 0.
Proof.
  apply/matrixP=> i j; rewrite !mxE /= trmx0 !mul0mx /=.
  case/mxvec_indexP: j => x y.
  by rewrite mxvecE !mxE.
Qed.

Lemma kronmx0 A : A *o (0 : 'M_(m2,n2)) = 0.
Proof.
  apply/matrixP=> i j; rewrite !mxE /= !mulmx0 /=.
  case/mxvec_indexP: j => x y.
  by rewrite mxvecE !mxE.
Qed.

End TrmxKron.

Section KronPColumn.

Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types C : 'M[R]_(m2,n2).

(* The characteristic property of Kronecker product, in terms of vec *)
Lemma kronPc A B C : vec (A *m B *m C) = (C^T *o A) *m vec B.
Proof.
  by rewrite !trmx_mul !mulmxA -kronP !trmx_mul trmx_kron trmxK.
Qed.

End KronPColumn.

(* Corollaries from the characteristic properties *)
Section Corollaries.

Variables m n r : nat.
Implicit Types A : 'M[R]_(m,n).
Implicit Types B : 'M[R]_(n,r).

Corollary vec_kron A B : vec (A *m B) = (I *o A) *m vec B.
Proof.
  by rewrite -(mulmx1 (A *m B)) kronPc trmx1.
Qed.

Corollary vec_kron2 A B : vec (A *m B) = (B^T *o I) *m vec A.
Proof.
  by rewrite -(mul1mx (A *m B)) !mulmxA kronPc.
Qed.

Corollary kron_shift A B : (I *o A) *m vec B = (B^T *o I) *m vec A.
Proof.
  by rewrite -vec_kron vec_kron2.
Qed.

End Corollaries.

End KroneckerProductTheory.

Section Map2Matrix.

Variables (aT bT rT : Type) (f : aT -> bT -> rT).
Variable m n : nat.
Implicit Types A : 'M[aT]_(m,n).
Implicit Types B : 'M[bT]_(m,n).

(* Element-wise operation *)
Fact map2_mx_key : unit. Proof. by []. Qed.
Definition map2_mx A B := \matrix[map2_mx_key]_(i, j) f (A i j) (B i j).

End Map2Matrix.

(* Hadamard (element-wise) product *)
Local Notation elemprod := (map2_mx *%R).
Local Notation "A .* B" := (elemprod A B) (at level 40, left associativity).

Lemma cowP : forall (R : Type) (n : nat) (u v : 'cV[R]_n), (forall i, u i 0 = v i 0) <-> u = v.
Proof. by split=> [eq_uv | -> //]; apply/matrixP=> i j; rewrite ord1. Qed.

Lemma vec_elemprod {R : ringType} {m n} (A B : 'M[R]_(m,n)) : vec (A .* B) = diag_mx (vec A)^T *m vec B.
Proof.
  apply/cowP=> k; case/mxvec_indexP: k => i j.
  by rewrite mul_diag_mx !mxE !mxvecE !mxE.
Qed.

Section CommMx.

Variable E : comRingType.

Variable m n : nat.

(* The commutation matrix *)
Definition trT := (lin_mx (@trmx E m n))^T.

(* Characteristic properties *)
Lemma trTP A : rvec A *m trT^T = rvec A^T.
  by rewrite trmxK mul_vec_lin.
Qed.

Lemma trTPc A : trT *m vec A = vec A^T.
Proof.
  by apply trmx_inj; rewrite !trmx_mul (trmxK (rvec A^T)) trTP !trmxK.
Qed.

End CommMx.

(* Miscellaneous results *)

Lemma mulmx1Bl {E : ringType} m n A (B : 'M[E]_(m,n)) : (I - A) *m B = B - A *m B.
Proof. by rewrite mulmxBl mul1mx. Qed.

Lemma mulmx1Br {E : ringType} m n (A : 'M[E]_(m,n)) B : A *m (I - B) = A - A *m B.
Proof. by rewrite mulmxBr mulmx1. Qed.

Lemma mul1Brmx {E : ringType} m n (A : 'M[E]_(m,n)) B : (I - B) *m A = A - B *m A.
Proof. by rewrite mulmxBl mul1mx. Qed.

Lemma map_mxE {aT rT} {f : aT -> rT} {m n} (A : 'M_(m,n)) i j : (map_mx f A) i j = f (A i j).
Proof. by rewrite !mxE /=. Qed.

Lemma invmx_inv {R : comUnitRingType} {n} (A : 'M[R]_n.+1) : invmx A = A^-1.
Proof. by []. Qed.

Lemma scalar_mxE {R : ringType} n (a : R) (i : 'I_n) : a%:M i i = a.
Proof.
  by rewrite !mxE eqxx.
Qed.

Module Notations.

Notation elemprod := (map2_mx *%R).
Notation ".*%M" := elemprod : ring_scope.
Notation "A .* B" := (elemprod A B) (at level 40, left associativity) : ring_scope.
Notation rvec := mxvec.
Notation vec A := (rvec A^T)^T.
Notation "A *o B" := (kron A B) (at level 40, left associativity) : ring_scope.
Notation I := (1%:M).
Notation "A ^^-1" := (invmx A) (at level 8): ring_scope.
Notation invertible A := (A \in unitmx).

End Notations.