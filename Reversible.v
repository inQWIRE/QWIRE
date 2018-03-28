Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Denotation.
Require Import DBCircuits.
Require Import TypeChecking.

Require Import List.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.
Delimit Scope matrix_scope with M.

(* ---------------------------------------*)

(* From ReVerC *)

Delimit Scope bexp_scope with bx.
Open Scope bexp_scope.

Inductive bexp := 
| bT    : bexp 
| bF    : bexp
| b_and : bexp -> bexp -> bexp 
| b_xor : bexp -> bexp -> bexp.

Infix "∧" := b_and (at level 40) : bexp_scope.
Infix "⊕" := b_xor (at level 40) : bexp_scope.

Definition b_or (a b : bexp) := (a ∧ b) ⊕ (a ⊕ b).
Definition b_neg (b : bexp)  := (bT ⊕ b).
Definition b_if (g a b : bexp) := (g ∧ a) ⊕ (b_neg g ∧ b).

Infix "∨" := b_or (at level 40) : bexp_scope.  
Notation "¬ b" := (b_neg b) (at level 10) : bexp_scope. 
Notation "'bif' g 'then' a 'else' b 'fib'" := (b_if g a b) (at level 90) : bexp_scope.

Reserved Notation "⌈ b ⌉" (at level 0). 

Fixpoint bexp_to_bool (b : bexp) : bool :=
  match b with
  | bT    => true
  | bF    => false
  | b_and a b => ⌈a⌉ && ⌈b⌉ 
  | b_xor a b => xorb ⌈a⌉ ⌈b⌉
  end 
  where "⌈ b ⌉" := (bexp_to_bool b) : bexp_scope.  

Locate "⌈ _ ⌉". 

Lemma b_or_to_bool : forall a b, ⌈a ∨ b⌉ = orb (⌈ a ⌉) (⌈ b ⌉).
Proof. intros. simpl. destruct ⌈a⌉, ⌈b⌉; reflexivity. Qed.
Lemma b_neg_to_bool : forall b, ⌈ ¬ b ⌉ = negb ⌈b⌉.
Proof. intros. simpl. destruct ⌈b⌉; reflexivity. Qed.
Lemma b_if_to_bool : forall g a b, ⌈ bif g then a else b fib ⌉ = if ⌈g⌉ then ⌈a⌉ else ⌈b⌉. 
Proof. intros. simpl. destruct ⌈g⌉,⌈a⌉,⌈b⌉; reflexivity. Qed.

(* ---------------------------------------*)

Fixpoint bexp_to_circ (b : bexp) : Box One Qubit :=
  box_ () ⇒
  match b with 
  | bT => gate_ p ← init1 @(); output p  
  | bF => gate_ p ← init0 @(); output p
  | b_and b1 b2 => let_ p1 ← unbox (bexp_to_circ b1) ();
                  let_ p2 ← unbox (bexp_to_circ b2) ();
                  unbox AND (p1,p2)
  | b_xor b1 b2 => let_ p1 ← unbox (bexp_to_circ b1) ();
                  let_ p2 ← unbox (bexp_to_circ b2) ();
                  unbox XOR (p1,p2)
  end.
Lemma WT_bexp_to_circ : forall b, Typed_Box (bexp_to_circ b).
Proof. induction b; type_check. Qed.

(* ---------------------------------------*)
(*---------Classical Circuit Specs -------*)
(* ---------------------------------------*)

Open Scope matrix_scope.
Lemma X_spec : forall b, super σx (bool_to_matrix b) = bool_to_matrix (negb b).
Proof. ket_denote. destruct b; solve_matrix. Qed.

Lemma NOT_spec : forall (b : bool), 
  ⟦boxed_gate X⟧ (bool_to_matrix b) = bool_to_matrix (negb b).
Proof. ket_denote. destruct b; unfold bool_to_ket; simpl; Msimpl; reflexivity. Qed.

Lemma CNOT_spec : forall b1 b2, super (control σx) (bool_to_matrix b1 ⊗ bool_to_matrix b2)
                           = (bool_to_matrix b1 ⊗ bool_to_matrix (xorb b1 b2)).
Proof. 
  ket_denote. destruct b1, b2; unfold bool_to_ket; simpl; Msimpl; solve_matrix.
Qed.

(* non-reversible circuits temporarily commented out:
Lemma XOR_spec : forall (b1 b2 : bool), 
    ⟦XOR⟧ (bool_to_matrix b1 ⊗ bool_to_matrix b2)%M  = bool_to_matrix (xorb b1 b2).
Proof.  intros b1 b2. 
        repeat (autounfold with den_db; simpl); Msimpl.
        repeat rewrite bool_to_matrix_eq; unfold bool_to_matrix'.
        solve_matrix;
        destruct b1, b2; simpl; clra.
Qed.


Lemma CCNOT_spec : forall (b1 b2 : bool), 
    denote_box true CCNOT (bool_to_matrix b1 ⊗ bool_to_matrix b2 ⊗ |0⟩⟨0|)%M  
      = (bool_to_matrix b1 ⊗ bool_to_matrix b2 ⊗ bool_to_matrix (andb b1 b2))%M.
Proof.
  ket_denote. 
  destruct b1, b2; unfold bool_to_ket; simpl; Msimpl; solve_matrix.
Qed.

Lemma AND_spec : forall (b1 b2 : bool), 
    ⟦AND⟧ (bool_to_matrix b1 ⊗ bool_to_matrix b2)%M  = bool_to_matrix (andb b1 b2).
Proof. 
  intros b1 b2. 
  repeat (autounfold with den_db; simpl). Msimpl.
  repeat rewrite bool_to_matrix_eq; unfold bool_to_matrix'.
  solve_matrix.
  all: destruct b1, b2; simpl; Csimpl; try reflexivity.
Qed.
  
Lemma OR_spec : forall (b1 b2 : bool), 
    ⟦OR⟧ (bool_to_matrix b1 ⊗ bool_to_matrix b2)%M  = bool_to_matrix (orb b1 b2).
Proof. 
  intros b1 b2. 
  repeat (autounfold with den_db; simpl). Msimpl.
  repeat rewrite bool_to_matrix_eq; unfold bool_to_matrix'.
  solve_matrix.
  all: destruct b1, b2; simpl; Csimpl; try reflexivity.
Qed.

(* ---------------------------------------*)

Lemma bexp_to_circ_correct : forall b, 
  ⟦bexp_to_circ b⟧ I1 = bool_to_matrix ⌈b⌉.
Proof.
  induction b.
  + repeat (autounfold with den_db; simpl). solve_matrix.
  + repeat (autounfold with den_db; simpl). solve_matrix.
  + Opaque AND. 
    repeat (autounfold with den_db; simpl).
    replace 0%nat with (⟦∅⟧) by auto.

    specialize denote_compose as DC. simpl in DC.
    unfold denote_circuit in DC.

    rewrite DC with (Γ := ∅) (Γ1 := ∅) (Γ1' := ∅);
    [ | apply unbox_typing; [type_check | apply WT_bexp_to_circ]
    | repeat (type_check; try apply WT_bexp_to_circ)
    | type_check ].

    rewrite DC with (Γ := ∅) (Γ1 := Valid [Some Qubit]) (Γ1' := Valid [Some Qubit]);
    [ | apply unbox_typing; [type_check | apply WT_bexp_to_circ]
    | intros; apply AND_WT; type_check; constructor
    | type_check ].
    
    repeat rewrite merge_nil_l.
    unfold compose_super.

    (* apply IH1 *)
    rewrite denote_db_unbox in IHb1.
    unfold denote_circuit in IHb1.
    simpl in IHb1. simpl.
    rewrite IHb1.
        
    rewrite <- (kron_1_l 2 2 (bool_to_matrix ⌈ b1 ⌉)) by 
          (try omega; try apply WF_bool_to_matrix).

    setoid_rewrite (denote_db_pad_right (Valid [Some Qubit]) ∅ 1 0); trivial.

    (* apply IH2 *)
    unfold I1 in *.
    rewrite denote_db_unbox in IHb2.
    unfold denote_circuit in IHb2. simpl in IHb2.
    unfold denote_circuit. simpl.
    rewrite IHb2.

    (* apply AND_spec *)
    specialize AND_spec; intros HA.
    rewrite denote_db_unbox in HA.
    simpl in HA.
    unfold denote_circuit in HA.
    rewrite HA.
    rewrite andb_comm.
    reflexivity.
    Transparent AND.
  + Opaque XOR. 
    repeat (autounfold with den_db; simpl).
    replace 0%nat with (⟦∅⟧) by auto.

    specialize denote_compose as DC. simpl in DC.
    unfold denote_circuit in DC.

    rewrite DC with (Γ := ∅) (Γ1 := ∅) (Γ1' := ∅);
    [ | apply unbox_typing; [type_check | apply WT_bexp_to_circ]
    | repeat (type_check; try apply WT_bexp_to_circ)
    | type_check ].
  
    erewrite DC with (Γ := ∅) (Γ1 := Valid [Some Qubit]) (Γ1' := Valid [Some Qubit]);
    [ | apply unbox_typing; [type_check | apply WT_bexp_to_circ]
    | intros; apply XOR_WT; type_check; constructor
    | type_check ].

    repeat rewrite merge_nil_l.
    unfold compose_super.

    (* apply IH1 *)
    rewrite denote_db_unbox in IHb1.
    unfold denote_circuit in IHb1.
    simpl in IHb1. simpl.
    rewrite IHb1.
        
    rewrite <- (kron_1_l 2 2 (bool_to_matrix ⌈ b1 ⌉)) by 
          (try omega; try apply WF_bool_to_matrix).

    setoid_rewrite (denote_db_pad_right (Valid [Some Qubit]) ∅ 1 0); trivial.

    (* apply IH2 *)
    unfold I1 in *.
    rewrite denote_db_unbox in IHb2.
    unfold denote_circuit in IHb2. simpl in IHb2.
    unfold denote_circuit. simpl.
    rewrite IHb2.

    (* apply AND_spec *)
    specialize XOR_spec; intros HX.
    rewrite denote_db_unbox in HX.
    simpl in HX.
    unfold denote_circuit in HX.
    rewrite HX.
    rewrite xorb_comm.
    reflexivity.
    Transparent XOR.
Qed.
*)

Close Scope bexp_scope.
Close Scope matrix_scope.

(**********************)
(* Syntactic Property *)
(**********************)

Close Scope matrix_scope.
Open Scope circ_scope.

Ltac destruct_pats :=
  repeat match goal with
  | [ p : Pat (S _ ⨂ _) |- _ ] => dependent destruction p
  | [ p : Pat Qubit |- _ ] => dependent destruction p
  | [ p : Pat Bit |- _ ] => dependent destruction p
  | [ p : Pat (_ ⊗ _) |- _] => dependent destruction p
  | [ p : Pat One |- _] => dependent destruction p
  end.

Definition partition (i : nat) {n} (p : Pat (n ⨂ Qubit))  (pf : (i < n)%nat)
                 : Pat (S i ⨂ Qubit) * Pat ((n-i - 1) ⨂ Qubit).
Proof.
  destruct n.
  { absurd False; auto. inversion pf. }
  induction i.
  * simpl in *. 
    dependent destruction p. 
    replace (n-0)%nat with n by omega.
    refine (_, p2)%core.
    exact (p1,()).
  * simpl.
    assert (pf' : (i < S n)%nat) by omega.
    destruct (IHi pf') as [p1 p2].
    replace (S n - i - 1)%nat with (S (n-i - 1))%nat in p2 by omega.
    simpl in p1, p2. 
    dependent destruction p2.
    refine (_, p2_2)%core.
    refine (p2_1, p1).
Defined.
Definition head {n} (p : Pat (n ⨂ Qubit)) (pf : (0 < n)%nat)
                  : Var * Pat ((n-1)%nat ⨂ Qubit).
Proof.
  destruct (partition 0 p pf) as [p1 p2].
  dependent destruction p1.
  dependent destruction p1_1.
  replace (n - 0 - 1)%nat with (n - 1)%nat in p2 by omega.
  exact (v,p2)%core.
Defined.

Definition join {i j : nat}
                (p1 : Pat (i ⨂ Qubit)) (p2 : Pat (j ⨂ Qubit))
              : Pat ((i + j) ⨂ Qubit).
Proof.
  dependent induction i.
  - exact p2.
  - replace (S i + j)%nat with (S (i + j))%nat by omega.
    dependent destruction p1; rename p1_1 into x, p1_2 into p1.
    refine (x,IHi j p1 p2).
Defined.

Definition unitary_at1 {n} (U : Unitary Qubit) (ls : list nat)
        : Box (n ⨂ Qubit) (n ⨂ Qubit).
Proof.
    destruct ls as [ | i _]; [(* ERROR *) exact id_circ | ].
    (* should have i < n *)
    destruct (lt_dec i n) as [pf | ]; [ | (* ERROR *) exact id_circ ].
    refine (box_ p ⇒ _).
    destruct (partition i p pf) as [p1 p2].
    simpl in p1.
    dependent destruction p1; rename p1_1 into x, p1_2 into p1.
    
    refine (gate_ x' ← U @x ; _). 
    set (p' := @join (S i) _ (x',p1) p2). 
    replace (S i + (n - i - 1))%nat with n in p' by omega.
    exact (output p').
Defined.

Definition assert (b : bool) : Gate Qubit One := if b then assert1 else assert0.

Definition assert_at (b : bool) {n : nat} (i : nat) : Box (S n ⨂ Qubit) (n ⨂ Qubit).
Proof.
  (* if i > n, error *)
  destruct (lt_dec i (S n)) as [pf | ].
  * (* i < S n *) 
    refine (box_ p ⇒ _ ). 
    destruct (partition i p pf) as [p1 p2].
    dependent destruction p1; rename p1_1 into x, p1_2 into p1.
    refine (let_ y ← assert b $ x; _).
    dependent destruction y.
    set (p' := join p1 p2).
    replace (i + (S n - i - 1))%nat with n in p' by omega.
    exact (output p').
    
  * (* i >= n *) refine (box_ p ⇒ _). 
                 refine (let_ x ← (assert b || id_circ) $ p; _).
                 dependent destruction x.
                 refine (output x2).
Defined.

Definition init_at (b : bool) {n : nat} (i : nat) : Box (n ⨂ Qubit) (S n ⨂ Qubit).
Proof.
  (* if i >= n, error *)
  destruct (lt_dec i n) as [pf | ].
  * (* i < n *)
    refine (box_ p ⇒ _).
    destruct (partition i p pf) as [p1 p2].
    refine (let_ x ← init b $ (); _).
    set (px := (x,()) : Pat (1 ⨂ Qubit)).
    set (p' := join (join p1 px) p2).
    replace (S i + 1 + (n - i - 1))%nat with (S n) in p' by omega.
    exact (output p').
  * (* i >= n -- ERROR *)
    refine (box_ p ⇒ let_ x ← init b $ (); output (x,p)).
Defined.

Definition unitary_at {n} {w} (U : Unitary w) (ls : list nat) 
        : Box (n ⨂ Qubit) (n ⨂ Qubit).
Proof.
  destruct U.
  * (* H *) exact (unitary_at1 H ls).
  * (* X *) exact (unitary_at1 X ls).
  * (* Y *) exact (unitary_at1 Y ls).
  * (* Z *) exact (unitary_at1 Z ls).
  * (* ctrl *)
    destruct ls as [ | i [ | j ls]]; [ (* ERROR *) exact id_circ 
                                     | (* ERROR *) exact id_circ | ].
    (* if i >= n or j >= n or i = j, error *)
    destruct (lt_dec i n) as [pf_i | ]; [ | (* ERROR *) exact id_circ ].
    destruct (lt_dec j n) as [pf_j | ]; [ | (* ERROR *) exact id_circ ].
    destruct (Nat.eq_dec i j) as [pf_eq | ]; [ (* ERROR *) exact id_circ | ].
    
    -- 
    refine (box_ p ⇒ _).
    destruct (partition i p pf_i) as [p1 p2]; clear p.
    dependent destruction p1; rename p1_1 into x, p1_2 into p1.

    admit.

  * (* bit_ctrl *) admit.
  * (* transpose U *) 
    destruct ls as [ | i _]; [(* ERROR *) exact id_circ | ].
    destruct (lt_dec i n) as [pf | ]; [ | (* ERROR *) exact id_circ ].
    
Admitted.




Inductive Classical_Gate : forall (n t : nat),
  Box ((n+t) ⨂ Qubit) ((n+t) ⨂ Qubit) -> Type :=
| classical_X {n t} i : Classical_Gate n t (unitary_at X [i])
| classical_CNOT {n t} i j : Classical_Gate n t (unitary_at CNOT [i;j])
| classical_CCNOT {n t} i j k : Classical_Gate n t (unitary_at CCNOT [i;j;k])
.
Definition uncompute {n t} b (pf : Classical_Gate n t b) 
                   : Box ((n+t) ⨂ Qubit) ((n+t) ⨂ Qubit).
Proof.
  destruct pf.
  * (* X *) (* if i < n, then uncompute it, otherwise leave it alone *)
    destruct (lt_dec i n).
    + exact (unitary_at X [i]).
    + exact id_circ.
  * (* CNOT *) (* if j < n then uncompute it, otherwise leave it alone *)
    destruct (lt_dec j n).
    + exact (unitary_at CNOT [i;j]).
    + exact id_circ.
  * (* CCNOT *) (* if k < n then uncompute it, otherwise leave it alone *)
    destruct (lt_dec k n).
    + exact (unitary_at CCNOT [i;j;k]).
    + exact id_circ.
Defined.

Lemma Tensor_S_plus : forall m n q,
    (S m + n) ⨂ q = (m + S n) ⨂ q.
Proof.
  intros.  replace (S m + n)%nat with (m + S n)%nat by omega.
  reflexivity.
Qed.

Program Definition coerce {n t} (c : Box ((n + S t) ⨂ Qubit) ((n + S t) ⨂ Qubit))
                              :  Box ((S n + t) ⨂ Qubit) ((S n + t) ⨂ Qubit) := c.
Next Obligation.
  rewrite <- Tensor_S_plus. reflexivity.
Defined.
Next Obligation.
  rewrite <- Tensor_S_plus. reflexivity.
Defined.

Program Inductive Symmetric t : forall n,  Box ((n+t) ⨂ Qubit) ((n+t) ⨂ Qubit) -> Type :=
| s_idcirc {n} : Symmetric t n id_circ
| s_classical_l {n g b} : forall (pf : Classical_Gate n (S t) g),
                Symmetric t (S n) b ->
                Symmetric t (S n) (coerce (uncompute g pf) · coerce g ·  b)
| s_classical_r {n g b} : forall (pf : Classical_Gate n (S t) g),
                Symmetric t (S n) b ->
                Symmetric t (S n) (coerce g ·  b · coerce (uncompute g pf))
| s_init {n} (x : bool) {b} i : 
           (i < S n)%nat ->
           Symmetric t (S n) b ->
           Symmetric t n (assert_at x i · b · init_at x i)
.

Lemma size_ntensor : forall n W, size_wtype (n ⨂ W) = (n * size_wtype W)%nat.
Proof.
  intros n W.
  induction n; trivial.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma inSeq_assoc : forall {w1 w2 w3 w4} (b1 : Box w1 w2) (b2 : Box w2 w3) (b3 : Box w3 w4),
      b3 · (b2 · b1) = (b3 · b2) · b1.
Proof.
  intros w1 w2 w3 w4 [c1] [c2] [c3]. unfold inSeq. simpl.
  apply f_equal; apply functional_extensionality; intros p1.
  simpl.
  remember (c1 p1) as c. clear c1 p1 Heqc.
  dependent induction c.
  - reflexivity.
  - simpl. apply f_equal; apply functional_extensionality; intros p2.
    rewrite H.
    reflexivity.
  - simpl. apply f_equal; apply functional_extensionality; intros p2.
    rewrite H.
    reflexivity.
Qed.
  

Require Ring.

About denote_box.
Lemma symmetric_id : forall {n t} (c : Box ((n+t) ⨂ Qubit) ((n + t) ⨂ Qubit)),
    Symmetric t n c -> forall ρ ρ',
    WF_Matrix (2^n)%nat (2^n)%nat ρ ->
    WF_Matrix (2^t)%nat (2^t)%nat ρ' ->
    exists ρ'', WF_Matrix (2^t)%nat (2^t)%nat ρ'' 
             /\ ⟦c⟧ (ρ ⊗ ρ' : Matrix (2^n * 2^t) (2^n*2^t))%M = (ρ ⊗ ρ'')%M.
Proof.
  intros n t c pf_c.
  induction pf_c; intros ρ ρ' pf_ρ pf_ρ'.
  - exists ρ'. split; auto.
    simpl. autounfold with den_db. simpl. 
    rewrite size_ntensor. simpl. rewrite Nat.mul_1_r.
    rewrite pad_nothing.
    rewrite hoas_to_db_pat_fresh_empty.
    rewrite denote_pat_fresh_id.
    matrix_denote.
    rewrite size_ntensor. simpl. rewrite Nat.mul_1_r.
    Msimpl. reflexivity.
Admitted.
  

Lemma symmetric_spec : forall {n t} (b : Box ((n+t) ⨂ Qubit) ((n + t) ⨂ Qubit)) ρ,
                                    Symmetric n b  -> WF_Matrix (2^(n+t))%nat (2^(n+t))%nat ρ ->
                                    ⟦ inSeq b b ⟧ ρ = ρ.
Proof.
  intros n t b ρ pf.
  induction pf; intros wf_ρ.
  - simpl. autounfold with den_db. simpl. 
    rewrite size_ntensor. simpl. rewrite Nat.mul_1_r.
    rewrite pad_nothing.
    rewrite hoas_to_db_pat_fresh_empty.
    rewrite denote_pat_fresh_id.
    simpl. 
    rewrite size_ntensor. simpl. rewrite Nat.mul_1_r.
    rewrite super_I; auto.
  - replace (((coerce (uncompute g pf)) · (coerce g) · b) · (coerce (uncompute g pf)) · (coerce g) · b)
      with ((coerce (uncompute g pf) · ((coerce g) · b · coerce (uncompute g pf)) · coerce g) · b)
      by (repeat rewrite <- inSeq_assoc; reflexivity).
Admitted.

(* -----------------------------------------*)
(*--------- Reversible Circuit Specs -------*)
(* -----------------------------------------*)

Open Scope matrix_scope.

Notation "¬ b" := (negb b).
Infix  "⊕" := xorb.

Lemma R_TRUE_spec : forall z, ⟦R_TRUE⟧ (bool_to_matrix z) = bool_to_matrix (true ⊕ z). 
Proof. 
  ket_denote. 
  destruct z; unfold bool_to_ket; simpl; Msimpl; reflexivity. 
Qed.

Lemma R_FALSE_spec : forall z, 
    ⟦R_FALSE⟧ (bool_to_matrix z) = bool_to_matrix (false ⊕ z). 
Proof.
  ket_denote. 
  destruct z; unfold bool_to_ket; simpl; Msimpl; reflexivity. 
Qed.

Lemma R_NOT_spec : forall (x z : bool), 
  ⟦R_NOT⟧ (bool_to_matrix x ⊗ bool_to_matrix z) = 
  bool_to_matrix x ⊗ bool_to_matrix ((¬ x) ⊕ z).
Proof.
  ket_denote. 
  destruct x, z; unfold bool_to_ket; simpl; Msimpl; solve_matrix. 
Qed.

Lemma R_XOR_spec : forall (x y z : bool), 
    ⟦R_XOR⟧ (bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix z)  = 
    bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix (x ⊕ y ⊕ z).
Proof.  
  ket_denote. Msimpl.
  destruct x, y, z; unfold bool_to_ket; simpl; Msimpl; solve_matrix. 
Qed.

Lemma R_AND_spec : forall (x y z : bool), 
    ⟦R_AND⟧ (bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix z)  = 
    bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix ((x && y) ⊕ z).
Proof. 
  ket_denote. Msimpl.
  destruct x, y, z; unfold bool_to_ket; simpl; Msimpl; solve_matrix. 
Qed.

Close Scope matrix_scope.

(* --------------------------------*)
(* Reversible bexps with variables *)
(* --------------------------------*)

Delimit Scope rbexp_scope with rbx.
Open Scope rbexp_scope.

Inductive rbexp := 
| rb_t   : rbexp
| rb_f   : rbexp
| rb_var : Var -> rbexp
| rb_not : rbexp -> rbexp
| rb_and : rbexp -> rbexp -> rbexp 
| rb_xor : rbexp -> rbexp -> rbexp.

Reserved Notation "⌈ b | f ⌉" (at level 0). 

Fixpoint interpret_rbexp (b : rbexp) (f : Var -> bool) : bool :=
  match b with
  | rb_t         => true 
  | rb_f         => false 
  | rb_var v     => f v 
  | rb_not b     => ¬ ⌈ b | f ⌉
  | rb_and b1 b2 => ⌈ b1 | f⌉ && ⌈ b2 | f⌉
  | rb_xor b1 b2 => ⌈ b1 | f⌉ ⊕ ⌈ b2 | f⌉
  end where "⌈ b | f ⌉" := (interpret_rbexp b f).  

Reserved Notation "Γ1 ∪ Γ2" (at level 30).

(* assumes no conflicts - all wires are 'Qubit' *)
Fixpoint classical_merge (Γ1 Γ2 : Ctx) := 
  match Γ1, Γ2 with 
  | []           , _        => Γ2
  | _            , []       => Γ1
  | None :: Γ1'  , o :: Γ2' => o      :: (Γ1' ∪ Γ2') 
  | Some w :: Γ1', _ :: Γ2' => Some w :: (Γ1' ∪ Γ2') 
  end where "Γ1 ∪ Γ2" := (classical_merge Γ1 Γ2).

(* Gets a context for the variables in an rbexp *)
Fixpoint get_context (b : rbexp) : Ctx :=
  match b with 
  | rb_t          => [] 
  | rb_f          => []
  | rb_var v      => singleton v Qubit 
  | rb_not b      => get_context b 
  | rb_and b1 b2  => get_context b1 ∪ get_context b2 
  | rb_xor b1 b2  => get_context b1 ∪ get_context b2 
  end.

(* Gets the index of v in Γ excluding Nones *)
Fixpoint position_of (v : Var) (Γ : Ctx) : nat := 
  match v with
  | 0     => 0
  | S v'  => match Γ with
            | [] => 0
            | None :: Γ'   => position_of v'  Γ'
            | Some w :: Γ' => S (position_of v' Γ')
            end
  end.

(* Retrieves the nth wire in a list *)
(* Will return default if m = 0 or n >= m *)
Fixpoint get_wire {W m} (n : nat) (ps : Pat (m ⨂ W)) (default : Pat W) : Pat W.
destruct m as [|m'].
+ exact default.
+ simpl in ps.
  dependent destruction ps.
  destruct n as [|n']. 
  - exact ps1.
  - exact (get_wire W m' n' ps2 default).
Defined.

Lemma get_wire_WT : forall Γ m n default (p : Pat (m ⨂ Qubit)), 
  (n < m)%nat ->
  Γ ⊢ p :Pat ->
  {Γ1 : OCtx & {Γ2 : OCtx & Γ == Γ1 ∙ Γ2 &
                     Γ1  ⊢ get_wire n p default :Pat}}.
Proof.
  intros Γ m. 
  generalize dependent Γ.
  induction m.
  intros; omega.
  intros Γ n default p H H0.
  dependent destruction p.
  dependent destruction H0.
  destruct n.
  - simpl.
    unfold solution_left.
    unfold eq_rect_r.
    simpl.
    exists Γ1, Γ2. constructor; trivial. assumption.
  - edestruct (IHm Γ2 n default) as [Γ1' T].    
    omega.
    apply H0_0.
    destruct T as [Γ2' T].
    simpl in t.
    simpl.
    unfold solution_left.
    unfold eq_rect_r.
    simpl.
    exists Γ1', (Γ1 ⋓ Γ2'). 2: apply t.
    type_check.
Qed.    

(* Replaces the nth wire in a pattern with the given wire *)
Fixpoint replace_wire {W m} (p : Pat W) (n : nat) (ps : Pat (m ⨂ W)) : (Pat (m ⨂ W)).
destruct m as [|m'].
+ exact ps.
+ dependent destruction ps.
    destruct n as [|n'].
  - exact (p, ps2).
  - exact (ps1, replace_wire W m' p n' ps2).
Defined.

(* Different approach *)
Fixpoint default_wire (W : WType) : Pat W := 
  match W with
  | One          => unit  
  | Qubit        => qubit 0%nat
  | Bit          => bit 0%nat 
  | Tensor W1 W2 => (default_wire W1, default_wire W2)
  end.

Fixpoint unzip_wires {W m} (n : nat) (ps : Pat (m ⨂ W)) : 
  Pat (n ⨂ W) * Pat W * Pat ((m - n - 1) ⨂ W).  
  destruct m as [|m'].
  - (* failure case *)
    exact (default_wire _ , default_wire _, default_wire _)%core.
  - dependent destruction ps.
    destruct n as [|n']. 
    + simpl.
      rewrite Nat.sub_0_r. 
      exact (unit, ps1, ps2)%core.
    + simpl.
      apply unzip_wires with (n:=n') in ps2.
      destruct ps2 as [[ps1' p] ps2'].
      pose (ps1'' := (ps1,ps1')).
      exact (ps1'', p, ps2')%core.                                             
Defined.

Fixpoint zip_wires {W m1 m2} (ps1 : Pat (m1 ⨂ W)) (p: Pat W) (ps2 : Pat (m2 ⨂ W)) :
  Pat ((m1 + m2 + 1) ⨂ W).
destruct m1.
- simpl. rewrite Nat.add_1_r. apply (p,ps2).
- simpl. 
  dependent destruction ps1.
  specialize (zip_wires _ _ _ ps1_2 p ps2).
  exact (ps1_1, zip_wires).
Defined.

Notation "'Square_Box' W" := (Box W W) (at level 100).

(* Shares the kth of n qubits to the (last) target qubit *)
(* Returns the identity circuit if k > n *)
Fixpoint share_to (n k : nat) : Square_Box ((n ⨂ Qubit) ⊗ Qubit) := 
  match n with 
  | 0 => id_circ (* error: n < k *)
  | S n' => match k with
           | 0    => box_ qqst ⇒
                    let_ ((q,qs),t) ← output qqst;
                    gate_ (q,t)     ← CNOT @(q,t);
                    output ((q,qs),t)
           | S k' => box_ qqst ⇒
                    let_ ((q,qs),t) ← output qqst;
                    let_ (qs,t) ← unbox (share_to n' k') (qs,t);
                    output ((q,qs),t)
           end
  end.

(* Morally this circuit:
Fixpoint share_to' (n k : nat) : Square_Box (S n ⨂ Qubit) ⊗ Qubit := 
  match n with 
  | 0 => id_circ (* error: n < k *)
  | S n' => match k with
           | 0    => box_ qqst ⇒
                     let_ ((q,qs),t) ← output qqst;
                     gate_ (q,t)     ← CNOT @(q,t);
                     output ((q,qs),t)
           | S k' => (@id_circ Qubit) || (share_to' n' k')
           end
  end.
*)

Lemma share_to_WT : forall n k, Typed_Box (share_to n k).
Proof. induction n; type_check. destruct k; type_check. apply IHn; type_check. Qed.


Lemma size_repeat_ctx : forall n W, size_ctx (repeat (Some W) n) = n.
Proof.
  induction n; trivial.
  intros; simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma repeat_combine : forall T n1 n2 (t : T), 
  List.repeat t n1 ++ List.repeat t n2 = List.repeat t (n1 + n2).
Proof.
  induction n1; trivial. 
  intros. simpl. 
  rewrite IHn1.
  reflexivity.
Qed.

Lemma fresh_state_ntensor : forall n (Γ : Ctx), fresh_state (n ⨂ Qubit) (Valid Γ) = 
                                           Valid (Γ ++ List.repeat (Some Qubit) n).
Proof.                            
  induction n. 
  - intros. simpl. rewrite app_nil_r; reflexivity.
  - intros. simpl. rewrite IHn. rewrite <- app_assoc. reflexivity.
Qed.

Lemma ctx_dom_repeat : forall n, ctx_dom (repeat (Some Qubit) n) = seq 0 n.
Proof.      
  induction n; trivial.
  simpl.
  rewrite IHn.
  rewrite seq_shift.
  reflexivity.
Qed.

Fixpoint pat_max {W} (p : Pat W) : nat := 
  match p with
  | () => 0
  | qubit v => v 
  | bit v   => v 
  | (p1, p2) => Nat.max (pat_max p1) (pat_max p2)
  end.

(* Does it make sense to have a shifted version of this too? *)
Lemma subst_pat_σ_n: forall W n (p : Pat W), (pat_max p < n)%nat -> subst_pat (σ_{ n}) p = p.
Proof.
  intros.
  induction p.
  - simpl; reflexivity.
  - simpl in *.
    rewrite subst_var_σ_n; easy.
  - simpl in *.
    rewrite subst_var_σ_n; easy.
  - simpl in *.
    apply Nat.max_lub_lt_iff in H as [L1 L2].
    rewrite IHp1, IHp2; easy. 
Qed.

Lemma ntensor_pat_to_list_shifted : forall (m n o : nat),
  (m + n < o)%nat ->
  pat_to_list (subst_pat (σ_{o}) (fresh_pat (n ⨂ Qubit) 
                                 (Valid (repeat (Some Qubit) m )))) = seq m n. 
Proof.
  intros m n. revert m.
  induction n; trivial.
  intros.
  simpl.
  rewrite repeat_length.
  rewrite subst_var_σ_n by omega.
  Search subst_pat.
  Search repeat.
  replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
  rewrite repeat_combine.
  rewrite IHn by omega.
  rewrite Nat.add_1_r.
  reflexivity.
Qed.


Lemma pat_max_fresh : forall m n, 
    (pat_max (@fresh_pat OCtx OCtx_State (n ⨂ Qubit) (Valid (repeat (Some Qubit) m))) < S (m + n))%nat.
Proof.
  intros. 
  generalize dependent m.
  induction n.
  - intros; simpl; omega.
  - intros.
    simpl.
    rewrite repeat_length.
    apply Nat.max_lub_lt. omega.
    simpl. 
    specialize (IHn (S m)).
    rewrite <- Nat.add_1_r in IHn.
    rewrite <- (repeat_combine _ m 1%nat) in IHn.
    simpl in IHn.
    omega.
Qed.      

(* Also true, does this come up?
Lemma pat_max_fresh : forall m n, 
    (pat_max (fresh_pat (NTensor n Qubit) (σ_{ m}) ) < S (m + n))%nat.
Proof.
  intros. 
  generalize dependent m.
  induction n.
  - intros; simpl; omega.
  - intros.
    simpl.
    rewrite seq_length.
    apply Nat.max_lub_lt. omega.
    simpl. 
    rewrite <- seq_S.
    specialize (IHn (S m)). 
    omega.
Qed.      
*)

Open Scope matrix_scope.

(*
Lemma pat_to_ctx_typing :forall W (p : Pat W), pat_to_ctx p ⊢ p :Pat.
Proof.
  intros w p.
  induction p.
  - simpl. constructor.
  - simpl. constructor. apply singleton_singleton. 
  - simpl. constructor. apply singleton_singleton. 
  - simpl. econstructor. 3: apply IHp1. 3: apply IHp2. 2: reflexivity.
    *)

Ltac unlock_merge := rewrite merge_shadow in *.

Lemma merge_singleton_append : forall W (Γ : Ctx), 
        Γ ⋓ (singleton (length Γ) W) = Valid (Γ ++ [Some W]). 
Proof. 
  induction Γ.
  - simpl. rewrite merge_nil_l. reflexivity.
  - unlock_merge. simpl in *.
    destruct a; simpl; rewrite IHΓ; reflexivity.
Qed.

Lemma fresh_pat_disjoint : forall W Γ, is_valid Γ ->
                                  is_valid (Γ ⋓ pat_to_ctx (fresh_pat W Γ)).
Proof.
  induction W; simpl; intros.
  - destruct Γ as [|Γ]. invalid_contradiction.
    simpl. 
    rewrite merge_singleton_append.
    apply valid_valid.
  - destruct Γ as [|Γ]. invalid_contradiction.
    simpl.
    rewrite merge_singleton_append. apply valid_valid.
  - validate.
  - validate.
    apply IHW1; assumption.
    (* 2: apply IHW2. fresh_pat and fresh_state ? *)
Admitted.

Lemma fresh_pat_typed' :forall (w : WType) (p : Pat w) (Γ : OCtx),
  p = fresh_pat w Γ -> pat_to_ctx p ⊢ p :Pat.
Proof.
  intros w p.
  induction p; intros Γ H.
  - simpl. constructor.
  - simpl. constructor. apply singleton_singleton. 
  - simpl. constructor. apply singleton_singleton. 
  - simpl in *. 
    dependent destruction H.
    econstructor.
    2: reflexivity.
    2: eapply IHp1; reflexivity.
    2: eapply IHp2; reflexivity.
Admitted.    

Lemma types_pat_fresh_ntensor : forall n m, 
  Valid ((repeat None m) ++ (repeat (Some Qubit) n))  ⊢ 
        @fresh_pat OCtx OCtx_State (NTensor n Qubit) 
        (Valid (repeat (Some Qubit) m)) :Pat.
Admitted.

Lemma share_to_spec : forall (t b : bool) (k n : nat) (l1 l2 : list (Square 2)),
  (k < n)%nat ->
  length l1 = k ->
  length l2 = (n - k - 1)%nat ->
  (forall i, WF_Matrix 2 2 (nth i l1 (Zero 2%nat 2%nat))) ->
  (forall i, WF_Matrix 2 2 (nth i l2 (Zero 2%nat 2%nat))) ->
  ⟦share_to n k⟧  ((⨂ l1)  ⊗ bool_to_matrix b ⊗ (⨂ l2) ⊗ bool_to_matrix t) =  
 (⨂ l1) ⊗ (bool_to_matrix b) ⊗ (⨂ l2) ⊗ bool_to_matrix (xorb t b).
Proof.
  intros t b k n.
  generalize dependent k.
  induction n as [|n' IH]; [intros; omega|]. 
  intros k l1 l2 Lt L1 L2 WF1 WF2.
  destruct k.
  - clear IH.
    simpl in *.
    rewrite Nat.sub_0_r in L2. clear Lt.
    destruct l1. 2: simpl in L1; omega. clear L1.
    simpl. Msimpl. 
    unfold denote_box.
    simpl.
    rewrite Nat.add_1_r.
    unfold compose_super.
    simpl.

(* Show that padding and subst_var are the identity *)
    rewrite fresh_state_ntensor. 
    remember (repeat (Some Qubit) (S (S n'))) as Qubits.
    replace (([Some Qubit] ++ repeat (Some Qubit) n') ++ [Some Qubit])%core with 
        Qubits.
    Focus 2.
      subst. clear.
      replace ([Some Qubit]) with (repeat (Some Qubit) 1%nat) by reflexivity.
      repeat rewrite repeat_combine.
      rewrite Nat.add_1_r. reflexivity.
        
    simpl.
    rewrite repeat_length.
    unfold denote_pat.
    replace (pat_to_list _) with (σ_{S (S n')}).
    Focus 2.
      rewrite HeqQubits. clear.
      induction n'.
      reflexivity.
      rewrite seq_S.
      rewrite IHn'.
      simpl.
      rewrite ctx_dom_repeat.      
      repeat rewrite seq_shift.      
      replace (0%nat :: 1%nat :: 2%nat :: seq 3 n') with (σ_{3+n'}) by reflexivity.
      replace (0%nat :: 1%nat :: seq 2 n') with (σ_{2+n'}) by reflexivity.
      repeat rewrite subst_var_σ_n by omega.
      replace ([Some Qubit; Some Qubit]) with (repeat (Some Qubit) 2) by reflexivity.
      replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
      rewrite ntensor_pat_to_list_shifted by omega.
      rewrite ntensor_pat_to_list_shifted by omega.
      rewrite <- seq_S. simpl. reflexivity.
    simpl.
    rewrite size_ntensor. simpl.
    rewrite Nat.add_1_r, Nat.mul_1_r.
    rewrite swap_list_n_id.
    rewrite pad_nothing.
    subst.
    rewrite ctx_dom_repeat.
    repeat rewrite subst_var_σ_n by omega.

(* Show that apply_U CNOT [0; n] has desired behavior *)
    remember (S (length l2)) as n.
    remember ('I_ (2 ^ S n)) as I_m.
    replace (@Datatypes.cons Var O (@Datatypes.cons Var n (@Datatypes.nil Var)))
          with ([0; 0 + length l2 + 1])%nat.
    2: subst; rewrite Nat.add_1_r; reflexivity. 
  
    specialize (CNOT_spec b t) as CS.
    assert ((0 + length l2 + 0 + 2)%nat = S n)%nat as E. omega.
    specialize (apply_U_spec_2 (S n) O (length l2) O (Id 1) (⨂ l2) (Id 1) 
                             _ _ _ _ _ E CS). simpl; Msimpl.
    intros H. 
    rewrite H.
    subst.
    unfold super.
    apply WF_big_kron in WF2.
    Msimpl.
    rewrite Mmult_1_l, Mmult_1_r.
    rewrite xorb_comm.
    reflexivity.
    all: repeat (apply WF_kron; try omega; try unify_pows_two; auto with wf_db). 
  - simpl in *.
    destruct l1. inversion L1.
    simpl.

    repeat (autounfold with den_db; simpl).
    rewrite fresh_state_ntensor. simpl.
    rewrite size_ntensor. simpl. rewrite Nat.add_1_r, Nat.mul_1_r.
    replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
    rewrite repeat_combine.
    replace (Some Qubit :: repeat (Some Qubit) (n'+1)) with 
        (repeat (Some Qubit) (S (n' + 1))) by reflexivity.
    rewrite Nat.add_1_r.

    
    specialize denote_compose as DC. simpl in DC.
    unfold denote_circuit in DC.
    
    replace (S (S n')) with (⟦(Valid (repeat (Some Qubit) (S (S n'))))⟧).
    2: simpl; rewrite size_repeat_ctx; reflexivity.
    replace (⟦(Valid (repeat (Some Qubit) (S (S n'))))⟧) with (S (S n')) at 2.
    2: simpl; rewrite size_repeat_ctx; reflexivity.
    replace (O) with (⟦∅⟧) by reflexivity.

    specialize (share_to_WT n' k) as WT.
    erewrite DC with (Γ0 := ∅) (Γ1 := Valid [Some Qubit]) (Γ1':= (Valid (repeat (Some Qubit) (S (S n'))))).
    Focus 2. apply WT. simpl. rewrite repeat_length. econstructor.
    Focus 3.
      replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
      apply types_pat_fresh_ntensor.
    3: constructor; apply singleton_singleton.
    2: reflexivity.
    replace (S n') with (length ((repeat None 1) ++ repeat (Some Qubit) n')).
    rewrite merge_singleton_append. apply valid_valid.    
    rewrite app_length. repeat rewrite repeat_length. omega.
    
    Focus 3.
      constructor. apply valid_valid.
      replace (S n') with (length ((repeat None 1) ++ repeat (Some Qubit) n')).
      rewrite merge_singleton_append.
      Transparent merge. simpl. rewrite repeat_length.   
      replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
      rewrite repeat_combine. rewrite Nat.add_1_r. reflexivity.
      rewrite app_length. repeat rewrite repeat_length. omega.    
      Opaque merge.
    
    Focus 2.
      intros.
      simpl.
      dependent destruction p0.
      dependent destruction H0.
      unfold wproj.
      econstructor. 
      reflexivity.
      econstructor.
      destruct H; assumption.
      3: apply H0_0.
      Focus 2. econstructor. 
        4: apply H0_.
        3: constructor; apply singleton_singleton; reflexivity.
        2: reflexivity.
        destruct H. type_check.
      destruct H. simpl. rewrite <- merge_assoc. rewrite merge_comm. assumption.

      unfold compose_super. simpl.
      rewrite fresh_state_ntensor. simpl.
      replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
      rewrite repeat_combine.
      rewrite size_repeat_ctx.      
      unfold denote_pat. simpl.
      rewrite size_ntensor. simpl. rewrite Nat.mul_1_r, Nat.add_1_r.
      rewrite ctx_dom_repeat.      
      repeat rewrite seq_shift.      
      replace (0%nat :: seq 1 (S n')) with (σ_{2+n'}) by reflexivity.
      rewrite repeat_length.
      rewrite subst_var_σ_n by omega.
      rewrite subst_var_σ_n by omega.
      rewrite merge_nil_l.
      replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
      rewrite ntensor_pat_to_list_shifted by omega.
      unfold size_octx. simpl.
      specialize (merge_singleton_append Qubit (repeat (Some Qubit) n')) as MSA.
      simpl in MSA. rewrite repeat_length in MSA. 
      unlock_merge. simpl. rewrite MSA. clear MSA.
      rewrite <- seq_S.
      replace (@Datatypes.cons Var O (seq (S O) (S n'))) with (σ_{2+n'}) by
          reflexivity.
      rewrite swap_list_n_id.
      rewrite pad_nothing.
      remember ('I_ (2 ^ (2 + n'))) as Im. 
      simpl. 
      replace ([Some Qubit]) with (repeat (Some Qubit) 1) by reflexivity.
      rewrite repeat_combine.
      rewrite size_repeat_ctx.

      specialize (IH k l1 l2).
      specialize (denote_db_unbox (share_to n' k)) as DDU.
      simpl in DDU. rewrite DDU in IH. clear DDU.
      rewrite fresh_state_ntensor in IH. simpl in IH.

      repeat rewrite kron_assoc.
      setoid_rewrite kron_assoc.
      specialize denote_db_pad_left as DDP. unfold denote_circuit in *.
      specialize (DDP [Some Qubit] (repeat (Some Qubit) (n'+1)%nat) 1%nat (n'+1)%nat 
                      (Tensor (NTensor n' Qubit) Qubit)). 
      specialize (DDP (unbox (share_to n' k) (@fresh_pat OCtx OCtx_State 
        (NTensor n' Qubit) (Valid (repeat (Some Qubit) 1)), qubit (S n')))). 
      match goal with
      | [|- context[?a ⊗ ?b] ] => remember b as ρ2
      end.
      specialize (DDP m ρ2).
      simpl in DDP. rewrite size_repeat_ctx in DDP.
      simpl.
      show_dimensions.
      rewrite Nat.add_1_r in *. simpl in *.
      replace (2 ^ length l1 * (2 ^ length l2 * 2 + (2 ^ length l2 * 2 + 0)))%nat
              with (2 ^ n' + (2 ^ n' + 0))%nat.
      2: clear -L1 L2 Lt; inversion L1; subst; unify_pows_two. 
      rewrite DDP by reflexivity.
      hide_dimensions.
      rewrite decr_circuit_pat. simpl.
      rewrite (decr_pat_once_qubit n' []).
      rewrite Nat.sub_0_r.
      rewrite (repeat_combine (option WType) n' 1) in IH.
      rewrite size_repeat_ctx in IH.
      subst.
      rewrite repeat_length in IH.
      rewrite Nat.add_1_r in IH. simpl in IH.
      repeat rewrite kron_assoc in IH.
      assert (k < n')%nat as Lt' by (clear -Lt; omega).
      assert (length l1 = k)%nat as L1' by (clear -L1; omega). clear Lt L1.
      specialize (IH Lt' L1' L2).
      replace (2 ^ length l2 * 2 + (2 ^ length l2 * 2 + 0))%nat with 
          (2 * (2 ^ length l2 * 2))%nat by unify_pows_two.
      rewrite IH; trivial.      
      2: intros i; apply (WF1 (S i)).
      unfold super.
      rewrite size_ntensor. simpl. rewrite Nat.mul_1_r, Nat.add_1_r. simpl.
      apply WF_big_kron in WF2; trivial.
      assert (WF1': WF_Matrix (2 ^ length l1) (2 ^ length l1) (⨂ l1)).
      apply WF_big_kron. intros j. apply (WF1 (S j)).
      specialize (WF1 O). rename WF1 into WFm. rename WF1' into WF1.
      rewrite id_sa, Mmult_1_l, Mmult_1_r.
      reflexivity.
      repeat (apply WF_kron; try omega; try unify_pows_two; auto with wf_db).
      repeat (apply WF_kron; try omega; try unify_pows_two; auto with wf_db).
Qed.


(* Target is the extra qubit *)
Close Scope matrix_scope.
Fixpoint compile (b : rbexp) (Γ : Ctx) : Square_Box (((⟦Γ⟧) ⨂ Qubit) ⊗ Qubit) :=
  box_ qst ⇒
  let_ (qs,t) ← output qst;
  match b with
  | rb_t          => let_ t ← unbox R_TRUE t;
                    output (qs,t)
  | rb_f          => let_ t ← unbox R_FALSE t;
                    output (qs,t)
  | rb_var v      => let n := position_of v Γ in
                    unbox (share_to (⟦Γ⟧) v) (qs,t)
  | rb_not b      => gate_ q             ← init0 @();
                    let_ (qs,q)         ← unbox (compile b Γ) (qs,q);
                    let_ (q,t)          ← unbox R_NOT (q,t);
                    let_ (qs,q)         ← unbox (compile b Γ) (qs,q);
                    gate_ ()            ← assert0 @q;                    
                    output (qs,t)
  | rb_and b1 b2  => gate_ q1            ← init0 @();
                    let_ (qs,q1)        ← unbox (compile b1 Γ) (qs,q1);
                    gate_ q2            ← init0 @();
                    let_ (qs,q2)        ← unbox (compile b2 Γ) (qs,q2);
                    let_ (q1,q2,t)      ← unbox R_AND (q1,q2,t);
                    let_ (qs,q2)        ← unbox (compile b2 Γ) (qs,q2);
                    gate_ ()            ← assert0 @q2;
                    let_ (qs,q1)        ← unbox (compile b1 Γ) (qs,q1);
                    gate_ ()            ← assert0 @q1;
                    output (qs,t)
  | rb_xor b1 b2  => gate_ q1            ← init0 @();
                    let_ (qs,q1)        ← unbox (compile b1 Γ) (qs,q1);
                    gate_ q2            ← init0 @();
                    let_ (qs,q2)        ← unbox (compile b2 Γ) (qs,q2);
                    let_ (q1,q2,t)      ← unbox R_XOR (q1,q2,t);
                    let_ (qs,q2)        ← unbox (compile b2 Γ) (qs,q2);
                    gate_ ()            ← assert0 @q2;
                    let_ (qs,q1)        ← unbox (compile b1 Γ) (qs,q1);
                    gate_ ()            ← assert0 @q1;
                    output (qs,t)
  end.

(* Note that the "correct" Γ here is `get_context b` *)
Lemma WT_compile : forall (b : rbexp) (Γ : Ctx), 
    Typed_Box (compile b Γ).
Proof.
  induction b.
  - type_check.
  - type_check.
  - type_check. 
    apply share_to_WT.
    type_check.
  - type_check.
    eapply IHb.
    all:type_check.
    eapply IHb.
    all:type_check.
  - type_check.
    eapply IHb1. type_check.
    eapply IHb2. type_check.
    all: type_check.
    eapply IHb2. type_check.
    eapply IHb1. type_check.
    all: type_check.
  - type_check.
    eapply IHb1. type_check.
    eapply IHb2. type_check.
    all: type_check.
    eapply IHb2. type_check.
    eapply IHb1. type_check.
    all: type_check.
Qed.

Fixpoint bools_to_matrix (l : list bool) : Square (2^(length l)) := 
  match l with
  | [] => 'I_1
  | b :: bs => ((bool_to_matrix b) ⊗ (bools_to_matrix bs))%M
  end.

Definition reversible {W1 W2} (c : Box W1 W2) :=
  exists (f : Superoperator (2^⟦W2⟧) (2^⟦W1⟧)), forall ρ, (f ∘ ⟦c⟧) ρ = ρ /\ (⟦c⟧ ∘ f) ρ = ρ.

(* Equivalent definition: There is some unitary matrix that is equivalent 
   to this *)

(* Is this equal to the density matrix being pure? *)

Definition self_inverse {W} (c : Box W W) := forall ρ, (⟦c⟧ ∘ ⟦c⟧) ρ = ρ.

Lemma self_inverse_reversible : forall W (c : Box W W), self_inverse c ->
                                                   reversible c.
Proof. intros. unfold reversible, self_inverse in *. eauto. Qed.

Open Scope matrix_scope.

(*
Lemma xor_fun_self_inverse : forall W (c : Box W W) (f : list bool -> bool),
  (forall (x : list bool) (z : bool),
  ⟦c⟧ (bools_to_matrix x ⊗ bool_to_matrix z) = 
  (bools_to_matrix x) ⊗ bool_to_matrix (xorb z (f x))) -> 
  self_inverse c.                              
Proof.  
  intros W c f H.
  unfold self_inverse.
  intros ρ.
  (* This is equivalent to saying if P holds of the basis states, 
     it holds of arbitrary states. How to state this general theorem? *)
  (* This actually isn't true of circuits with measurement. *)
Abort.
*)
  


Inductive semi_classical {W} : Circuit W -> Set := 
| rev_output : forall p, semi_classical (output p)
| rev_not    : forall p1 c, semi_classical c -> semi_classical (gate_ p2 ←  X @p1; c)
| rev_cnot   : forall p1 c, semi_classical c -> semi_classical (gate_ p2 ←  CNOT @p1; c)
| rev_ccnot  : forall p1 c, semi_classical c -> semi_classical (gate_ p2 ← CCNOT @p1; c).

Definition semi_classical_box {W} (c : Box W W) :=
  match c with 
  | box c' => forall p, semi_classical (c' p)
  end.

Lemma semi_classical_reversible : forall W (c : Box W W), 
    semi_classical_box c -> reversible c.
Proof.
  intros W c H.
  unfold semi_classical_box in H.
  destruct c.
  unfold reversible.
Abort.

Fixpoint ctx_to_matrix (Γ : Ctx) (f : Var -> bool) {struct Γ} : Square (2^⟦Γ⟧) :=
  match Γ with 
  | [] => 'I_1
  | None :: Γ' => ctx_to_matrix Γ' (fun v => f (S v))
  | Some W :: Γ' => bool_to_matrix (f O) ⊗ ctx_to_matrix Γ' (fun v => f (S v))
  end.
Lemma WF_ctx_to_matrix : forall Γ f, WF_Matrix (2^⟦Γ⟧) (2^⟦Γ⟧) (ctx_to_matrix Γ f).
Proof.
  induction Γ; intros f.
  - auto with wf_db.
  - destruct a; simpl; auto with wf_db. 
Qed.
Hint Resolve WF_ctx_to_matrix : wf_db.


Eval simpl in (ctx_to_matrix [Some Qubit; None; None; Some Qubit; Some Qubit] 
               (fun v => if v =? 3 then true else false)).
Eval simpl in (ctx_to_matrix [Some Qubit; None; None; Some Qubit; Some Qubit] 
               (fun v => if v =? 2 then true else false)).

Reserved Notation "Γ1 ⊂ Γ2" (at level 90).

Inductive subset_eq : Ctx -> Ctx -> Set :=
| sub_empty : forall Γ, [] ⊂ Γ
| sub_none  : forall o Γ1 Γ2, Γ1 ⊂ Γ2 -> None :: Γ1 ⊂ o :: Γ2
| sub_some  : forall W Γ1 Γ2, Some W :: Γ1 ⊂ Some W :: Γ2
where "Γ1 ⊂ Γ2" := (subset_eq Γ1 Γ2).

Lemma compile_self_inverse : forall b Γ, Γ ⊂ get_context b ->
                                    self_inverse (compile b Γ).
Admitted.

Delimit Scope circ_scope with qc.

Lemma is_valid_singleton_merge : forall W (Γ : Ctx) n, (length Γ <= n)%nat ->
                                                  is_valid (Γ ⋓ singleton n W).
Proof.
  induction Γ; intros.
  - unlock_merge. simpl. apply valid_valid. 
  - destruct n. simpl in H; omega.
    unlock_merge. simpl.
    simpl in H. 
    destruct IHΓ with (n := n). omega.
    rewrite H0.
    destruct a; simpl; apply valid_valid.
Qed.

Lemma size_ctx_app : forall (Γ1 Γ2 : Ctx), 
          size_ctx (Γ1 ++ Γ2) = (size_ctx Γ1 + size_ctx Γ2)%nat.
Proof.
  induction Γ1; trivial.
  intros.
  simpl.
  rewrite IHΓ1.
  destruct a; reflexivity.
Qed.

Lemma singleton_length : forall n W, length (singleton n W) = (n + 1)%nat.
Proof.
  induction n; trivial. 
  intros W. simpl. rewrite IHn. reflexivity.
Qed.

Theorem compile_correct : forall b (Γ : Ctx) (f : Var -> bool) (t : bool), 
  get_context b ⊂ Γ ->
  ⟦compile b Γ⟧ ((ctx_to_matrix Γ f) ⊗ (bool_to_matrix t)) = 
  ctx_to_matrix Γ f ⊗ bool_to_matrix (t ⊕ ⌈b | f⌉).
Proof.
  intros b Γ f t H.
  induction b.
  - simpl.
    unfold denote_box.
    unfold denote_db_box. simpl.
    rewrite size_ntensor. simpl. rewrite Nat.mul_1_r, Nat.add_1_r. 
    rewrite fresh_state_ntensor. simpl.
    rewrite pad_nothing.
    rewrite repeat_length. 
    unfold denote_pat.
    remember (size_ctx Γ) as n.
    replace (pat_to_list _) with (σ_{S n}).
    Focus 2.
      clear.
      induction n.
      reflexivity.
      rewrite seq_S.
      rewrite IHn.
      simpl.
      rewrite (repeat_combine (option WType) n 1).
      rewrite ctx_dom_repeat.      
      repeat rewrite seq_shift.  
      rewrite Nat.add_1_r.
      replace (0%nat :: seq 1 (S n)) with (σ_{2+n}) by reflexivity.
      repeat rewrite subst_var_σ_n by omega.
      rewrite (ntensor_pat_to_list_shifted 1%nat) by omega.      
      rewrite (ntensor_pat_to_list_shifted 0%nat) by omega.
      rewrite <- seq_S.
      simpl.
      reflexivity.
    simpl.
    rewrite size_ntensor. simpl. rewrite Nat.add_1_r, Nat.mul_1_r.
    rewrite swap_list_n_id.
    rewrite (repeat_combine (option WType) n 1).
    rewrite ctx_dom_repeat.
    repeat rewrite subst_var_σ_n by omega.
    unfold compose_super.
    show_dimensions.    
    rewrite <- (kron_1_r  _ _ 
       (kron' (2 ^ n) (2 ^ n) 2 2 (ctx_to_matrix Γ f) (bool_to_matrix t))).    
    unfold Var.
    hide_dimensions.
    specialize (apply_U_spec_1 (S n) n 0%nat (ctx_to_matrix Γ f) ('I_1) σx 
                               (bool_to_matrix t)) as appX.
    simpl in *.
    rewrite appX by omega.
    rewrite X_spec.
    rewrite xorb_true_r.
    unfold super.
    Msimpl.
    rewrite Mmult_1_l by (apply WF_kron; subst; auto with wf_db; omega).
    rewrite Mmult_1_r by (apply WF_kron; subst; auto with wf_db; omega).
    reflexivity.
  - simpl.
    unfold denote_box. simpl.
    remember (size_ctx Γ) as n.
    rewrite fresh_state_ntensor. simpl.    
    rewrite size_ntensor. simpl. rewrite Nat.add_1_r, Nat.mul_1_r.
    rewrite (repeat_combine (option WType) n 1).
    rewrite pad_nothing.
    unfold denote_pat. simpl.
    rewrite ctx_dom_repeat.
    rewrite subst_var_σ_n by (rewrite repeat_length; omega).
    rewrite size_ntensor. simpl. rewrite Nat.add_1_r, Nat.mul_1_r.
    replace (pat_to_list _) with (σ_{n}).
    Focus 2.
      clear; simpl.
      induction n; trivial.
      rewrite seq_S.
      rewrite IHn.
      simpl.
      rewrite Nat.add_1_r.
      replace (0%nat :: seq 1 (S n)) with (σ_{2+n}) by reflexivity.
      repeat rewrite subst_var_σ_n by omega.
      rewrite (ntensor_pat_to_list_shifted 1%nat) by omega.      
      rewrite (ntensor_pat_to_list_shifted 0%nat) by omega.
      rewrite <- seq_S.
      simpl.
      reflexivity.
    rewrite repeat_length.
    rewrite <- seq_S.
    rewrite swap_list_n_id.
    rewrite xorb_false_r.
    unfold super.
    Msimpl.
    rewrite Mmult_1_l by (apply WF_kron; subst; auto with wf_db; simpl; omega). 
    rewrite Mmult_1_r by (apply WF_kron; subst; auto with wf_db; simpl; omega). 
    reflexivity.
  - specialize share_to_spec as SS.
    simpl.
    admit.
  - simpl in H.
    specialize (IHb H).
    simpl.
    
    repeat (autounfold with den_db; simpl).
    unfold add_fresh_state. simpl.
    rewrite fresh_state_ntensor. simpl.
    rewrite size_ntensor. simpl. rewrite Nat.add_1_r, Nat.mul_1_r.
    rewrite (repeat_combine (option WType) _ 1%nat).
    rewrite (repeat_combine (option WType) _ 1%nat).
    unfold get_fresh_var. simpl.
    rewrite repeat_length.
    simpl.   
      
    specialize denote_compose as DC. simpl in DC.
    unfold denote_circuit in DC.

    remember (Valid (repeat (Some Qubit) (size_ctx Γ + 1 + 1))) as Γ1'.
    replace (@denote_db_circuit (Tensor (NTensor (size_ctx Γ) Qubit) Qubit) true 0 
                                (S (S (size_ctx Γ)))) with 
            (@denote_db_circuit (Tensor (NTensor (size_ctx Γ) Qubit) Qubit) true 
                                (⟦∅⟧) (⟦Γ1'⟧)) by
            (simpl; subst; repeat rewrite Nat.add_1_r; 
             unfold size_octx; rewrite size_repeat_ctx; reflexivity).
    
    erewrite DC.
    Focus 2.
      apply WT_compile.
      econstructor.
      4: constructor; apply singleton_singleton.
      3: apply (types_pat_fresh_ntensor _ O).
      2: reflexivity.
      apply is_valid_singleton_merge.
      simpl. rewrite repeat_length. omega.
    Focus 3.
      simpl. subst.
      constructor. apply valid_valid.
      instantiate (1 := (singleton (size_ctx Γ) Qubit)).      
      rewrite merge_comm. rewrite <- merge_assoc. 
      rewrite (merge_comm (singleton _ _)). rewrite merge_assoc.
      Search repeat "append".
      replace (singleton (size_ctx Γ)) with
              (singleton (length (repeat (Some Qubit) (size_ctx Γ)))) by 
              (rewrite repeat_length; reflexivity).
      rewrite merge_singleton_append.
      replace (singleton (size_ctx Γ + 1)%nat) with
              (singleton (length (repeat (Some Qubit) (size_ctx Γ)++[Some Qubit])))
        by (rewrite (repeat_combine (option WType) _ 1), repeat_length; reflexivity).
      rewrite merge_singleton_append.
      repeat rewrite (repeat_combine (option WType) _ 1).
      reflexivity.

    Focus 2.
      intros.
      rewrite repeat_length.
      specialize WT_compile as WT.
      unfold Typed_Box in WT.
      type_check.
      11: apply WT.
      11: type_check.
      12: type_check.
      12: type_check.
      12: rewrite merge_assoc; constructor; validate; reflexivity.
      9: reflexivity.
      all: type_check.
      8: apply singleton_singleton.
      4: apply WT.
      3: apply singleton_singleton.
      3: type_check. 
      4: type_check.
      4: type_check.
      2: reflexivity.
      validate.
      validate.
      type_check.



  simpl.  
  rewrite fresh_state_ntensor. simpl.
  repeat rewrite denote_ctx_app. simpl.
  repeat rewrite app_length. 
  Search singleton.
  specialize singleton_size as SS. simpl in SS. repeat rewrite SS. clear SS.
  simpl.
  repeat rewrite size_repeat_ctx.
  rewrite Nat.add_1_r. simpl.
  rewrite repeat_length.
    
  erewrite (size_octx_merge (Valid (repeat (Some Qubit) (size_ctx Γ)))
           (Valid (None :: singleton (size_ctx Γ) Qubit))) by (apply 
     (is_valid_singleton_merge _ _ (S (size_ctx Γ))); rewrite repeat_length; omega).

    unfold size_octx.
    rewrite size_repeat_ctx.
    rewrite merge_nil_l.
    rewrite singleton_length.

    remember ((singleton (size_ctx Γ) Qubit ++
                     repeat (Some Qubit) (size_ctx Γ)) ++ 
                    [Some Qubit]) as Γ1''.
    replace (@denote_db_circuit (Tensor (NTensor (size_ctx Γ) Qubit) Qubit) true 0 
                                (S (S (size_ctx Γ)))) with 
            (@denote_db_circuit (Tensor (NTensor (size_ctx Γ) Qubit) Qubit) true 
                                (⟦∅⟧) (⟦Γ1''⟧)) by
        (simpl; subst; repeat rewrite size_ctx_app; rewrite size_repeat_ctx, 
                     singleton_size; simpl; rewrite Nat.add_1_r; easy).
    
    erewrite DC.
    

    
    
(*
Fixpoint make_reversible {W} (c : Circuit W) (r : reversible c)
  (stack : list ({ W' : WType & Unitary W' & Pat W' })) : Circuit W.
  induction r eqn:Er.
  - induction stack eqn:Es.
    + exact (output p).
    + destruct a as [W' u p']. 
      exact (gate_ p'' ← u @p';
             make_reversible W (output p) r l).
  - exact (let stack' := ((existT2 _ _ Qubit X p1) :: stack) in stack').
    pose stack'.

  :=
  match r with 
  | rev_output p => match stack with 
                   | (exist _ W' (u,p')%core :: stack' => gate_ p'' ← u @p';
                                            make_reversible (rev_output p) r stack'
  | rev_not p c r' => gate_ p' ← X @p;
                     make_reversible c r' stack';
                  
                  
               
 Circuit W. 


Fixpoint reverse {W} (c : Circuit W) (R : reversible c): Circuit W := 
  match R with
  | rev_output p => output p
  | rev_not p1 c => reverse c; 
                   gate_ p ← X 
  | rev_cnot   : forall p1 c, reversible c -> reversible (gate_ p2 ←  CNOT @p1; c)
  | rev_ccnot  : forall p1 c, reversible c -> reversible (gate_ p2 ← CCNOT @p1; c).


Fixpoint reverse {W} (c : Circuit W) (R : reversible c): Circuit W := 
  match R with
  | rev_output p => 
  | rev_not    : forall p1 c, reversible c -> reversible (gate_ p2 ←  X @p1; c)
  | rev_cnot   : forall p1 c, reversible c -> reversible (gate_ p2 ←  CNOT @p1; c)
  | rev_ccnot  : forall p1 c, reversible c -> reversible (gate_ p2 ← CCNOT @p1; c).
  
*)

