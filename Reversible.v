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
Inductive bexp := 
| bT    : bexp 
| bF    : bexp
| b_and : bexp -> bexp -> bexp 
| b_xor : bexp -> bexp -> bexp.

Infix "∧" := b_and (at level 40).
Infix "⊕" := b_xor (at level 40).

Definition b_or (a b : bexp) := (a ∧ b) ⊕ (a ⊕ b).
Definition b_neg (b : bexp)  := (bT ⊕ b).
Definition b_if (g a b : bexp) := (g ∧ a) ⊕ (b_neg g ∧ b).

Infix "∨" := b_or (at level 40).  
Notation "¬ b" := (b_neg b) (at level 10). 
Notation "'bif' g 'then' a 'else' b 'fib'" := (b_if g a b) (at level 90).

Reserved Notation "⌈ b ⌉" (at level 0). 

Fixpoint bexp_to_bool (b : bexp) : bool :=
  match b with
  | bT    => true
  | bF    => false
  | b_and a b => ⌈a⌉ && ⌈b⌉ 
  | b_xor a b => xorb ⌈a⌉ ⌈b⌉
  end 
  where "⌈ b ⌉" := (bexp_to_bool b).  

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

Definition bool_to_matrix (b : bool) : Matrix 2 2 := 
  if b then |1⟩⟨1| else |0⟩⟨0|.

Definition bool_to_matrix' (b : bool) : Matrix 2 2 := fun x y =>
  match x, y with
  | 0, 0 => if b then 0 else 1
  | 1, 1 => if b then 1 else 0
  | _, _ => 0
  end.  
  
Lemma bool_to_matrix_eq : forall b, bool_to_matrix b = bool_to_matrix' b.
Proof. intros. destruct b; simpl; solve_matrix. Qed.

Lemma WF_bool_to_matrix : forall b, WF_Matrix 2 2 (bool_to_matrix b).
Proof. destruct b; simpl; show_wf. Qed.

(******************)
(** Discard Test **) 
(******************)

Definition new_disc_test : Box One Bit :=
  box_ () ⇒ 
  gate_ x    ← new0 @();
  gate_ y    ← new0 @();
  gate_ z    ← new1 @();
  gate_ ()   ← discard @x;
  gate_ ()   ← discard @y;
  output z.
Lemma typed_test : Typed_Box new_disc_test.
Proof. type_check.  Qed.

Lemma test_spec : ⟦new_disc_test⟧ I1 = |1⟩⟨1|. 
Proof.
  unfold denote; simpl.
  unfold denote_box. simpl.
  repeat (autounfold with den_db; simpl). 
  Msimpl.
  solve_matrix.
Qed.

(* ---------------------------------------*)
(*---------Classical Circuit Specs -------*)
(* ---------------------------------------*)

Lemma NOT_spec : forall (b : bool), ⟦boxed_gate X⟧ (bool_to_matrix b) = bool_to_matrix (negb b).
Proof. destruct b;
       repeat (autounfold with den_db; simpl);
       assoc_least; Msimpl; reflexivity.
Qed.

Lemma XOR_spec : forall (b1 b2 : bool), 
    ⟦XOR⟧ (bool_to_matrix b1 ⊗ bool_to_matrix b2)%M  = bool_to_matrix (xorb b1 b2).
Proof.  intros b1 b2. 
        specialize (WF_bool_to_matrix b1) as WFb1.
        specialize (WF_bool_to_matrix b2) as WFb2.
        repeat rewrite bool_to_matrix_eq in *.
        unfold bool_to_matrix' in *.
        repeat (autounfold with den_db; simpl); Msimpl.
        solve_matrix;
        destruct b1, b2; simpl; clra.
Qed.

Lemma CCNOT_spec : forall (b1 b2 : bool), 
    denote_box true CCNOT (bool_to_matrix b1 ⊗ bool_to_matrix b2 ⊗ |0⟩⟨0|)%M  
      = (bool_to_matrix b1 ⊗ bool_to_matrix b2 ⊗ bool_to_matrix (andb b1 b2))%M.
Proof.
  intros b1 b2.
  specialize (WF_bool_to_matrix b1) as WFb1.
  specialize (WF_bool_to_matrix b2) as WFb2.
  repeat rewrite bool_to_matrix_eq in *.
  unfold bool_to_matrix' in *.
  repeat (autounfold with den_db; simpl); Msimpl.
  solve_matrix. 
  all: destruct b1, b2; simpl; try clra.
Qed.

Lemma AND_spec : forall (b1 b2 : bool), 
    ⟦AND⟧ (bool_to_matrix b1 ⊗ bool_to_matrix b2)%M  = bool_to_matrix (andb b1 b2).
Proof. 
  intros b1 b2. 
  specialize (WF_bool_to_matrix b1) as WFb1.
  specialize (WF_bool_to_matrix b2) as WFb2.
  repeat rewrite bool_to_matrix_eq in *.
  repeat (autounfold with den_db; simpl).   
  Msimpl.
  unfold bool_to_matrix'.
  solve_matrix.
  all: destruct b1, b2; simpl; Csimpl; try reflexivity.
Qed.
  
Lemma OR_spec : forall (b1 b2 : bool), 
    ⟦OR⟧ (bool_to_matrix b1 ⊗ bool_to_matrix b2)%M  = bool_to_matrix (orb b1 b2).
Proof. 
  intros b1 b2. 
  specialize (WF_bool_to_matrix b1) as WFb1.
  specialize (WF_bool_to_matrix b2) as WFb2.
  repeat rewrite bool_to_matrix_eq in *.
  repeat (autounfold with den_db; simpl).   
  Msimpl.
  unfold bool_to_matrix'.
  solve_matrix.
  all: destruct b1, b2; simpl; Csimpl; try reflexivity.
Qed.


(* ---------------------------------------*)

Open Scope matrix_scope.
Lemma denote_db_pad : forall Γ0 Γ pad n w (c : Circuit w) (ρ1 : Square (2^n)) (ρ2 : Square (2^pad)),
  ⟦Γ0⟧ = pad ->
  ⟦Γ⟧ = n ->
  ⟨ Γ0 | Γ ⊩ c ⟩ (ρ1 ⊗ ρ2) = ⟨ ∅ | Γ ⊩ c ⟩ ρ1 ⊗ ρ2.
Admitted.


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

    setoid_rewrite (denote_db_pad (Valid [Some Qubit]) ∅ 1 0); trivial.

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

    setoid_rewrite (denote_db_pad (Valid [Some Qubit]) ∅ 1 0); trivial.

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

(* -----------------------------------------*)
(*--------- Reversible Circuit Specs -------*)
(* -----------------------------------------*)

Open Scope matrix_scope.

Lemma R_TRUE_spec : forall z, ⟦R_TRUE⟧ (bool_to_matrix z) = bool_to_matrix (xorb true z). 
Proof. 
  intros z. 
  specialize (WF_bool_to_matrix z) as WF.
  repeat rewrite bool_to_matrix_eq in *.
  repeat (autounfold with den_db; simpl).   
  Msimpl.
  solve_matrix.
  all: destruct z; simpl; try clra.
Qed.

Lemma R_FALSE_spec : forall z, 
    ⟦R_FALSE⟧ (bool_to_matrix z) = bool_to_matrix (xorb false z). 
Proof.
  intros z. 
  specialize (WF_bool_to_matrix z) as WF.
  repeat rewrite bool_to_matrix_eq in *.
  repeat (autounfold with den_db; simpl).   
  Msimpl.
  solve_matrix.
  all: destruct z; simpl; try clra.
Qed.

Lemma R_NOT_spec : forall (x z : bool), 
  ⟦R_NOT⟧ (bool_to_matrix x ⊗ bool_to_matrix z) = 
  bool_to_matrix x ⊗ bool_to_matrix (xorb (negb x) z).
Proof.
  intros x z.
  specialize (WF_bool_to_matrix x) as WFx.
  specialize (WF_bool_to_matrix z) as WFz.
  repeat rewrite bool_to_matrix_eq in *.
  repeat (autounfold with den_db; simpl); Msimpl.
  solve_matrix. 
  all: destruct x, z; simpl; try clra.
Qed.

Lemma R_XOR_spec : forall (x y z : bool), 
    ⟦R_XOR⟧ (bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix z)  = 
    bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix (xorb (xorb x y) z).
Proof.  
  intros x y z.
  specialize (WF_bool_to_matrix x) as WFx.
  specialize (WF_bool_to_matrix y) as WFy.
  specialize (WF_bool_to_matrix z) as WFz.
  repeat rewrite bool_to_matrix_eq in *.
  repeat (autounfold with den_db; simpl); Msimpl.
  solve_matrix. 
  all: destruct x, y, z; simpl; try clra. 
Qed.

Lemma R_AND_spec : forall (x y z : bool), 
    ⟦R_AND⟧ (bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix z)  = 
    bool_to_matrix x ⊗ bool_to_matrix y ⊗ bool_to_matrix (xorb (andb x y) z).
Proof. 
  intros x y z.
  specialize (WF_bool_to_matrix x) as WFx.
  specialize (WF_bool_to_matrix y) as WFy.
  specialize (WF_bool_to_matrix z) as WFz.
  repeat rewrite bool_to_matrix_eq in *.
  repeat (autounfold with den_db; simpl); Msimpl.
  solve_matrix. 
  all: destruct x, y, z; simpl; try clra. 
Qed.
  
(* --------------------------------*)
(* Reversible bexps with variables *)
(* --------------------------------*)

Inductive rbexp := 
| rb_t   : rbexp
| rb_f   : rbexp
| rb_var : Var -> rbexp
| rb_and : rbexp -> rbexp -> rbexp 
| rb_xor : rbexp -> rbexp -> rbexp.

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
  | rb_and b1 b2  => get_context b1 ∪ get_context b2 
  | rb_xor b1 b2  => get_context b1 ∪ get_context b2 
  end.

AND_R

(* stack for ancillae? *)
Fixpoint forward_compile (z : Var) (b : rbexp) : 
  Circuit (S (⟦get_context b⟧) ⨂ Qubit).

(* forward compile in reverse, excluding gates that target the output qubit *)
Fixpoint backward_compile (z : Var) (b : rbexp) : 
  Circuit (S (⟦get_context b⟧) ⨂ Qubit).





Inductive reversible {W} : Circuit W -> Set := 
| rev_output : forall p, reversible (output p)
| rev_not    : forall p1 c, reversible c -> reversible (gate_ p2 ←  X @p1; c)
| rev_cnot   : forall p1 c, reversible c -> reversible (gate_ p2 ←  CNOT @p1; c)
| rev_ccnot  : forall p1 c, reversible c -> reversible (gate_ p2 ← CCNOT @p1; c).

Definition test : forall (n : nat), (n = n)%nat * (n = n)%nat :=
  fun x => (eq_refl, eq_refl)%core.

Print test.

Definition test2 : { n : nat & n = n & True }%nat.
  exists 1%nat. reflexivity. exact I. 
Defined.

Print test2.

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
  


