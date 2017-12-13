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

Lemma b_or_to_bool : forall a b, ⌈a ∨ b⌉ = ⌈ a ⌉ || ⌈ b ⌉.
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


(* ---------------------------------------*)
(*---------Classical Circuit Specs -------*)

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
        repeat (autounfold with den_db; simpl); assoc_least; Msimpl;
        solve_matrix;
        destruct b1, b2; simpl; clra.
Qed.

Lemma AND_spec : forall (b1 b2 : bool), 
    ⟦AND⟧ (bool_to_matrix b1 ⊗ bool_to_matrix b2)%M  = bool_to_matrix (andb b1 b2).
Proof. 
  intros b1 b2. 
  specialize (WF_bool_to_matrix b1) as WFb1.
  specialize (WF_bool_to_matrix b2) as WFb2.
  repeat rewrite bool_to_matrix_eq in *.
  repeat (autounfold with den_db; simpl); assoc_least; Msimpl.
  repeat (try rewrite Mmult_plus_distr_l; try rewrite Mmult_plus_distr_r).
  unfold bool_to_matrix' in *.
  solve_matrix.
  
  

(* ---------------------------------------*)

Lemma bexp_to_circ_correct : forall b, 
  ⟦bexp_to_circ b⟧ I1 = bool_to_matrix ⌈b⌉.
Proof.
  induction b.
  + repeat (autounfold with den_db; simpl). solve_matrix.
  + repeat (autounfold with den_db; simpl). solve_matrix.
  + repeat (autounfold with den_db; simpl).

    erewrite denote_compose with (Γ := ∅) (Γ1 := ∅) (Γ1' := ∅);
      [ | apply unbox_typing; [type_check | apply WT_bexp_to_circ]
      | split; [validate | monoid]
      | repeat (type_check; try apply WT_bexp_to_circ)
      | auto
      | replace (remove_OCtx ∅ (st_{0})) with (st_{0})
          by (unfold remove_OCtx; auto);
         rewrite fresh_pat_eq'; auto
      ]. 

       (* Apply IHb1 *)
       rewrite denote_db_unbox in IHb1.
       simpl. 
       unfold compose_super. 
       rewrite IHb1.

    erewrite denote_compose with (Γ := Valid [Some Qubit]);
      [ | apply unbox_typing; [type_check | apply WT_bexp_to_circ]
      | split; [validate | monoid]
      | 
      | auto
      | replace (remove_OCtx ∅ (st_{1})) with (st_{1})
          by (unfold remove_OCtx; auto);
         rewrite fresh_pat_eq'; auto
      ]. 

       2: rewrite merge_nil_l; apply valid_valid. 
       
       Focus 2.
       intros.
       inversion H.
       unfold fresh_pat. simpl.
       assert(TP0 : Types_Pat (Valid [Some Qubit]) (qubit O)) by repeat constructor. 
       type_check.

       simpl.
       unfold compose_super.

Lemma denote_db_pad1 : forall W (b : Box One W) (A B : Square (2^⟦W⟧)), ⟦b⟧ I1 = A -> 
      denote_db_circuit 1 0 (hoas_to_db (unbox b ()) (st_{1})) B = (A ⊗ B)%M.
Proof.
  intros.
  destruct b.
  induction (c ()) eqn:Ceq.
  + simpl. rewrite Ceq. simpl. 
    autounfold with den_db.
Admitted.

  eapply denote_db_pad1 in IHb2.     
  rewrite IHb2.
  repeat (autounfold with den_db; simpl).
  specialize (WF_bool_to_matrix ⌈b1⌉) as WFb1.
  specialize (WF_bool_to_matrix ⌈b2⌉) as WFb2.
  Msimpl.
  destruct ⌈b1⌉, ⌈b2⌉; simpl.
  - assoc_least.
    simpl.
    repeat (try rewrite Mmult_plus_distr_l; try rewrite Mmult_plus_distr_r).
    assoc_least.
    solve_matrix.



Lemma denote_db_pad : forall W (pad n : nat) (b : Box One W) (A B : Square ⟦W⟧), 
           denote_db_circuit pad n (hoas_to_db (unbox b ()) (st_{pad})) = 
           


           denote_db_circuit 0 0 (hoas_to_db (unbox b ()) (st_{ 0})) I2 = A ->
           denote_db_circuit 1 0 C 

       replace (denote_db_circuit 1 0 (hoas_to_db (unbox (bexp_to_circ b2) ()) (st_{ 1}))) with (bool_to_matrix ⌈b2⌉).
       repeat (autounfold with den_db; simpl).
       
       Msimpl.
       rewrite IHb2.

       rewrite denote_db_unbox in IHb2.


       2: reflexivity.
       Focus 2.
       replace (remove_OCtx ∅ (st_{1})) with (st_{1})
          by (unfold remove_OCtx; auto);
         rewrite fresh_pat_eq'; auto.

       repeat (autounfold with den_db; simpl).
       simpl.
       

       Focus 2.
       constructor.
       2: rewrite merge_nil_l; reflexivity.
       
 
       Focus 3.
       intros.
       rewrite H.
       subst.
       type_check.


       rewrite IHb2.


    simpl.
    repeat (autounfold with den_db; simpl).

    erewrite denote_compose with (Γ := ∅) (Γ1 := Valid [Some Qubit]) 
                                 (Γ1' := Valid [Some Qubit]);
      [ | apply unbox_typing; [type_check | apply WT_bexp_to_circ]
      | split; [validate | monoid]
      | 
      | auto
      | ].
    
 


    erewrite denote_compose with (Γ := ∅) (Γ1 := ∅) (Γ1' := ∅);
      [ | apply unbox_typing; [type_check |]
      | split; [validate | monoid]
      | 
      | auto
      | replace (remove_OCtx ∅ (st_{0})) with (st_{0})
          by (unfold remove_OCtx; auto);
         rewrite fresh_pat_eq'; auto
      ].
    all: type_check; try apply WT_box_to_circ; type_check.
    erewrite denote_compose with (Γ := ∅) (Γ1 := ∅) (Γ1' := ∅);
      [ | apply unbox_typing; [type_check |]
      | split; [validate | monoid]
      | 
      | auto
      | replace (remove_OCtx ∅ (st_{0})) with (st_{0})
          by (unfold remove_OCtx; auto);
         rewrite fresh_pat_eq'; auto
      ].
    all: type_check; try apply WT_box_to_circ; type_check.

    
    Focus 2.

    simpl.


    simpl.
    idtac.

(* ---------------------------------------*)

Inductive reversible {W} : Circuit W -> Set := 
| rev_output : forall p, reversible (output p)
| rev_not    : forall p1 c, reversible c -> reversible (gate_ p2 ←  X @p1; c)
| rev_cnot   : forall p1 c, reversible c -> reversible (gate_ p2 ←  CNOT @p1; c)
| rev_ccnot  : forall p1 c, reversible c -> reversible (gate_ p2 ← CCNOT @p1; c).

Fixpoint reverse {W} (c : Circuit W) (R : reversible c): Circuit W := 
  match R with
  | rev_output p => 
  | rev_not    : forall p1 c, reversible c -> reversible (gate_ p2 ←  X @p1; c)
  | rev_cnot   : forall p1 c, reversible c -> reversible (gate_ p2 ←  CNOT @p1; c)
  | rev_ccnot  : forall p1 c, reversible c -> reversible (gate_ p2 ← CCNOT @p1; c).
  


