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


(* retrieves the nth wire in a list *)
(* get_wire implements the following function, which I can't convince Coq to accept:
Fixpoint get_wire {W m} (n : nat) (ps : Pat (m ⨂ W)) (default : Pat W) : Pat W :=
  match ps with
  | unit    => default 
  | (p,ps') => match n with 
              | O => p
              | S n' => get_wire n' ps' default 
              end
  end.
*)

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

(* Replaces the nth wire in a pattern with the given wire *)
(* failed definition 
Fixpoint replace_wire {W m} (p : Pat W) (n : nat) (ps : Pat (m ⨂ W)) : (Pat (m ⨂ W)) :=
  match ps with
  | unit      => unit 
  | (p',ps')  => match n with 
               | O => p 
               | S n' => (p',replace_wire p n' ps')
                end
  end.*)

Fixpoint replace_wire {W m} (p : Pat W) (n : nat) (ps : Pat (m ⨂ W)) : (Pat (m ⨂ W)).
destruct m as [|m'].
+ exact ps.
+ dependent destruction ps.
    destruct n as [|n'].
  - exact (p, ps2).
  - exact (ps1, replace_wire W m' p n' ps2).
Defined.

(*
Fixpoint position_of (v : Var) (Γ : Ctx) : nat := 
  match Γ with
  | []           => 0 
  | None :: Γ'   => position_of (v - 1)%nat  Γ'
  | Some w :: Γ' => S (position_of (v - 1)%nat Γ')
  end.
*)

Fixpoint position_of (v : Var) (Γ : Ctx) : nat := 
  match v with
  | 0     => 0
  | S v'  => match Γ with
            | [] => 0
            | None :: Γ'   => position_of v'  Γ'
            | Some w :: Γ' => S (position_of v' Γ')
            end
  end.

Fixpoint compile (b : rbexp) (Γ : Ctx) : Box (S (⟦Γ⟧) ⨂ Qubit) (S (⟦Γ⟧) ⨂ Qubit) :=
  box_ tqs ⇒
  let_ (target, qs) ← output tqs;
  match b with
  | rb_t          => let_ target ← unbox R_TRUE target;
                    output (target,qs)
  | rb_f          => let_ target ← unbox R_FALSE target;
                    output (target,qs)
  | rb_var v      => let n := position_of v Γ in 
                    let q := get_wire n qs target in 
                    gate_ (q',target) ← CNOT @(q,target);
                    let qs' := replace_wire q' n qs in
                    output (target,qs')
  | rb_and b1 b2  => gate_ q1            ← init0 @();
                    let_ (q1,qs)        ← unbox (compile b1 Γ) (q1,qs);
                    gate_ q2            ← init0 @();
                    let_ (q2,qs)        ← unbox (compile b2 Γ) (q2,qs);
                    let_ (target,q1,q2) ← unbox R_AND (target,q1,q2);
                    let_ (q2,qs)        ← unbox (compile b2 Γ) (q2,qs);
                    gate_ ()            ← assert0 @q2;
                    let_ (q1,qs)        ← unbox (compile b2 Γ) (q1,qs);
                    gate_ ()            ← assert0 @q1;
                    output (target,qs)
  | rb_xor b1 b2  => gate_ q1            ← init0 @();
                    let_ (q1,qs)        ← unbox (compile b1 Γ) (q1,qs);
                    gate_ q2            ← init0 @();
                    let_ (q2,qs)        ← unbox (compile b2 Γ) (q2,qs);
                    let_ (target,q1,q2) ← unbox R_XOR (target,q1,q2);
                    let_ (q2,qs)        ← unbox (compile b2 Γ) (q2,qs);
                    gate_ ()            ← assert0 @q2;
                    let_ (q1,qs)        ← unbox (compile b2 Γ) (q1,qs);
                    gate_ ()            ← assert0 @q1;
                    output (target,qs)
  end.

Lemma merge_intersection : forall Γ1 Γ2 Γ3 Γ4,
  is_valid (Γ1 ⋓ Γ2) ->
  (Γ1 ⋓ Γ2) = (Γ3 ⋓ Γ4) ->
  { Γ13 : OCtx & { Γ14 : OCtx & { Γ23 : OCtx & { Γ24 : OCtx &
  Γ1 == Γ13 ∙ Γ14 /\ Γ2 == Γ23 ∙ Γ24 /\ Γ3 == Γ13 ∙ Γ23 /\ Γ4 == Γ14 ∙ Γ24}}}}.
Proof.
  intros Γ1 Γ2 Γ3 Γ4 V M.  
  assert (H : (Γ1 ⋓ Γ2) == Γ3 ∙ Γ4). constructor; assumption. 
  clear M V.
  apply merge_fun_ind in H.
  dependent induction H. 
  - exists ∅, Γ1, ∅, Γ2. repeat split; type_check. 3: assumption. 
    destruct Γ1. rewrite merge_I_l in x. inversion x. apply valid_valid.
    destruct Γ2. rewrite merge_I_r in x. inversion x. apply valid_valid.
  - exists Γ1, ∅, Γ2, ∅. repeat split; type_check. 3: assumption. 
    destruct Γ1. rewrite merge_I_l in x. inversion x. apply valid_valid.
    destruct Γ2. rewrite merge_I_r in x. inversion x. apply valid_valid.
  - rename Γ3 into Γ4. rename Γ0 into Γ3. rename o1 into o3. rename o2 into o4.
    destruct Γ1 as [|Γ1]. inversion x. 
    destruct Γ2 as [|Γ2]. inversion x.
    destruct Γ1 as [|o1 Γ1], Γ2 as [|o2 Γ2]. 
    + inversion x.
    + rewrite merge_nil_l in x. inversion x. subst.
      exists ∅, ∅, (Valid (o3 :: Γ3)), (Valid (o4 :: Γ4)).
      repeat split; type_check.
      apply merge_ind_fun.
      constructor; assumption.
    + rewrite merge_nil_r in x. inversion x. subst.
      exists (Valid (o3 :: Γ3)), (Valid (o4 :: Γ4)), ∅, ∅.
      repeat split; type_check.
      apply merge_ind_fun.
      constructor; assumption.
    + assert (M12 : (Valid (o :: Γ) == Valid (o1 :: Γ1) ∙ Valid (o2 :: Γ2))).
      constructor. apply valid_valid. assumption.
      clear x.
      apply merge_fun_ind in M12.
      inversion M12. subst. clear M12.
      destruct (IHmerge_ind (Valid Γ1) (Valid Γ2)) as [Γ13 [Γ14 [Γ23 [Γ24 pf]]]].
      apply merge_ind_fun in H7 as [V M]. assumption.
      destruct pf as [pf1 [pf2 [pf3 pf4]]].
      destruct Γ13 as [|Γ13]. clear -pf1. invalid_contradiction.
      destruct Γ14 as [|Γ14]. clear -pf1. invalid_contradiction.
      destruct Γ23 as [|Γ23]. clear -pf2. invalid_contradiction.
      destruct Γ24 as [|Γ24]. clear -pf2. invalid_contradiction.
      inversion m; subst; inversion H3; subst.
      Transparent merge.
      * exists (Valid (None :: Γ13)), (Valid (None :: Γ14)), 
          (Valid (None :: Γ23)), (Valid (None :: Γ24)).
        repeat split; type_check. 
        rewrite <- pf_merge2. reflexivity.
        rewrite <- pf_merge1. reflexivity.
        rewrite <- pf_merge0. reflexivity.
        rewrite <- pf_merge. reflexivity.
      * exists (Valid (Some w :: Γ13)), (Valid (None :: Γ14)), 
          (Valid (None :: Γ23)), (Valid (None :: Γ24)).
        repeat split; type_check. 
        rewrite <- pf_merge2. reflexivity.
        rewrite <- pf_merge1. reflexivity.
        rewrite <- pf_merge0. reflexivity.
        rewrite <- pf_merge. reflexivity.
      * exists (Valid (None :: Γ13)), (Valid (None :: Γ14)), 
          (Valid (Some w :: Γ23)), (Valid (None :: Γ24)).
        repeat split; type_check. 
        rewrite <- pf_merge2. reflexivity.
        rewrite <- pf_merge1. reflexivity.
        rewrite <- pf_merge0. reflexivity.
        rewrite <- pf_merge. reflexivity.
      * exists (Valid (None :: Γ13)), (Valid (Some w :: Γ14)), 
          (Valid (None :: Γ23)), (Valid (None :: Γ24)).
        repeat split; type_check. 
        rewrite <- pf_merge2. reflexivity.
        rewrite <- pf_merge1. reflexivity.
        rewrite <- pf_merge0. reflexivity.
        rewrite <- pf_merge. reflexivity.
      * exists (Valid (None :: Γ13)), (Valid (None :: Γ14)), 
          (Valid (None :: Γ23)), (Valid (Some w :: Γ24)).
        repeat split; type_check. 
        rewrite <- pf_merge2. reflexivity.
        rewrite <- pf_merge1. reflexivity.
        rewrite <- pf_merge0. reflexivity.
        rewrite <- pf_merge. reflexivity.
      Opaque merge.
Qed.        

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

(*
Lemma singleton_merge : forall Γ Γ1 Γ2 v W, SingletonOCtx v W Γ ->
                                       Γ == Γ1 ∙ Γ2 ->
                                       (Γ1 = ∅) \/ (Γ2 = ∅).
Proof.
  intros Γ Γ1 Γ2 v W H H0.
  destruct Γ as [|Γ]. inversion H.
  induction Γ.
  - destruct H0.
    symmetry in pf_merge.
    apply merge_nil_inversion in pf_merge as [E1 E2].
    left. assumption.
  - destruct a.
    inversion H. subst.
    inversion H2. subst.
    destruct Γ1 as [|Γ1]. invalid_contradiction. destruct Γ1 as [|o1 Γ1]. 
    left. reflexivity.
    destruct Γ2 as [|Γ2]. invalid_contradiction. destruct Γ2 as [|o2 Γ2]. 
    right. reflexivity.
   (* this should be a contradiction. Sadly, we have empty contexts that aren't ∅ *)
Search empty_Ctx.
    destruct H0.
    invalid_contradiction.
    simpl in H0. inv
    destruct Γ2
*)

Lemma replace_wire_WT : forall m n W (q default : Pat W) (p : Pat (m ⨂ W)) Γ0 Γq Γq',
  (n < m)%nat ->
  (Γ0 ⋓ Γq) ⊢ p :Pat ->
  Γq ⊢ get_wire n p default :Pat ->
  Γq' ⊢ q :Pat ->
  is_valid (Γ0 ⋓ Γq') ->
  (Γ0 ⋓ Γq') ⊢ replace_wire q n p :Pat.
Proof.
  intros m n.
  generalize dependent m.
  induction n as [|n' IH].
  + intros m W q default p Γ0 Γq Γq' H H0 H1 H2 H3.
    destruct m as [|m']. omega.
    dependent destruction p.
    simpl in *.
    unfold solution_left in *.
    unfold eq_rect_r in *.
    simpl in *.
    dependent destruction H0.
    econstructor.
    assumption.
    2: apply H2.
    rewrite merge_comm. reflexivity. (* ? *)
    admit.
  + intros m W q default p Γ0 Γq Γq' H H0 H1 H2 H3.
    destruct m as [|m']. omega.
    dependent destruction p.
    dependent destruction H0.
    
    specialize (merge_intersection _ _ _ _ i e) as MI.
    destruct MI as [Γ01 [Γ02 [Γ1q [Γ2q pf]]]].
    destruct pf as [pf0 [pfq [pf1 pf2]]].
    
    simpl in *.
    unfold solution_left in *.
    unfold eq_rect_r in *.
    simpl in *.
    econstructor.
    assumption.
    2: apply H0_.

    Focus 2. eapply IH.
             omega.
             3: apply H2.
             2: apply H1.
Admitted.

Lemma position_of_lt : forall Γ v w, nth v Γ None = Some w  -> 
                              (position_of v Γ < denote_Ctx Γ)%nat.
Proof.
  induction Γ.
  - intros v w H.
    simpl in H.
    destruct v; inversion H.
  - intros v w H.
    destruct a.
    + destruct v. 
      * simpl in *.
        omega.
      * simpl in *.
        apply IHΓ in H.
        omega.
    + destruct v. 
      * simpl in *. 
        inversion H.
      * simpl.
        apply (IHΓ v w).
        apply H.
Qed.    
    
Lemma WT_compile : forall (b : rbexp) (Γ Γb Γo : Ctx), 
    Γb = (get_context b) ->
    Valid Γ = Γb ⋓ Γo -> 
    Typed_Box (compile b Γ).
Proof.
  induction b.
  - type_check.
  - type_check.
  - unfold Typed_Box.
    intros Γ Γb Γo H H0 Γ0 p H1.
    dependent destruction p.
    dependent destruction H1.
    specialize (get_wire_WT Γ2 (denote_Ctx Γ) (position_of v Γ) p1) 
      as [Γ1' [Γ2' GWT]].
    apply position_of_lt with (w:=Qubit). admit. (* trivial *)
    apply H1_0.
    type_check.
    clear -H t H1_0 pf_valid0 H0.
    eapply replace_wire_WT.
    apply position_of_lt with (w:=Qubit). admit. (* trivial *)
    rewrite merge_comm. apply H1_0.
    apply t.
    assumption.
    validate.
  - 


  intros Γ1 Γ2 Γ3 Γ4 H.
  remember (Γ1 ⋓ Γ2) as Γ.
  assert (V : is_valid Γ). type_check. 
  apply merge_fun_ind in H.
  induction H. 
  - exists ∅, Γ1, ∅, Γ2. repeat split; type_check. 3: assumption. 
    destruct Γ1. rewrite merge_I_l in HeqΓ. rewrite HeqΓ in V. apply not_valid in V.
    contradiction. apply valid_valid.
    destruct Γ2. rewrite merge_I_r in HeqΓ. rewrite HeqΓ in V. apply not_valid in V.
    contradiction. apply valid_valid.
  - exists Γ1, ∅, Γ2, ∅. repeat split; type_check. 3: assumption. 
    destruct Γ1. rewrite merge_I_l in HeqΓ. rewrite HeqΓ in V. apply not_valid in V.
    contradiction. apply valid_valid.
    destruct Γ2. rewrite merge_I_r in HeqΓ. rewrite HeqΓ in V. apply not_valid in V.
    contradiction. apply valid_valid.
  - 
  

Lemma Ctx_minus : SingletonOCtx v2 Qubit Γ2 ->
                  SingletonOCtx v2 Qubit Γ3 ->
                  Γ1 == Γ3 ⋓ (Γ4 - Γ2)

  Γ1 ⋓ Γ2 == Γ3 ∙ Γ4, 
    



Lemma merge_intersection : forall Γ1 Γ2 Γ3 Γ4,
  (Γ1 ⋓ Γ2) == Γ3 ∙ Γ4 ->
  { Γ13 : OCtx & {Γ14 : OCtx & {Γ23 :OCtx & {Γ24 : OCtx &
  Γ1 == Γ13 ∙ Γ14 /\ Γ2 == Γ23 ∙ Γ24 /\ Γ3 == Γ13 ∙ Γ23 /\ Γ4 == Γ14 ∙ Γ24}}}}.
Proof.
  intros Γ1 Γ2 Γ3 Γ4 H.
  apply merge_fun_ind in H.
  induction H.


    Focus 2. eapply IH.
             omega.
             3: apply H2.
             3: apply H3.
             2: apply H1.
             (* this is false (Γ0 ⋓ Γq - Γ1) types p2 *)

             2: apply H2_.
    4: apply H2_0.
    5: apply H4.
    4: apply H3.
  


Lemma replace_WT : forall m n W (q default : Pat W) (p : Pat (m ⨂ W)) Γ Γ' Γ0 Γq Γq',
  (n < m)%nat ->
  Γ == Γ0 ∙ Γq ->
  Γ' == Γ0 ∙ Γq' ->
  Γ ⊢ p :Pat ->
  Γq ⊢ get_wire n p default :Pat ->
  Γq' ⊢ q :Pat ->
  Γ' ⊢ replace_wire q n p :Pat.
Proof.
  intros m n.
  generalize dependent m.
  induction n as [|n' IH].
  + intros m W q default p Γ Γ' Γ0 Γq Γq' H H0 H1 H2 H3 H4.
    destruct m as [|m']. omega.
    dependent destruction p.
    simpl in *.
    unfold solution_left in *.
    unfold eq_rect_r in *.
    simpl in *.
    dependent destruction H2.
    econstructor.
    destruct H1. assumption.
    destruct H1. rewrite merge_comm. apply pf_merge.
    assumption.
    admit.
  + intros m W q default p Γ Γ' Γ0 Γq Γq' H H0 H1 H2 H3 H4.
    destruct m as [|m']. omega.
    dependent destruction p.
    dependent destruction H2.
    simpl in *.
    unfold solution_left in *.
    unfold eq_rect_r in *.
    simpl in *.
    econstructor.
    type_check.
    2: apply H2_.
    destruct H0, H1.
    rewrite pf_merge0.
    rewrite <- pf_merge.
    3: eapply IH.
    3: omega.
    2: apply H2_.
    4: apply H2_0.
    5: apply H4.
    4: apply H3.
    
    
intros p H2 H3.
    

    type_check.

Ltac type_check_once :=
  intros **;
   try match goal with
       | |- Typed_Box ?c => unfold Typed_Box in *; try unfold c
       end; intros **; simpl in *; subst; invert_patterns;
   repeat
    match goal with
    | b:bool |- _ => destruct b
    | H:_ == _ ∙ _ |- _ => destruct H
    | |- _ ⊢ _ :Circ => econstructor; type_check_once
    | |- _ ⊢ if ?b then _ else _ :Circ => destruct b; type_check_once
    | |- _ ⊢ _ :Circ => eapply compose_typing; type_check_once
    | H:forall a b, _ ⊢ _ :Pat -> _ ⊢ _ :Circ
      |- _ ⊢ _ :Circ => apply H; type_check_once
    | H:_ ⊢ ?p :Pat |- _ ⊢ ?p :Pat => exact H
    | H:?Γ1 ⊢ ?p :Pat |- ?Γ2 ⊢ ?p :Pat => replace Γ2 with Γ1; [ exact H | monoid ]
    | |- _ ⊢ _ :Pat => econstructor; type_check_once
    | |- ?Γ == ?Γ1 ∙ ?Γ2 => has_evars (Γ1 ⋓ Γ2 ⋓ Γ)
    | |- _ == _ ∙ _ => solve_merge
    end;
   match goal with
   | |- is_valid ?Γ => tryif has_evar Γ then idtac else (idtac; validate) 
   | |- ?G => tryif has_evars G then idtac else (idtac; monoid) 
   end

type_check_once.
    Focus 3. Search SingletonCtx.

    specialize (get_wire_WT) as GWT.    
    type_check.   
    Focus 3.
    edestruct GWT as [Γ1' [Γ2' E GMT]] .
    Focus 3. 
    apply GMT.

replace (get_wire (S n) (p1, p2)) with (get_wire n p2).

 simpl.
  



  generalize dependent Γ'.
  generalize dependent Γ.  
  induction m. intros; omega.
  intros Γ Γ' v default p H H0.
  destruct (position_of v Γ) eqn:P.
  - dependent destruction p.
    dependent destruction H0.
    simpl.
    unfold solution_left.
    unfold eq_rect_r.
    simpl.
    exists Γ1, Γ2. type_check. assumption.
  - dependent destruction p.    
    dependent destruction H0.
    
    edestruct IHm.
    

    
assert (GWS : forall n p1 p2 default, get_wire (S n) (p1,p2) default = 
                                 get_wire n p2 default).

    simpl.
    apply IHm.

    replace (get_wire (S n) (p1, p2) default) with
        (get_wire n p2 default) by reflexivity.
    simpl.

    replace (Tensor Qubit (m ⨂ Qubit)) with (S m ⨂ Qubit) in p2.
    assert (p2' : Pat (S m ⨂ Qubit)) by apply p2. clear p2.



Lemma get_wire_WT : forall Γ Γ' m v default (p : Pat (m ⨂ Qubit)), 
  (⟦Γ⟧ <= ⟦Γ'⟧)%nat   ->
  Γ' <> ∅ ->
  Γ' ⊢ p :Pat ->
  {Γ1 : OCtx & {Γ2 : OCtx & Γ' == Γ1 ∙ Γ2 &
                     Γ1  ⊢ get_wire (position_of v Γ) p default :Pat}}.
Proof.
  intros Γ Γ' m.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction m as [|m'].
  - intros Γ Γ' v default p E NZ T.
  simpl in p.
  dependent destruction p.
  dependent destruction T.
  contradict NZ; reflexivity.
  - intros Γ Γ' v default p E NZ T.
    clear NZ.
    dependent destruction p.
    dependent destruction T.
    simpl.
    unfold solution_left.
    unfold eq_rect_r.
    unfold eq_rect.
    simpl.
    destruct v.
    simpl.
    exists Γ1. exists Γ2. type_check. assumption.
    destruct Γ.
    simpl.
    exists Γ1. exists Γ2. type_check. assumption.
    destruct o.
    simpl.

    edestruct IHm'.
    Focus 4.
    destruct s.
    exists x. exists x0. apply v0. apply t.
    apply t.

    apply IHm'.
    simpl in E. simpl. omega.
    dependent destruction p1.
    dependent destruction T1.
    apply singleton_equiv in s.
    subst.
    intros F.
    apply merge_nil_inversion in F as [F _].
    destruct v0; simpl in F; inversion F.
    
    
    inversion F.
    simpl in IHm. 
    specialize (IHm p2).



  intros Γ Γ' m v default p E NZ T.
  induction m.
  simpl in p.
  dependent destruction p.
  dependent destruction T.
  contradict NZ; reflexivity.
  clear NZ.
  dependent destruction p.
  dependent destruction T.
  simpl.
  unfold solution_left.
  unfold eq_rect_r.
  unfold eq_rect.
  simpl.
  destruct v.
  simpl.
  exists Γ1. exists Γ2. type_check. assumption.
  destruct Γ.
  simpl.
  exists Γ1. exists Γ2. type_check. assumption.
  destruct o.
  simpl.
  simpl in IHm. 
  specialize (IHm p2).
  

(*
(* Not sure if this lemma is right *)
Lemma get_wire_WT : forall m Γ v default (p : Pat (S m ⨂ Qubit)), 
  Valid Γ ⊢ p :Pat ->
  {Γ1 : OCtx & {Γ2 : OCtx & Γ == Γ1 ∙ Γ2 & Γ1  ⊢ get_wire (position_of v Γ) p default :Pat}}.
Proof.
  intros m Γ v default p H.
  induction m.
  - simpl in p.
    dependent destruction p.
    dependent destruction p2.
    dependent destruction H.
    dependent destruction H0.
    rewrite merge_nil_r in e. subst.
    dependent destruction H.
    simpl.
    unfold solution_left.
    unfold eq_rect_r.
    simpl.
    destruct v.
    simpl.
    exists Γ. exists ∅. type_check. type_check. assumption.
    simpl.

(* untrue in current form *)
Lemma position_of_singleton : forall Γ W x v, SingletonCtx x W Γ ->
                                         position_of v Γ = 0%nat.
Proof.
  intros Γ W x v H.
  induction H.
  - destruct v; simpl. reflexivity. destruct v; simpl.
  

    dependent destruction Γ.
    destruct Γ. 

dependent destruction s.
    exists Γ. exists ∅. type_check. type_check. assumption.
    simpl.
  

induction v.
  - simpl.
    destruct m. 
    simpl in p.
    dependent destruction p.
    destruct H.
    inversion TP. subst.
    destruct Γo. inversion pf_merge. destruct c. inversion pf_merge.
    inversion pf_merge. destruct o. inversion H0. inversion H0.
    dependent destruction p.
    dependent destruction TP. 
    simpl.
    unfold solution_left.
    unfold eq_rect_r.
    simpl.
*)

Lemma WT_compile : forall (b : rbexp) (Γ Γb Γo : Ctx), 
    Γb = (get_context b) ->
    Valid Γ = Γb ⋓ Γo -> 
    Typed_Box (compile b Γ).
Proof.
  induction b.
  - type_check.
  - type_check.
  - type_check.
    Focus 3. 
    

    assert({Γ : Ctx & (Γ ⊢ get_wire (position_of v Γ) p2 (qubit v0) :Pat) }).
      induction v.
      destruct Γo.
        rewrite merge_nil_r in H0. inversion H0. subst.
        simpl in p2.
        dependent destruction p2. 
        dependent destruction p2_2.
        dependent destruction H1_0.
        dependent destruction H1_0_2.
        rewrite merge_nil_r in i, i0. 
        simpl.
        unfold solution_left.
        unfold eq_rect_r.
        simpl.
        destruct Γ1 as [|Γ1]. apply not_valid in i0. contradiction.        
        exists Γ1.
        apply H1_0_1.
        (* *)
        destruct o. simpl in H0. inversion H0.
        simpl in H0.
        Transparent merge.
        simpl in H0.
        Opaque merge.
        simpl.
        destruct Γ. inversion H0.
        inversion H0. subst. clear H0.
        dependent destruction p2. 
        simpl.
        unfold solution_left.
        unfold eq_rect_r.
        unfold eq_rect.
        simpl.
        dependent destruction H1_0.
        destruct Γ1 as [|Γ1]. apply not_valid in i0. contradiction.        
        exists Γ1.
        apply H1_0_1.
        (* *)
        simpl.
        unfold get_wire.



      induction v.
      destruct Γo.
        rewrite merge_nil_r in H0. inversion H0. subst.
        simpl in p2.
        dependent destruction p2. 
        dependent destruction p2_2.
        dependent destruction H1_0.
        dependent destruction H1_0_2.
        rewrite merge_nil_r in e. subst.
        simpl.
        unfold solution_left.
        unfold eq_rect_r.
        simpl.
        apply H1_0_1.
        (* *)
        destruct o. simpl in H0. inversion H0.
        simpl in H0.
        Transparent merge.
        simpl in H0.
        Opaque merge.
        simpl.
        destruct Γ. inversion H0.
        inversion H0. subst. clear H0.
        dependent destruction p2. 
        simpl.
        unfold solution_left.
        unfold eq_rect_r.
        unfold eq_rect.
        simpl.
        dependent destruction H1_0.

*)        

(* without generalized hypothesis *)
Lemma WT_compile : forall (b : rbexp), Typed_Box (compile b (get_context b)).
Proof.
  induction b.
  - type_check.
  - type_check.
  - type_check.
    Focus 3. 
      induction v.
      simpl in p2. 
      dependent destruction p2. 
      dependent destruction p2_2.
      dependent destruction H0.
      dependent destruction H0_0.
      rewrite merge_nil_r in e. subst.
      simpl.
      unfold solution_left.
      unfold eq_rect_r.
      simpl.
      apply H0_.
      simpl.
      apply IHv.
      apply H0.
    Focus 2.
      reflexivity.
    validate.
    Focus 4.
      induction v.
      simpl in p2. 
      dependent destruction p2. 
      dependent destruction p2_2.
      dependent destruction H0.
      dependent destruction H0_0.
      rewrite merge_nil_r in e. subst.
      simpl.
      unfold solution_left.
      unfold eq_rect_r.
      simpl.
      econstructor.
      all: type_check.
      rewrite merge_nil_r in IHv.
      apply IHv. assumption. apply pf_valid.
    all:type_check.
  - type_check.
    Focus 4.
      4: constructor.
      3: apply H1_.
      2: rewrite merge_nil_r; reflexivity.
      apply H1_.
      simpl.
      apply IHv.
      apply H0.
    
      

 unfold denote_Ctx in p2. simpl in p2.
  - type_check.
  - type_check.

(*

Inductive reversible {W} : Circuit W -> Set := 
| rev_output : forall p, reversible (output p)
| rev_not    : forall p1 c, reversible c -> reversible (gate_ p2 ←  X @p1; c)
| rev_cnot   : forall p1 c, reversible c -> reversible (gate_ p2 ←  CNOT @p1; c)
| rev_ccnot  : forall p1 c, reversible c -> reversible (gate_ p2 ← CCNOT @p1; c).


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

