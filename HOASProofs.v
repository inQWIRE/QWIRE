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


(*****************************************************************************)
(** EXAMPLES START **)
(*****************************************************************************)

Lemma Ex : ⟦init true⟧ I1 = (|1⟩⟨1| : Density 2).
Proof.
  repeat (autounfold with den_db; simpl).
  autorewrite with M_db.
  reflexivity.
Qed.


Fixpoint pat_map {w} (f : Var -> Var) (p : Pat w) : Pat w :=
  match p with
  | unit => unit
  | qubit x => qubit (f x)
  | bit x => bit (f x)
  | pair p1 p2 => pair (pat_map f p1) (pat_map f p2)
  end.

(* Why are we defining this from scratch??? *)
Fixpoint inb (a : Var) (ls : list Var) : bool :=
  match ls with
  | [] => false
  | b :: ls' => (b =? a) || inb a ls'
  end%bool.

Fixpoint subset (ls1 ls2 : list Var) : bool :=
  match ls1 with
  | [] => true
  | a :: ls1' => inb a ls2 && subset ls1' ls2
  end.
Notation "ls1 ⊆ ls2" := (subset ls1 ls2 = true) (at level 30).

Fixpoint disjoint (ls1 ls2 : list Var) : bool :=
  match ls1 with
  | [] => true
  | a :: ls1' => (negb (inb a ls2)) && disjoint ls1' ls2
  end.
Notation "ls1 ⊥ ls2" := (disjoint ls1 ls2 = true) (at level 30).

Lemma disjoint_nil_l : forall ls, nil ⊥ ls. Proof. reflexivity. Qed.
Lemma disjoint_nil_r : forall ls, ls ⊥ nil. Proof. induction ls; trivial. Qed.

(*
Lemma disjoint_cons : forall a ls1 ls2, (negb (inb a ls1)) = true ->
                                   ls1 ⊥ ls2 ->
                                   ls1 ⊥ (a :: ls2).
Proof.
  intros a ls1 ls2 H H0.
  induction ls1.
  apply disjoint_nil_l.
  simpl in *.
  Search ((_ =? _) = (_ =? _)).
  rewrite Nat.eqb_sym.
  destruct (a0 =? a). simpl in *. inversion H.
  destruct (inb a0 ls2). simpl in *. inversion H0.
  simpl in *.
  apply IHls1; assumption.
Qed.  
*)

Lemma disjoint_cons : forall a ls1 ls2, 
    ((negb (inb a ls1)) && disjoint ls1 ls2 = disjoint ls1 (a :: ls2))%bool.
Proof.
  intros a ls1 ls2.
  induction ls1. reflexivity.
  simpl.
  rewrite <- IHls1.
  rewrite Nat.eqb_sym.
  destruct (a =? a0), (inb a ls1), (inb a0 ls2); auto.
Qed.  

Lemma disjoint_symm : forall ls1 ls2, disjoint ls1 ls2 = disjoint ls2 ls1.
Proof. intros. 
       induction ls1.
       - simpl.
         symmetry.
         apply disjoint_nil_r.
       - simpl.
         rewrite <- disjoint_cons.
         rewrite IHls1.
         reflexivity.
Qed.         
         

Lemma eqb_neq : forall x y, x <> y -> x =? y = false.
Proof.
  induction x as [ | x]; destruct y as [ | y]; intros H; auto.
  - contradiction.
  - simpl.
    apply IHx.
    intros H'.
    subst.
    contradiction.
Qed.

Lemma lookup_app : forall x ls1 ls2,
      lookup x (ls1 ++ ls2) = if inb x ls1 then lookup x ls1 
                                           else (lookup x ls2 + length ls1)%nat.
Proof.
  induction ls1; intros; simpl; auto. 
  destruct (Nat.eq_dec x a) as [H_x_a | H_x_a].
  * subst.
    rewrite Nat.eqb_refl.
    reflexivity.
  * repeat rewrite eqb_neq; auto. simpl.
    rewrite IHls1.
    destruct (inb x ls1); auto.
Qed.

Lemma subset_app : forall ls1 ls2 ls, (ls1 ++ ls2) ⊆ ls -> ls1 ⊆ ls /\ ls2 ⊆ ls.
Proof.
  induction ls1; intros ls2 ls H; simpl in *; split; auto.
  - apply Bool.andb_true_iff in H.
    destruct H as [H_a_ls H].
    rewrite H_a_ls; simpl.
    apply IHls1 in H.
    destruct H; auto.
  - apply Bool.andb_true_iff in H.
    destruct H as [H_a_ls H].
    apply IHls1 in H.
    destruct H; auto.
Qed.

Lemma seq_app : forall offset1 offset2 start,
      seq start offset1 ++ seq (start + offset1) offset2 
    = seq start (offset1 + offset2).
Proof.
  induction offset1; intros; simpl; auto.
  rewrite Nat.add_succ_r.
  rewrite <- Nat.add_succ_l.
  rewrite IHoffset1.
  reflexivity.
Qed.



Lemma pat_WType_size : forall W (p : Pat W), pat_size p = size_WType W.
Proof. reflexivity. Qed.



Lemma get_fresh_pat_state : 
  forall w σ σ', σ' = snd (get_fresh_pat w σ) ->
                 fresh σ' = (fresh σ + ⟦w⟧)%nat.
Proof.
  induction w; intros; subst; simpl; try omega.

  autounfold with monad_db.
  destruct (get_fresh_pat w1 σ) as [p1 σ1] eqn:H1.
  destruct (get_fresh_pat w2 σ1) as [p2 σ2] eqn:H2.
  simpl.
  rewrite (IHw2 σ1 σ2); [ | rewrite H2; auto].
  rewrite (IHw1 σ σ1); [ | rewrite H1; auto].
  simpl. omega.
Qed.


Lemma swap_fresh_seq : forall {w} σ,
    pat_to_list (fresh_pat w σ) = seq (fresh σ) (⟦w⟧).
Proof.
  induction w; intros σ; simpl; auto.
  unfold fresh_pat. simpl.
  autounfold with monad_db.
    destruct (get_fresh_pat w1 σ) as [p1 σ1] eqn:H1.
    destruct (get_fresh_pat w2 σ1) as [p2 σ2] eqn:H2. 
    rewrite <- seq_app; simpl.
    replace p1 with (fresh_pat w1 σ) by (unfold fresh_pat; rewrite H1; auto).
    replace p2 with (fresh_pat w2 σ1) by (unfold fresh_pat; rewrite H2; auto).
    rewrite IHw1, IHw2.
    simpl.
    rewrite (get_fresh_pat_state w1 σ σ1); auto.
    rewrite H1; auto.
Qed.
    


Lemma swap_list_id : forall w,
      swap_list (⟦w⟧) (pat_to_list (fresh_pat w (st_{0}))) = Id (2^⟦w⟧).
Proof.
  intros.
  rewrite swap_fresh_seq. 
  apply swap_list_n_id.
Qed.



Lemma id_circ_Id : forall W ρ, WF_Matrix (2^⟦W⟧) (2^⟦W⟧) ρ -> 
    ⟦@id_circ W⟧ ρ = ρ.
Proof.
  intros W ρ H.
  repeat (simpl; autounfold with den_db).
  rewrite fresh_pat_eq'.
  simpl.
  rewrite subst_fresh_id.
  rewrite swap_list_id; auto.
  unfold super. autorewrite with M_db. reflexivity.
Qed.
 
Lemma unitary_transpose_id_qubit : forall (U : Unitary Qubit), forall ρ,
   WF_Matrix (2^⟦Qubit⟧) (2^⟦Qubit⟧) ρ -> 
   ⟦unitary_transpose U⟧ ρ = ⟦@id_circ Qubit⟧ ρ.
Proof.
  intros U ρ pf_ρ.
  assert (unitary_U : is_unitary (denote_unitary U)) by apply unitary_gate_unitary.
  destruct unitary_U as [WF inv].
  repeat (autounfold with den_db; simpl in *).
  autorewrite with M_db.
  repeat rewrite Mmult_assoc; try rewrite inv.
  repeat rewrite <- Mmult_assoc; try rewrite inv.
  autorewrite with M_db.
  reflexivity.
Qed.



Lemma unitary_transpose_id : forall W (U : Unitary W) (ρ : Density (2^⟦W⟧ )),
  WF_Matrix (2^⟦W⟧) (2^⟦W⟧) ρ ->
  ⟦unitary_transpose U⟧ ρ = ⟦@id_circ W⟧ ρ.
Proof.
  intros W U ρ wfρ. 
  specialize (unitary_gate_unitary U); intros [WFU UU].
  repeat (simpl; autounfold with den_db).

  rewrite fresh_pat_eq'.
  simpl.
  rewrite subst_fresh_id.
  rewrite swap_list_id; auto.

  (* do some arithmetic *)
  rewrite minus_plus, Nat.add_0_r.
  rewrite Nat.leb_refl.

  repeat rewrite subst_fresh_id.
  erewrite swap_fresh_seq by (unfold fresh_pat; auto).  

  repeat (autounfold with den_db; simpl).
  setoid_rewrite swap_list_n_id.

  rewrite Nat.sub_diag.
  autorewrite with M_db.
  repeat rewrite Mmult_assoc.
  setoid_rewrite UU.
  repeat rewrite <- Mmult_assoc.
  setoid_rewrite UU.
  autorewrite with M_db.
  reflexivity.
Qed.

Definition fair_coin : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => 1/2
          | 1, 1 => 1/2
          | _, _ => 0
          end.

Definition biased_coin (c : C) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => (1 - c) 
          | 1, 1 => c
          | _, _ => 0
          end.

Definition uniform (n : nat) : Matrix n n :=
  fun x y => if (x =? y) && (x <? n) then 1/(INR n) else 0.

Lemma bias1 : biased_coin 1 = |1⟩⟨1|.
Proof.
  unfold biased_coin.
  prep_matrix_equality; simpl.
  destruct_m_eq; clra.
Qed.

Lemma even_bias : biased_coin (1/2) = fair_coin.
Proof. 
  unfold biased_coin, fair_coin.
  prep_matrix_equality; simpl.
  destruct_m_eq; clra.
Qed.

Lemma fair_toss : ⟦coin_flip⟧ I1  = fair_coin.
Proof.
  repeat (autounfold with den_db; simpl).
  autorewrite with M_db.
  prep_matrix_equality.
  autounfold with M_db.
  simpl; autorewrite with C_db.
  destruct_m_eq; autorewrite with C_db; reflexivity.
Qed.

Fixpoint upper_bound (li : list nat) : nat :=
  match li with
  | nil => 0
  | n :: li' => max (S n) (upper_bound li')
  end.

Lemma size_singleton : forall x w, size_Ctx (singleton x w) = 1%nat.
Proof.
  induction x; intros; simpl; auto.
Qed.

Lemma size_pat_to_ctx : forall {w} (p : Pat w) Γ, Types_Pat Γ p ->
    ⟦pat_to_ctx p⟧= ⟦w⟧.
Proof.
  induction 1; simpl; auto; try apply size_singleton.
  admit (* lemma about denote_OCtx (_ ⋓ _) *).
Admitted.


Lemma size_OCtx_WType : forall Γ w (p : Pat w), Types_Pat Γ p -> ⟦Γ⟧=⟦w⟧.
Admitted.

Lemma OCtx_dom_pat : forall w (p : Pat w),
      OCtx_dom (pat_to_ctx p) = pat_to_list p.
Admitted.

Lemma remove_refl : forall σ,
  fold_left (fun σ x => remove_var x σ) (get_σ σ) σ = st_{0}.
Admitted.



(* Do these belong back in Denotation? *) 
Theorem inSeq_correct : forall W1 W2 W3 (g : Box W2 W3) (f : Box W1 W2),
      Typed_Box g -> Typed_Box f ->
     ⟦inSeq f g⟧ = compose_super (⟦g⟧) (⟦f⟧).
Proof.
  intros W1 W2 W3 g f types_g types_f.
  autounfold with den_db; simpl. 

  destruct f as [f]. 
  destruct g as [g].
  autounfold with den_db; simpl.
  repeat rewrite fresh_pat_eq'. simpl.

  set (p1 := fresh_pat W1 (st_{0})).
  set (Γ1 := pat_to_ctx p1).
  assert (types_p : Types_Pat Γ1 p1).
  { apply fresh_pat_typed with (σ := st_{0}). auto. }
  assert (valid_Γ1 : is_valid Γ1).
  { eapply pat_ctx_valid; eauto. }

(*  set (σ0 := remove_OCtx Γ1 (st_{⟦W1⟧})).*)
  set (p2 := fresh_pat W2 (st_{0})).

  erewrite denote_compose with (Γ1' := Γ1) (Γ := ∅) (Γ2 := Γ1);
    [ | apply types_f; auto 
    | split; [auto | monoid]
    | intros p' Γ Γ2' [pf_merge pf_valid] types_p';
      apply types_g; rewrite merge_nil_r in pf_valid; subst; apply types_p'
    | simpl; erewrite size_OCtx_WType; [ | eauto]; simpl; omega 
    | rewrite surjective_pairing; f_equal ].
 
  replace (remove_OCtx Γ1 (st_{size_WType W1})) with (st_{0}).
  -- 
  simpl. unfold compose_super. 
  rewrite (Nat.add_0_r (size_WType W2)).
  replace (size_WType W1) with (denote_OCtx Γ1) by (eapply size_OCtx_WType; eauto).
  rewrite fresh_pat_eq'; simpl.
  unfold p2, fresh_pat. 
  reflexivity.

  -- 
    unfold remove_OCtx.
    unfold Γ1.
    rewrite OCtx_dom_pat.
    unfold p1.
    rewrite swap_fresh_seq.
    replace (fresh (st_{0})) with 0%nat by auto.
    replace (σ_{⟦W1⟧}) with (get_σ (st_{⟦W1⟧})) by auto. 
    rewrite remove_refl; auto.
Qed.

Theorem inPar_correct : forall W1 W1' W2 W2' (f : Box W1 W1') (g : Box W2 W2') 
     (ρ1 : Square (2^⟦W1⟧)) (ρ2 : Square (2^⟦W2⟧)),
     Typed_Box f -> Typed_Box g ->
     Mixed_State ρ1 -> Mixed_State ρ2 ->
     denote_box (inPar f g) (ρ1 ⊗ ρ2)%M = (denote_box f ρ1 ⊗ denote_box g ρ2)%M.
Proof.  
  intros W1 W1' W2 W2' f g H H0.
  autounfold with den_db; simpl. 

  destruct f as [f]. 
  destruct g as [g].
  autounfold with den_db; simpl.
  repeat rewrite fresh_pat_eq'. simpl.

  set (p1 := fresh_pat W1 (st_{0})).
  set (p2 := fresh_pat W2 (st_{0})).
Admitted.  

Open Scope circ_scope.

(* probably a more general form of this *)
Lemma denote_db_unbox : forall {w1 w2} (b : Box w1 w2),
    ⟦b⟧ = ⟨ 0 | ⟦w1⟧ | unbox b (fresh_pat w1 (st_{0})) | st_{⟦w1⟧} ⟩.
Proof.
  destruct b.
  simpl. unfold denote_box.
  simpl.
  rewrite fresh_pat_eq'. simpl.
  reflexivity.
Qed.

Lemma wf_biased_coin : forall c, WF_Matrix 2 2 (biased_coin c).
Proof.
  intros; show_wf.
Qed.

Hint Resolve wf_biased_coin : wf_db.

Open Scope circ_scope.

Hint Unfold super_Zero : den_db. Print coin_flips.

Lemma flips_correct : forall n, ⟦coin_flips n⟧ I1 = biased_coin (1/(2^n)).
Proof.
  induction n.  
  + repeat (autounfold with den_db; simpl).
    autorewrite with M_db.
    prep_matrix_equality.
    autounfold with M_db.
    destruct_m_eq; clra.
  + simpl.
    repeat (simpl; autounfold with den_db). 

    erewrite denote_compose with (Γ := ∅) (Γ1 := ∅) (Γ1' := ∅);
      [ | apply unbox_typing; [type_check | apply coin_flips_WT]
      | split; [validate | monoid]
      | 
      | auto
      | replace (remove_OCtx ∅ (st_{0})) with (st_{0})
          by (unfold remove_OCtx; auto);
         rewrite fresh_pat_eq'; auto
      ].
    -- 
       (* Apply IH *)
       rewrite denote_db_unbox in IHn.
       unfold fresh_pat in IHn.
       simpl in *. 
       unfold compose_super.
       rewrite IHn.

       repeat (autounfold with den_db; simpl).
       unfold hoas_to_db.
       autorewrite with M_db. 
    
      
       setoid_rewrite kron_conj_transpose. 
       autorewrite with M_db.
       specialize hadamard_sa; intros pf_H.
       setoid_rewrite control_sa; auto.

       solve_matrix.
       * rewrite Cmult_comm.
         rewrite Cmult_assoc.
         autorewrite with C_db.
         rewrite Cinv_mult_distr; [|nonzero|apply Cpow_nonzero; lra].         
         replace (/ 2^n) with (/2 * /2 ^ n + /2 */2^n) at 1 by clra.
         rewrite Copp_plus_distr.
         repeat rewrite <- Cplus_assoc.
         autorewrite with C_db.
         reflexivity.
       * rewrite Cmult_comm.
         rewrite Cmult_assoc.
         autorewrite with C_db.
         rewrite Cinv_mult_distr; [|nonzero|apply Cpow_nonzero; lra].         
         reflexivity.

    --
      intros p Γ2 Γ2' [pf_valid pf_merge] types_p.
      rewrite merge_nil_r in pf_merge. subst. 
      type_check; auto.
Qed.



Lemma cnot_eq : cnot = control σx.
Proof.
  autounfold with M_db.
  simpl.
  prep_matrix_equality.
  repeat (try destruct x; try destruct y; autorewrite with C_db; trivial).
Qed.


Definition EPR00 : Matrix 4 4 :=
  fun x y => match x, y with
             | 0, 0 => 1/2
             | 0, 3 => 1/2
             | 3, 0 => 1/2
             | 3, 3 => 1/2
             | _, _ => 0
             end.

Lemma bell00_eq :  ⟦bell00⟧ I1  = EPR00.
Proof.
  repeat (simpl; autounfold with den_db). 
  autorewrite with M_db. 
  repeat setoid_rewrite kron_conj_transpose.
  autorewrite with M_db. 
  solve_matrix.
Qed.

(***********)
(* sharing *)
(***********)

Close Scope circ_scope.

Fixpoint kron_n (n : nat) {m1 m2 : nat} (A : Matrix m1 m2) : Matrix (m1^n) (m2^n) :=
  match n with
  | 0    => Id 1
  | S n' => A ⊗ kron_n n' A
  end.
Lemma wf_kron_n : forall n m1 m2 A,
      m1 <> 0%nat -> m2 <> 0%nat ->
      WF_Matrix m1 m2 A ->
      WF_Matrix (m1^n) (m2^n) (kron_n n A).
Proof.
  induction n; intros; simpl; try show_wf.
  apply WF_kron; auto;
  apply Nat.pow_nonzero; auto.
Qed.
      

Open Scope circ_scope.


Lemma denote_circuit_subst : forall w (c : Circuit w) Γ, Types_Circuit Γ c ->
      forall pad n σ, 
      WF_σ Γ (get_σ σ) ->
      ⟨ pad | n | c | σ ⟩ 
    = compose_super ⟨pad | n | c | st_{n}⟩
                    (super (swap_list n (get_σ σ))).
Proof.
  induction 1; intros.
  * simpl. 
    erewrite subst_id; eauto.
    admit. admit.
  * simpl. erewrite H; eauto. admit.

Admitted.

Lemma denote_unbox : forall n w1 w2 (b : Box w1 w2) Γ1 p σ, 
      Typed_Box b -> Types_Pat Γ1 p ->
      n = ⟦w1⟧ ->  WF_σ Γ1 (get_σ σ) ->

      ⟨0 | n | unbox b p | σ⟩
    = compose_super (⟦b⟧)
                    (super (swap_list (⟦w1⟧) (pat_to_list (subst_pat (get_σ σ) p)))).
Proof.
  intros.
  rewrite denote_db_unbox.
  rewrite denote_circuit_subst with (Γ := Γ1); auto.
  subst.
 admit (* not quite *).

Admitted.
  
Hint Unfold apply_box : den_db.


Lemma share_correct : forall n ρ, 
      WF_Matrix 2 2 ρ -> 
      ⟦share n⟧ ρ = kron_n (S n) ρ.
Proof.
  induction n; intros.
  * repeat (autounfold with den_db; simpl).
    autorewrite with M_db.
    reflexivity.
  * repeat (autounfold with den_db; simpl).
    autorewrite with M_db. 
    setoid_rewrite kron_conj_transpose.
    autorewrite with M_db. 

    remember (singleton 1%nat Qubit) as Γ_1.
    remember (singleton 0%nat Qubit) as Γ_2.
    remember (Γ_1 ⋓ Γ_2) as Γ_1'.
    remember ({| get_σ := [0%nat]; fresh := 2|}) as σ0. 
    destruct (get_fresh_pat (S n ⨂ Qubit) σ0) as [p0 σ0'] eqn:H_p0.

    rewrite denote_compose with (Γ1 := Γ_1) (Γ := Γ_2) (Γ1' := Γ_1')
                                 (p := p0) (σ' := σ0') ; subst;
    [ | apply share_WT; type_check; repeat constructor
    | type_check | | reflexivity | auto ]. 
 Focus 2. Transparent merge. simpl. Opaque merge.
          validate.
 Focus 2. intros. destruct H0. subst.
    econstructor; [reflexivity | ]. 
    econstructor; [auto | | | eauto]; [monoid | ]. constructor. 
      apply singleton_singleton.


  simpl. 
(*
  rewrite denote_unbox. unfold compose_super. simpl. rewrite IHn.
  Focus 2. simpl. (* BUG: swap_list 1 [1] voilates precondition of swap_list *)
    apply WF_Mixed.
    apply mixed_unitary. admit (* swap lists are well-formed? *).
                         admit (* swap lists are unitary? *).
                         admit.


  simpl in H_p0. autounfold with monad_db in H_p0. simpl in H_p0.
Print subst_state.
  unfold Var in *.
  set (σ1 := Mk_subst_state (0%nat :: 2%nat :: nil) (3%nat)).
  fold σ1 in H_p0.

  destruct (get_fresh_pat (n ⨂ Qubit) σ1) as [p1 σ1'] eqn:H_p1.
  inversion H_p0; subst. 
  repeat (autounfold with den_db; simpl).
*)
(*??? *)
Admitted.



(***********************)
(* Deutsch's Algorithm *)
(***********************)
(* Temporarily commented out for efficient compilation

Delimit Scope circ_scope with qc.


(* f(x) = 0. Unitary: Identity *)
Definition f0 : Matrix 4 4 := Id 4.

(* f(x) = x. Unitary: CNOT *)
Definition f1 : Matrix 4 4 := control σx.

(* f(x) = 1 - x. Unitary: inverse CNOT *)
Definition f2 : Matrix 4 4 := fun x y =>
  match x, y with
  | 0, 1 | 1, 0 | 2, 2 | 3, 3 => 1
  | _, _                      => 0
  end.

Close Scope circ_scope. 

(* f(x) = 1. Unitary: Id ⊗ X *)
Definition f3 : Matrix 4 4 := Id 2 ⊗ σx.

Definition constant (U : Unitary (Qubit ⊗ Qubit)%qc) := 
                       denote_unitary U = f0 \/ denote_unitary U = f3.
Definition balanced (U : Unitary (Qubit ⊗ Qubit)%qc) := 
                       denote_unitary U = f1 \/ denote_unitary U = f2.

Lemma f2_WF : WF_Matrix 4 4 f2. Proof. show_wf. Qed.
Hint Resolve f2_WF : wf_db.
  
Lemma deutsch_constant : forall U_f, constant U_f -> 
                                ⟦deutsch U_f⟧ I1 = |0⟩⟨0|.
Proof.
  intros U_f H.
  repeat (simpl; autounfold with den_db). 
  specialize (unitary_gate_unitary U_f). intros [WFU UU].
  simpl in WFU.
  autorewrite with M_db.
  repeat setoid_rewrite kron_conj_transpose.
  autorewrite with M_db. 

  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  autorewrite with M_db. 
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_r.
  autorewrite with M_db. 
  destruct H; rewrite H; clear.
  + (* f0 *)
    unfold f0.
    repeat reduce_matrix.
    crunch_matrix.
    all: try (destruct y; simpl; try rewrite divmod_eq; simpl; clra).
    unfold Cdiv.
    autorewrite with C_db. 
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db.  
    rewrite <- (Cmult_assoc 2 (√2) _).
    rewrite (Cmult_assoc (√2) _ _).
    autorewrite with C_db.
    repeat rewrite Cmult_assoc.
    autorewrite with C_db.
    reflexivity.
  + (* f3 *)
    unfold f3.
    repeat reduce_matrix.
    crunch_matrix.
    all: try (destruct y; simpl; try rewrite divmod_eq; simpl; clra).
    unfold Cdiv.
    autorewrite with C_db. 
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db.  
    rewrite <- (Cmult_assoc 2 (√2) _).
    rewrite (Cmult_assoc (√2) _ _).
    autorewrite with C_db.
    repeat rewrite Cmult_assoc.
    autorewrite with C_db.
    reflexivity.
Qed.

Lemma deutsch_balanced : forall U_f, balanced U_f -> 
                                ⟦deutsch U_f⟧ I1 = |1⟩⟨1|.
Proof.
  intros U_f H.
  repeat (simpl; autounfold with den_db). 
  specialize (unitary_gate_unitary U_f). intros [WFU UU].
  simpl in WFU.
  autorewrite with M_db.
  repeat setoid_rewrite kron_conj_transpose.
  autorewrite with M_db. 

  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  autorewrite with M_db. 
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_r.
  autorewrite with M_db. 
  
  destruct H; rewrite H; clear.
  + (* f1 *)
    unfold f1.
    repeat reduce_matrix.
    crunch_matrix.
    all: try (destruct y; simpl; try rewrite divmod_eq; simpl; clra).
    autorewrite with C_db. 
    unfold Cdiv.
    autorewrite with C_db. 
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db.  
    rewrite <- (Cmult_assoc 2 (√2) _).
    rewrite (Cmult_assoc (√2) _ _).
    autorewrite with C_db.
    repeat rewrite Cmult_assoc.
    autorewrite with C_db.
    reflexivity.
  + (* f2 *)
    unfold f2.
    repeat reduce_matrix.
    crunch_matrix.
    all: try (destruct y; simpl; try rewrite divmod_eq; simpl; clra).
    autorewrite with C_db. 
    unfold Cdiv.
    autorewrite with C_db. 
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db.  
    rewrite <- (Cmult_assoc 2 (√2) _).
    rewrite (Cmult_assoc (√2) _ _).
    autorewrite with C_db.
    repeat rewrite Cmult_assoc.
    autorewrite with C_db.
    reflexivity.
Qed.

(* Let's see if not distributing is faster *)
Lemma deutsch_balanced' : forall U_f, balanced U_f -> 
                                ⟦deutsch U_f⟧ I1 = |1⟩⟨1|.
Proof.
  intros U_f H.
  repeat (simpl; autounfold with den_db). 
  specialize (unitary_gate_unitary U_f). intros [WFU UU].
  simpl in WFU.
  autorewrite with M_db.
  repeat setoid_rewrite kron_conj_transpose.
  autorewrite with M_db. 
  destruct H; rewrite H; clear.
  + (* f1 *)
    unfold f1.
    solve_matrix.
    rewrite (Cmult_comm (1/√2) (1/2)).
    repeat rewrite <- Cmult_assoc.
    rewrite (Cmult_comm (1/√2) _).
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    unfold Cdiv.
    autorewrite with C_db. 
    repeat rewrite Cmult_assoc.
    rewrite <- (Cmult_assoc 2 2 _).
    autorewrite with C_db.
    reflexivity.
  + (* f2 *)
    unfold f2.
    solve_matrix.
    rewrite (Cmult_comm (1/√2) (1/2)).
    repeat rewrite <- Cmult_assoc.
    rewrite (Cmult_comm (1/√2) _).
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    unfold Cdiv.
    autorewrite with C_db. 
    repeat rewrite Cmult_assoc.
    rewrite <- (Cmult_assoc 2 2 _).
    autorewrite with C_db.
    reflexivity.
Qed.
*)

(* We convert the matrices back to functional representation for 
   unification. Simply comparing the matrices may be more efficient,
   however. *)
(*
Lemma teleport_eq : forall (ρ : Density 2), 
  Mixed_State ρ -> ⟦teleport⟧ ρ = ρ.
Proof.
  intros ρ H.
  idtac.
  repeat (simpl; autounfold with den_db). 
  autorewrite with M_db.
  repeat (setoid_rewrite kron_conj_transpose).
  autorewrite with M_db.
  idtac.

  assoc_least.
  solve_matrix.

  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite <- Mmult_assoc.
  
  (* This makes progress. Haven't managed to run to completion yet. *)
  repeat reduce_matrix.
  solve_matrix.
  

Abort.
*)

(* Lemmas out of date
Lemma boxed_gate_correct : forall W1 W2 (g : Gate W1 W2) (ρ : Density (2^⟦W1⟧)) ,
      Mixed_State (2^⟦W1⟧) (2^⟦W1⟧) ρ -> ⟦boxed_gate g⟧ ρ = ⟦g⟧ ρ.
Proof.
  intros W1 W2 g ρ wf_ρ. simpl.
  unfold denote_pat_in.
  repeat rewrite merge_nil_r.
  repeat rewrite size_fresh_ctx.
  repeat rewrite fresh_pat_empty.
  repeat rewrite map_num_wires_before.
  repeat rewrite swap_list_n_id.
  unfold super, compose_super.
  repeat rewrite mult_1_r.
  assert (wf_g : WF_Matrix (2^⟦W2⟧) (2^⟦W2⟧) (⟦g⟧ ρ)).
    generalize (WF_denote_gate 0 _ _ g ρ); intros.
    simpl in *. repeat rewrite mult_1_r in *. unfold denote_gate. apply (H wf_ρ).
  autorewrite with M_db.
  reflexivity.
Qed.

Lemma lift_meas_correct : lift_meas ≡ boxed_gate meas.
Proof.
  intros ρ wf_ρ.
  simpl.
  repeat (unfold denote_pat_in, swap_list, swap_two; simpl).
  Msimpl.
  unfold super, compose_super, Splus, SZero.
  Msimpl.
  rewrite braket0_conj_transpose, braket1_conj_transpose.
  prep_matrix_equality; simpl.
  unfold Mplus, Mmult, Id, conj_transpose, Zero. simpl.
  autorewrite with C_db.
  rewrite Cplus_comm. reflexivity.
Qed.

Lemma lift_eta_correct : forall (ρ : Density 2), WF_Matrix 2 2 ρ
      -> ⟦lift_eta Bit⟧ ρ = ⟦@id_circ Bit⟧ ρ.
Abort (* This is only true if ρ is a classical state *).
(* Proof.
  intros ρ wf_ρ.
  simpl.
  repeat (unfold denote_pat_in, swap_list, swap_two; simpl).
  Msimpl.
  unfold super, compose_super, Splus, SZero. 
  Msimpl.
  prep_matrix_equality.
  unfold Mmult, Mplus, Zero, conj_transpose, ket0, ket1. simpl.
  Csimpl.
  destruct x; Csimpl. 
  destruct y; Csimpl.
*)
*)


