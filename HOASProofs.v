Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Denotation.
Require Import DBCircuits.
Require Import TypeChecking.

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


(*
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
*)

Definition get_fresh_var {A} `{Gate_State A} (σ : A) (w : WType) : Var :=
    fst (get_fresh w σ).

Lemma is_valid_fresh : forall Γ w,
      is_valid Γ ->
      is_valid (fresh_state w Γ).
Admitted.

Lemma get_fresh_var_OCtx : forall Γ w,
      get_fresh_var Γ w = length_OCtx Γ.
Proof.
  destruct Γ as [ | Γ]; auto.
Qed.


Lemma length_fresh_state : forall w Γ,
      is_valid Γ ->
      length_OCtx (fresh_state w Γ) = (length_OCtx Γ + ⟦w⟧)%nat.
Proof.
  induction w; intros; (destruct Γ as [ | Γ]; [invalid_contradiction | ]); 
    simpl; auto.
  * rewrite app_length. auto.
  * rewrite app_length; auto.
  * rewrite IHw2; auto.
    rewrite IHw1; auto.
    simpl. omega.
    apply is_valid_fresh; auto.
Qed.

Lemma length_fresh_state' : forall w (σ : substitution),
      length (fresh_state w σ) = (length σ + ⟦w⟧)%nat.
Proof.
  induction w; intros; simpl; auto.
  * rewrite app_length; auto.
  * rewrite app_length; auto.
  * rewrite IHw2. 
    rewrite IHw1.
    simpl; omega.
Qed.



Lemma swap_fresh_seq : forall w (σ : substitution),
    pat_to_list (fresh_pat w σ) = seq (get_fresh_var σ w) (⟦w⟧).
Proof.
  induction w; intros; simpl; auto.
  rewrite IHw1.
  rewrite IHw2. 
  repeat rewrite get_fresh_var_OCtx.
  rewrite <- seq_app.
  unfold get_fresh_var. simpl.
  rewrite length_fresh_state'.
  auto.
Qed.


(*
Lemma swap_list_id : forall w,
      swap_list (⟦w⟧) (pat_to_list (fresh_pat w ∅)) = Id (2^⟦w⟧).
Proof.
  intros.
  rewrite swap_fresh_seq. 
  apply swap_list_n_id.
Qed.
*)

Print denote_pat.

Lemma denote_pat_fresh_id : forall w,
      denote_pat (fresh_pat w []) = Id (2^⟦w⟧).
Proof.
  intros.
  unfold denote_pat.
  rewrite swap_fresh_seq by validate.
  unfold get_fresh_var. simpl.
  rewrite swap_list_n_id.
  reflexivity.
Qed.

Lemma fmap_app : forall {A B} (f : A -> B) ls1 ls2,
      fmap f (ls1 ++ ls2) = fmap f ls1 ++ fmap f ls2.
Proof.
  induction ls1; intros; simpl; auto.
  rewrite IHls1. auto.
Qed.
Lemma fmap_id : forall {A} (ls : list A),
      fmap (fun x => x) ls = ls.
Proof.
  induction ls; simpl in *; auto.
  rewrite IHls.
  reflexivity.
Qed.
Lemma fmap_compose : forall {A B C} (f : A -> B) (g : B -> C) (ls : list A),
      fmap g (fmap f ls) = fmap (fun x => g (f x)) ls.
Proof.
  induction ls; simpl in *; auto.
  rewrite IHls.
  reflexivity.
Qed.

Lemma inb_fmap_S : forall ls x,
      inb (S x) (fmap S ls) = inb x ls.
Proof.
  induction ls; intros; simpl in *; auto.
  simpl.
  rewrite IHls.
  reflexivity.
Qed.

Opaque fmap.
Lemma ge_length_dom : forall Γ x,
      (x >= length_OCtx Γ)%nat ->
      inb x (OCtx_dom Γ) = false.
Proof.
  destruct Γ as [ | Γ]; [intros; auto | ].
  induction Γ as [ | [w | ] Γ]; intros; auto.
  * simpl in *.
    destruct x as [ | x]; [inversion H | ].
    simpl.
    rewrite inb_fmap_S.
    rewrite IHΓ; auto.
    omega.
  * simpl in *.
    destruct x as [ | x]; [inversion H | ].
    rewrite inb_fmap_S.
    apply IHΓ. 
    omega.
Qed.
Transparent fmap.


Lemma Ctx_dom_app : forall Γ1 Γ2,
      Ctx_dom (Γ1 ++ Γ2) = Ctx_dom Γ1 ++ fmap (fun x => length Γ1 + x)%nat (Ctx_dom Γ2).
Proof. 
  induction Γ1 as [ | [w | ] Γ1]; intros.
  * simpl.
    rewrite fmap_id.
    auto.
  * simpl. 
    rewrite IHΓ1. 
    rewrite fmap_app.
    rewrite fmap_compose.
    reflexivity.
  * simpl. 
    rewrite IHΓ1.
    rewrite fmap_app.
    rewrite fmap_compose.
    reflexivity.
Qed.
Transparent fmap.


Lemma OCtx_dom_fresh : forall w Γ, 
      is_valid Γ ->
      OCtx_dom (fresh_state w Γ) = OCtx_dom Γ ++ seq (length_OCtx Γ) (⟦w⟧).
Proof.
  induction w; 
  (destruct Γ as [ | Γ]; [intros; invalid_contradiction | ]);
  intros; simpl.

  * rewrite Ctx_dom_app. simpl.
    rewrite Nat.add_0_r.
    auto.
  * rewrite Ctx_dom_app. simpl.
    rewrite Nat.add_0_r.
    auto.
  * rewrite app_nil_r. 
    auto.
  * rewrite IHw2; [ | apply is_valid_fresh; auto].
    rewrite IHw1; auto.
    simpl.
    rewrite length_fresh_state; auto. simpl.

    rewrite <- seq_app.
    rewrite app_assoc.
    reflexivity.
Qed.


Lemma hoas_to_db_pat_fresh : forall w Γ w',
      Γ = fresh_state w' ∅ ->
      hoas_to_db_pat (fresh_state w Γ) (fresh_pat w Γ) 
    = fresh_pat w (OCtx_dom Γ).
Proof.
  induction w; intros; 
    (assert (is_valid Γ) by (subst; apply is_valid_fresh; validate));
    (destruct Γ as [ | Γ]; [invalid_contradiction | ]);
    unfold hoas_to_db_pat in *; simpl in *; auto.

  * rewrite Ctx_dom_app; simpl.
    unfold subst_var.
    rewrite lookup_app.
    replace (Ctx_dom Γ) with (OCtx_dom (Valid Γ)) by auto.
    rewrite ge_length_dom by (simpl; omega).
    rewrite Nat.add_0_r.
    simpl.
    rewrite Nat.eqb_refl.
    auto.
  * admit (* same as above *).

  * f_equal.
    + admit. (* more general lemma *)
    + rewrite IHw2 with (w' := w' ⊗ w1).
      - f_equal. Search OCtx_dom fresh_state.
        rewrite OCtx_dom_fresh; auto.
        simpl.
        admit (* lemma *).
      - rewrite H.
        reflexivity.
Admitted.

Lemma hoas_to_db_pat_fresh_empty : forall w,
      hoas_to_db_pat (fresh_state w ∅) (fresh_pat w ∅)
    = fresh_pat w [].
Proof.
  intros.
  apply hoas_to_db_pat_fresh with (w' := One).
  auto.
Qed.
    
Lemma super_I : forall n ρ,
      WF_Matrix n n ρ ->
      super ('I_n) ρ = ρ.
Proof.
  intros.
  unfold super.
  autorewrite with M_db.
  reflexivity.
Qed.



Lemma singleton_size' : forall x w,
      ⟦Valid (singleton x w)⟧ = 1%nat.
Proof.
  intros.
  simpl.
  eapply singleton_size.
  apply singleton_singleton.
Qed.

Lemma denote_Ctx_app : forall Γ1 Γ2,
      denote_Ctx (Γ1 ++ Γ2) = (denote_Ctx Γ1 + denote_Ctx Γ2)%nat.
Proof.
  induction Γ1; intros; simpl; auto.
  destruct a; auto.
  rewrite IHΓ1; auto.
Qed.

Lemma denote_OCtx_fresh : forall w Γ,
      is_valid Γ ->
      ⟦fresh_state w Γ⟧ = (⟦Γ⟧ + ⟦w⟧)%nat.
Proof.
  induction w; intros;
    (destruct Γ as [ | Γ]; [invalid_contradiction | ]).
  * simpl. 
    rewrite denote_Ctx_app.
    auto.
  * simpl.
    rewrite denote_Ctx_app.
    auto.
  * simpl.
    omega.
  * simpl.
    rewrite IHw2 by (apply is_valid_fresh; auto).
    rewrite IHw1 by auto.
    simpl. 
    omega. 
Qed.



(*
Lemma app_merge_singleton : forall Γ w,
    Valid (Γ ++ [Some w]) = Valid Γ ⋓ singleton (length Γ) w.
Proof.
  Transparent merge.
  induction Γ as [ | [w | ] Γ]; intros w'; simpl in *; auto.
  * rewrite <- IHΓ.
    auto.
  * rewrite <- IHΓ.
    auto.
  Opaque merge.
Qed.
*)

(*
Lemma fresh_state_qubit : forall Γ,
      fresh_state Qubit Γ = Γ ⋓ singleton (length_OCtx Γ) Qubit.
Proof.
  intros.
  unfold fresh_state.
  simpl.
  autounfold with monad_db.
  destruct Γ as [ | Γ]; auto.
  simpl. 
  apply app_merge_singleton.
Qed.
Lemma fresh_state_bit : forall Γ,
      fresh_state Bit Γ = Γ ⋓ singleton (length_OCtx Γ) Bit.
Proof.
  intros.
  unfold fresh_state.
  simpl.
  autounfold with monad_db.
  destruct Γ as [ | Γ]; auto.
  simpl. 
  apply app_merge_singleton.
Qed.
*)




Lemma WF_pad : forall m n (A : Square m),
      (m <= n)%nat ->
      WF_Matrix (2^m) (2^m) A ->
      WF_Matrix (2^n) (2^n) (@pad m n A).
Proof.
  intros. unfold pad.
  apply WF_kron; [ apply Nat.pow_nonzero; auto 
                 | apply Nat.pow_nonzero; auto 
                 | | | auto | show_wf].
  admit (* true *).
  admit (* true *).
Admitted.

Lemma apply_U_σ : forall m n (U : Square (2^m)),
      WF_Matrix (2^m) (2^m) U ->
      (m <= n)%nat -> 
      @apply_U m n U (σ_{n}) = super (pad n U).
Proof.
  intros. unfold apply_U.
  rewrite swap_list_n_id.
  apply WF_pad with (n := n) in H; auto.
  autorewrite with M_db.
  reflexivity.
Qed.



Lemma pad_nothing : forall m A,
      WF_Matrix (2^m) (2^m) A ->
      @pad m m A = A.
Proof.
  intros.
  unfold pad.
  rewrite Nat.sub_diag.
  simpl.
  autorewrite with M_db.
  reflexivity.
Qed.


(* TACTICS for doing this kind of proofs *)


Hint Rewrite hoas_to_db_pat_fresh_empty : proof_db.
Hint Rewrite denote_OCtx_fresh using validate : proof_db.

(* add some arithmetic *)
Hint Rewrite Nat.leb_refl : proof_db.
Hint Rewrite denote_pat_fresh_id : proof_db.
Hint Rewrite swap_fresh_seq : proof_db.
Hint Rewrite apply_U_σ pad_nothing using auto : proof_db.



Lemma id_circ_Id : forall W ρ, WF_Matrix (2^⟦W⟧) (2^⟦W⟧) ρ -> 
    ⟦@id_circ W⟧ ρ = ρ.
Proof.
  intros W ρ H.

  simpl. unfold denote_box. simpl.
  autorewrite with proof_db.
  rewrite super_I; auto.
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
  simpl. autounfold with den_db. simpl.

  assert (wf_U : WF_Matrix (2^⟦W⟧) (2^⟦W⟧) (⟦U⟧)) by show_wf.
  assert (wf_U_dag : WF_Matrix (2^⟦W⟧) (2^⟦W⟧) (⟦U⟧†)) by show_wf.

  autorewrite with proof_db.

  repeat (simpl; autounfold with den_db).
  autorewrite with M_db.
  
  repeat rewrite <- Mmult_assoc.
  setoid_rewrite UU.
  repeat rewrite Mmult_assoc.
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



Lemma fresh_state_pat : forall w,
      fresh_state w ∅ ⊢ fresh_pat w ∅ :Pat.
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

  set (Γ1_0 := fresh_state W1 ∅).
  set (Γ2_0 := fresh_state W2 ∅).

  erewrite denote_compose with (Γ := ∅) (Γ2 := Γ1_0) (Γ1 := Γ1_0);
    [ reflexivity (* main proof *)
    | apply types_f; apply fresh_state_pat
    | intros Γ0 Γ0' p0 [pf1 pf2] pf_p0; apply types_g;
      subst; rewrite merge_nil_r; auto
    | solve_merge; apply is_valid_fresh; validate].
Qed.

Lemma merge_singleton_end : forall Γ w,
      Valid (Γ ++ [Some w]) = Valid Γ ⋓ singleton (length Γ) w.
Proof.
  Transparent merge.
  induction Γ as [ | [w' | ] Γ]; intros; simpl in *; auto.
  * rewrite <- IHΓ. reflexivity.
  * rewrite <- IHΓ. reflexivity.
  Opaque merge.
Qed.

Lemma fresh_state_decompose : forall w Γ,
      is_valid Γ ->
      fresh_state w Γ == Γ ∙ (pat_to_ctx (fresh_pat w Γ)).
Proof.
  induction w; intros;
    (destruct Γ as [ | Γ]; [invalid_contradiction | ]);
    simpl.
  - solve_merge. apply merge_singleton_end.
  - solve_merge. apply merge_singleton_end.
  - solve_merge.
  - solve_merge.
    * repeat apply is_valid_fresh; auto.
    * destruct (IHw1 Γ); [auto | ].
      rewrite pf_merge.
      rewrite pf_merge in pf_valid.
      destruct (IHw2 (Γ ⋓ pat_to_ctx (fresh_pat w1 (Valid Γ)))); auto.
      rewrite pf_merge0.
      monoid.
Qed.

Close Scope circ_scope.
Lemma denote_tensor : forall (Γ Γ' : OCtx) {w} (c : Circuit w) 
                             {n1 n2} (ρ1 : Square n1) (ρ2 : Square n2),
      WF_Matrix (2^⟦Γ'⟧) (2^⟦Γ'⟧) ρ1 ->
      WF_Matrix (2^⟦Γ⟧) (2^⟦Γ⟧) ρ2 ->
      ⟨Γ | Γ' ⊩ c⟩ (ρ1 ⊗ ρ2) = (⟨∅ | Γ' ⊩ c⟩ ρ1) ⊗ ρ2.
Admitted.



Lemma hoas_to_db_pair : forall Γ w1 w2 (p1 : Pat w1) (p2 : Pat w2),
      hoas_to_db_pat Γ (pair p1 p2)
    = pair (hoas_to_db_pat Γ p1) (hoas_to_db_pat Γ p2).
Proof.
  intros. unfold hoas_to_db_pat. simpl.
  reflexivity.
Qed.



Theorem inPar_correct : forall W1 W1' W2 W2' (f : Box W1 W1') (g : Box W2 W2') 
     (ρ1 : Square (2^⟦W1⟧)) (ρ2 : Square (2^⟦W2⟧)),
     Typed_Box f -> Typed_Box g ->
     Mixed_State ρ1 -> Mixed_State ρ2 ->
     denote_box (inPar f g) (ρ1 ⊗ ρ2)%M = (denote_box f ρ1 ⊗ denote_box g ρ2)%M.
Proof.  
  intros W1 W1' W2 W2' f g ρ1 ρ2 types_f types_g mixed_ρ1 mixed_ρ2.

  destruct f as [f]. 
  destruct g as [g].
  repeat (autounfold with den_db; simpl).


  set (p_1 := fresh_pat W1 ∅).
  set (Γ_1 := fresh_state W1 ∅).
  set (p_2 := fresh_pat W2 Γ_1).
  set (Γ_2 := pat_to_ctx p_2).
  assert (Γ_1 ⊢ p_1 :Pat) by apply fresh_state_pat.
  assert (Γ_2 ⊢ p_2 :Pat) by admit (* need a vaiant of fresh_pat_typed *).

  rewrite denote_compose with (Γ1 := Γ_1) (Γ := Γ_2) (Γ2 := Γ_1).
  Focus 2. 
    apply types_f; auto.
  Focus 2.
    intros. 
    type_check. 
    apply types_g; auto.
  Focus 2.
    apply fresh_state_decompose.
    apply is_valid_fresh; validate.

  autounfold with den_db.
  rewrite merge_nil_l.


  set (p_1' := fresh_pat W1' Γ_2).
  set (Γ_1' := pat_to_ctx p_1').
  assert (Γ_1' ⊢ p_1' :Pat) by admit (* same lemma as above *).
  erewrite denote_compose with (Γ1 := Γ_2) (Γ := Γ_1') (Γ2 := Γ_2).
  Focus 2.
    apply types_g; auto.
  Focus 2.
    intros; type_check. 
  Focus 2.
    apply fresh_state_decompose.
    Search pat_to_ctx is_valid.
    admit (* lemma *).
  
  set (p_2' := fresh_pat W2' Γ_1').
  unfold compose_super.

  assert (size_Γ_2 : ⟦Γ_2⟧ = ⟦W2⟧).
  { unfold Γ_2. 
    erewrite size_pat_to_ctx; eauto.
  }
  assert (size_Γ_1 : ⟦Γ_1⟧ = ⟦W1⟧).
  { unfold Γ_1.
    rewrite denote_OCtx_fresh. auto. validate.
  }

  rewrite denote_tensor;
    [ | rewrite size_Γ_1; apply WF_Mixed; auto
      | rewrite size_Γ_2; apply WF_Mixed; auto ].
  rewrite merge_nil_l.
  rewrite denote_tensor. (* TODO: finish these *)

  rewrite denote_tensor. 
  admit (*???*).    
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
Print scale. Print Mplus.

Close Scope circ_scope.
Fixpoint kron_n n {m1 m2} (A : Matrix m1 m2) : Matrix (m1^n) (m2^n) :=
  match n with
  | 0    => Id 1
  | S n' => A ⊗ kron_n n' A
  end.
Notation "n ⨂ A" := (kron_n n A) : matrix_scope.
Open Scope circ_scope.

Open Scope matrix_scope.
Fixpoint prepare (ls : list nat) : Matrix 1%nat (2^(length ls)) :=
  fold_left (fun A x => ket x ⊗ A) ls (Id 1).

Definition pure {n} (vec : Matrix n 1%nat) : Matrix n n := vec × (vec †).

Definition prep α β : Matrix 2 2 := pure ((α.*|0⟩) .+ (β.*|1⟩)).
Lemma wf_prep : forall α β, WF_Matrix 2 2 (prep α β).
Proof.
  intros. unfold prep, pure.
  show_wf.
Qed.

Hint Unfold pure : den_db.


Lemma share_correct : forall n α β, 
      @denote _ _ (@Denote_Box _ _) (share n) (pure (α.*|0⟩ .+ β.*|1⟩))
    = pure (α.*(S n ⨂ |0⟩) .+ β.*(S n ⨂ |1⟩)).
Close Scope matrix_scope.
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
 Focus 2. intros. econstructor; [reflexivity | ].
                  econstructor; [ solve_merge | | | eauto]; [solve_merge | ].
    constructor. apply singleton_singleton.


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


