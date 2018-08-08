Require Import DBCircuits.
Require Import Denotation.
Require Import TypeChecking.

(*************************)
(* Assertion Correctness *)
(*************************)

Inductive not_assert : forall {W1 W2} (g : Gate W1 W2), Prop :=  
  | na_U       : forall W u, not_assert (@U W u)
  | na_NOT     : not_assert BNOT
  | na_init0   : not_assert init0
  | na_init1   : not_assert init1
  | na_new0    : not_assert new0
  | na_new1    : not_assert new1
  | na_meas    : not_assert meas
  | na_discard : not_assert discard.

Inductive ancilla_free {W} : Circuit W -> Prop := 
  | af_output : forall p, ancilla_free (output p)
  | af_gate : forall W1 W2 (g : Gate W1 W2) p c', 
                        not_assert g ->
                        (forall p, ancilla_free (c' p)) -> 
                        ancilla_free (gate g p c')
  | af_lift : forall p c, (forall b, ancilla_free (c b)) ->
                     ancilla_free (lift p c).

Inductive ancilla_free_box {W1 W2} : Box W1 W2 -> Prop :=
  | af_box : forall c, (forall p, ancilla_free (c p)) -> ancilla_free_box (box c).

Definition valid_ancillae {W} (c : Circuit W) : Prop := forall (Γ Γ0 : Ctx), 
  (* Γ' == Γ0 ∙ Γ -> *) (* necessary? *)
  Γ ⊢ c:Circ -> (* <- is this right? *)
  ⟨ Γ0 | Γ ⊩ c ⟩ = ⟨! Γ0 | Γ ⊩ c !⟩.

Definition valid_ancillae_box {W1 W2} (c : Box W1 W2) := 
  Typed_Box c -> 
  denote_box true c = denote_box false c.

Definition valid_ancillae' {W} (c : Circuit W) := forall (Γ Γ0 : Ctx) ρ, 
  Γ ⊢ c:Circ -> (* <- is this right? *)
  Mixed_State ρ ->
  trace (⟨! Γ0 | Γ ⊩ c !⟩ ρ) = 1.

Definition valid_ancillae_box' {W1 W2} (c : Box W1 W2) : Prop := forall ρ, 
  Typed_Box c -> 
  Mixed_State ρ ->
  trace (denote_box false c ρ) = 1.

Proposition valid_ancillae_equal : forall W (c : Circuit W), 
  valid_ancillae c <-> valid_ancillae' c.
Proof.
  intros.
  unfold valid_ancillae, valid_ancillae'.
  split.
  - intros VA.
  unfold valid_ancillae, valid_ancillae'.
  induction c.
Abort.

Fact valid_ancillae_box_equal : forall W1 W2 (c : Box W1 W2), 
  valid_ancillae_box c <-> valid_ancillae_box' c.
Proof.
  intros.
  destruct c.
Admitted.

(* This relationship should be easy to prove. 
   Alternatively, we could just define one in terms of the other *)
Fact valid_ancillae_unbox : forall W W' (c : Pat W -> Circuit W'),
  (forall p, valid_ancillae (c p)) <-> valid_ancillae_box (box (fun p => c p)).
Proof.
  intros.
  unfold valid_ancillae, valid_ancillae_box.
  unfold denote_box. unfold denote_circuit.
  unfold denote_db_box.
  unfold hoas_to_db_box.  
  split.
  - intros H T.
    specialize (H (add_fresh_pat W []) (add_fresh_state W []) []).
    simpl in *.
    rewrite size_fresh_ctx in H.
    simpl in H. 
    unfold add_fresh_state, add_fresh_pat in *.
    destruct (add_fresh W []) as [p Γ] eqn:E.
    simpl in *.
    rewrite H. 
    easy.
    unfold Typed_Box in T. simpl in T. apply T.
    (* Lemma to add to DBCircuits *)
    admit.
  - intros H p Γ Γ0 T.
    simpl in *.
Admitted.

Proposition valid_ancillae_unbox' : forall W W' (c : Box W W') (p : Pat W),
  valid_ancillae (unbox c p) <-> valid_ancillae_box c.
Proof.
  intros W W' c p.
  unfold valid_ancillae, valid_ancillae_box.
  unfold denote_box.
  unfold denote_db_box.
  destruct c.
  simpl.
  unfold denote_circuit.
  simpl.
  split.
  - intros H.    
    admit.
Abort.

Lemma id_correct : forall W p, valid_ancillae (@output W p).
Proof.
  intros W p.
  unfold valid_ancillae.
  reflexivity.
Qed.

Lemma update_merge : forall (Γ Γ' :Ctx) W W' v, Γ' == singleton v W ∙ Γ ->
   Valid (update_at Γ' v (Some W')) == singleton v W' ∙ Γ.
Proof.
  intros Γ Γ' W W' v H.
  generalize dependent Γ.
  generalize dependent Γ'.
  induction v.
  - intros Γ' Γ H.
    simpl in *.
    apply merge_fun_ind in H.
    inversion H; subst.
    simpl.
    constructor.
    apply valid_valid.
    reflexivity.
    inversion H5; subst.
    inversion H4; subst.
    constructor.
    apply valid_valid.
    reflexivity.
    inversion H4; subst.
    constructor.
    apply valid_valid.
    reflexivity.
  - intros Γ' Γ H.
    simpl.
    destruct Γ.
    + destruct H.
      rewrite merge_nil_r in pf_merge. inversion pf_merge.
      simpl.
      edestruct IHv.
      constructor.
      2: rewrite merge_nil_r; easy.
      apply valid_valid.
      rewrite merge_nil_r in pf_merge0.
      inversion pf_merge0.
      constructor.
      apply valid_valid.
      rewrite merge_nil_r.
      easy.
    + destruct H.
      constructor.
      apply valid_valid.
      unlock_merge. simpl in *.
      destruct (merge' (singleton v W) Γ) eqn:E. 
      rewrite pf_merge in pf_valid. invalid_contradiction. 
      simpl.
      edestruct IHv.
      constructor.
      2: symmetry in E; unlock_merge; apply E.
      apply valid_valid.      
      unlock_merge.
      rewrite <- pf_merge0.
      inversion pf_merge.
      simpl.
      easy.
Qed.

Lemma change_type_singleton : forall v W W', change_type v W' (singleton v W) = singleton v W'.
Proof.
  intros v W W'.
  unfold change_type.
  erewrite update_at_singleton.
  reflexivity.
  apply singleton_singleton.
  apply singleton_singleton.
Qed.

Lemma ancilla_free_valid : forall W (c : Circuit W), 
                           ancilla_free c -> 
                           valid_ancillae c.
Proof.
  intros W c AF.
  induction c.  
  + unfold valid_ancillae. reflexivity.
  + assert (forall p : Pat w2, valid_ancillae (c p)) as VA.
      intros p'.
      apply H.
      dependent destruction AF.
      apply H1.
    clear H.  
    unfold valid_ancillae in *. 
    intros Γ0 Γ1 WT.
    dependent destruction WT.
    destruct Γ as [|Γ], Γ2 as [|Γ2]; try invalid_contradiction.
    erewrite denote_gate_circuit; [|apply pf1|apply t]. 
    erewrite denote_gate_circuit_unsafe; [|apply pf1|apply t].


    destruct g.
    - simpl. erewrite VA. reflexivity. eapply t0; [apply pf1|apply t].
    - simpl. erewrite VA. reflexivity. eapply t0; [apply pf1|apply t].
    - simpl. erewrite VA. reflexivity.
      eapply t0.
      2: constructor; apply singleton_singleton.
      dependent destruction p.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. inversion pf_merge. subst.
      unfold process_gate_state. simpl.
      split. validate.
      rewrite merge_comm, merge_singleton_append.
      easy.
    - simpl. erewrite VA. reflexivity.      
      eapply t0. 
      2: constructor; apply singleton_singleton.
      dependent destruction p.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. inversion pf_merge. subst.
      unfold process_gate_state. simpl.
      split. validate.
      rewrite merge_comm, merge_singleton_append.
      easy.
    - simpl. erewrite VA. reflexivity.      
      eapply t0. 
      2: constructor; apply singleton_singleton.
      dependent destruction p.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. inversion pf_merge. subst.
      unfold process_gate_state. simpl.
      split. validate.
      rewrite merge_comm, merge_singleton_append.
      easy.
    - simpl. erewrite VA. reflexivity.
      eapply t0. 
      2: constructor; apply singleton_singleton.
      dependent destruction p.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. inversion pf_merge. subst.
      unfold process_gate_state. simpl.
      split. validate.
      rewrite merge_comm, merge_singleton_append.
      easy.
    - dependent destruction p.
      dependent destruction t.
      simpl. erewrite VA. reflexivity.
      eapply t0.      
      2: constructor; apply singleton_singleton.
      apply singleton_equiv in s; subst.
      unfold process_gate_state. simpl.
      split. validate. 
      unfold change_type.
      eapply update_merge.
      apply pf1.
    - simpl. erewrite VA. reflexivity. eapply t0; [apply pf1|apply t].
    - dependent destruction p.
      dependent destruction t.
      simpl. erewrite VA. reflexivity.
      eapply t0.
      2: constructor.
      constructor.
      validate.
      rewrite merge_nil_l.
      assert (t' : Γ ⊢ c () :Circ). apply (t0 ∅). split. 
        validate. rewrite merge_nil_l. easy. constructor.
      specialize (types_circ_types_pat w Γ (c ()) t') as [w' [p' TP]].  
      unfold process_gate_state; simpl.
      apply ctx_octx.
      apply (remove_bit_merge _ _ w' p'); trivial. 
      apply singleton_equiv in s. subst.
      assumption.
    - dependent destruction AF. inversion H.
    - dependent destruction AF. inversion H.
  + dependent destruction AF.
    assert (forall b, valid_ancillae (c b)) as VA. intros; apply H; apply H0.
    clear H.
    unfold valid_ancillae in *.      
    intros Γ Γ0 WT.
    unfold denote_circuit in *.
    simpl in *.
    replace (size_ctx Γ - 1)%nat with (size_ctx (DBCircuits.remove_pat p Γ)).
    erewrite VA.
    erewrite VA.
    reflexivity.
    * dependent destruction WT.
      dependent destruction p.
      dependent destruction t.
      apply singleton_equiv in s. subst.
      specialize (types_circ_types_pat w Γ2 (c true) (t0 true)) as [w' [p' TP]].      
      destruct Γ2 as [|Γ2]; try invalid_contradiction.
      rewrite (remove_bit_merge Γ2 Γ w' p'); easy. 
    * dependent destruction WT.
      dependent destruction p.
      dependent destruction t.
      apply singleton_equiv in s. subst.
      specialize (types_circ_types_pat w Γ2 (c false) (t0 false)) as [w' [p' TP]].   
      destruct Γ2 as [|Γ2]; try invalid_contradiction.
      rewrite (remove_bit_merge Γ2 Γ w' p'); easy. 
    * dependent destruction WT.
      dependent destruction p.
      dependent destruction t.
      apply singleton_equiv in s. subst.
      specialize (types_circ_types_pat w Γ2 (c true) (t0 true)) as [w' [p' TP]].      
      destruct Γ2 as [|Γ2]; try invalid_contradiction.
      rewrite (remove_bit_pred Γ2 Γ); easy.
Qed.

Lemma ancilla_free_box_valid : forall W W' (c : Box W W'), 
    ancilla_free_box c -> 
    valid_ancillae_box c.
Proof.
  intros.
  destruct H.
  apply valid_ancillae_unbox.
  intros p. 
  apply ancilla_free_valid.
  apply H.
Qed.

(* *)
