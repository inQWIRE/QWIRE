Require Export Contexts.
Require Export HOASCircuits.
Require Export HOASLib.
Require Export DBCircuits.
Require Export Quantum.
Require Export Denotation.
Require Import Setoid.

(* Move to... composition? *)
Lemma denote_box_compat : forall (safe : bool) (W1 W2 : WType) (c : Box W1 W2) ρ ρ',
  ρ == ρ' ->
  denote_box safe c ρ == denote_box safe c ρ'.
Proof.
  intros.
  destruct c.
  unfold denote_box; simpl.
  rewrite add_fresh_split; simpl.
  remember (add_fresh_pat W1 []) as p.
  induction (c p).
  - matrix_denote.
  match goal with
  | |- ?A =>
        let A' := restore_dims_rec tac A in
        replace
        A
        with
        A'
  end.
  2:{ apply f_equal_gen; trivial.
      apply f_equal_gen; trivial.
      apply f_equal_gen; trivial.
      apply f_equal_gen; trivial.
      (* strange. should W1 be ∅ ? *)
Admitted.

Add Parametric Morphism b W1 W2 c : (@denote_box b W1 W2 c)
  with signature mat_equiv ==> mat_equiv as denote_box_mor.
Proof. intros. apply denote_box_compat; easy. Qed.


Fact denote_compose : forall safe w (c : Circuit w) (Γ : Ctx), 
     forall w' (f : Pat w -> Circuit w') (Γ0 Γ1 Γ1' Γ01 : Ctx) ρ,
  Γ ⊢ c :Circ ->
  Γ1 ⊢ f :Fun ->
  Γ1' ⩵ Γ1 ∙ Γ ->
  Γ01 ⩵ Γ0 ∙ Γ1 -> 
      denote_circuit safe (compose c f) Γ0 Γ1' ρ
    = compose_super 
        (denote_circuit safe (f (add_fresh_pat w Γ1)) Γ0 (add_fresh_state w Γ1)) 
        (denote_circuit safe c Γ01 Γ) ρ. 
Proof.
  intros safe w c Γ w' f Γ0 Γ1 Γ1' Γ01 ρ TP.
  dependent induction TP.
  - intros WT pf_merge1 pf_merge2.
    simpl.
    unfold compose_super.
    unfold denote_circuit.
    simpl.
    unfold pad.
    rewrite (ctx_wtype_size w p Γ) by easy.
    rewrite Nat.add_sub.
    rewrite size_fresh_ctx.
    destruct pf_merge1 as [V1 M1].
    replace (size_ctx Γ1') with (size_octx Γ1') by easy.
    rewrite M1 in *.
    rewrite size_octx_merge by easy.
    simpl.
    rewrite (ctx_wtype_size w p Γ t).
    admit. (* property about f being parametric *)
    (* ⟨ Γ0 | Γ1 ⋓ Γ2 ⊩ f p ⟩
    =  ⟨ Γ0 | fresh_state Γ2 ⊩ f (fresh_pat w Γ2) ⟩ ∘ ⟨ Γ1 ⊩ p ⟩ 
    *)
  - intros WT pf_merge1 pf_merge2.
    replace (compose (gate g p1 f0) f) 
      with (gate g p1 (fun p2 => compose (f0 p2) f)) 
      by auto.
    repeat rewrite denote_gate_circuit; fold_denotation.

    set (p2 := process_gate_pat g p1 Γ).
    set (Γ3'' := process_gate_state g p1 Γ).

(*
    evar (Γ4 : OCtx).
    set (Γ4' := process_gate_state g p1 Γ1').
    assert (pf2 : Γ2' ⩵ Γ2 ∙ Γ) by admit.
    assert (H_p2 : Γ2 ⊢ process_gate_pat g p1 Γ3' :Pat) by admit.
    assert (H_h : Γ3 ⊢ h :Fun) by auto.
    assert (pf3 : Γ3'' ⩵ Γ3 ∙ Γ2') by admit.

    specialize (H Γ2 Γ2' (process_gate_pat g p1 Γ3') pf2 H_p2 w' h Γ0 Γ3 Γ3'' H_h pf3).
    fold p2 in H.
*)
  (*  rewrite H. *)
    
    admit (* sort of close *).

  - admit.
Admitted.

(**********************)
(* Composition lemmas *)
(**********************)

Theorem inSeq_correct : forall W1 W2 W3 (g : Box W2 W3) (f : Box W1 W2) (safe : bool) ρ,
      Typed_Box g -> Typed_Box f ->
      denote_box safe (inSeq f g) ρ == 
      compose_super (denote_box safe g) (denote_box safe f) ρ.
Proof.
  intros W1 W2 W3 g f safe ρ types_g types_f.
  autounfold with den_db; simpl. 

  destruct f as [f]. 
  destruct g as [g].
  autounfold with den_db; simpl.

  destruct (add_fresh W1 []) as [p1 Γ1] eqn:E1. simpl.
  destruct (add_fresh W2 []) as [p2 Γ2] eqn:E2. simpl.

  rewrite add_fresh_split in E1, E2.
  inversion E1. inversion E2.
  
  assert (S1 : ⟦Γ1⟧ = ⟦W1⟧).
    rewrite <- H1. rewrite size_fresh_ctx; auto.
  assert (S2 : ⟦Γ2⟧ = ⟦W2⟧).
    rewrite <- H3. rewrite size_fresh_ctx; auto.

  rewrite H0, H1, H2, H3.

  replace 0%nat with (⟦[]:Ctx⟧:nat) by auto.
  replace (size_wtype W1) with (⟦Γ1⟧).
  replace (size_wtype W2) with (⟦Γ2⟧).
  
  specialize denote_compose as DC.
  unfold denote_circuit in DC.

  erewrite DC with (Γ1 := []) (Γ01 := []).
  simpl.
  unfold compose_super.
  rewrite H2, H3.
  reflexivity.
  * apply types_f. rewrite <- H0, <- H1. apply add_fresh_typed_empty. rewrite add_fresh_split. easy. 
  * unfold Typed_Box in types_g. intros Γ Γ' p pf wf_p.
    solve_merge.
    apply types_g. monoid. rewrite merge_nil_r. auto.
  * solve_merge.
  * split; [validate|monoid].
Qed.

Fact inPar_correct : forall W1 W1' W2 W2' (f : Box W1 W1') (g : Box W2 W2') (safe : bool)
     (ρ1 : Square (2^⟦W1⟧)) (ρ2 : Square (2^⟦W2⟧)),
     Typed_Box f -> Typed_Box g ->
     denote_box safe (inPar f g) (ρ1 ⊗ ρ2)%M == 
    (denote_box safe f ρ1 ⊗ denote_box safe g ρ2)%M.
Proof.  
(*
  intros W1 W1' W2 W2' f g safe ρ1 ρ2 types_f types_g mixed_ρ1 mixed_ρ2.
  destruct f as [f]. 
  destruct g as [g].
  repeat (autounfold with den_db; simpl).


  set (p_1 := add_fresh_pat W1 []).
  set (Γ_1 := add_fresh_state W1 []).
  set (p_2 := add_fresh_pat W2 Γ_1).
  set (Γ_2 := add_fresh_state W2 Γ_1).
  assert (Γ_1 ⊢ p_1 :Pat) by apply fresh_state_empty_types_fresh_pat.
  assert (Γ_2 ⊢ p_2 :Pat) by admit (* need a vaiant of fresh_pat_typed *).

  replace 0%nat with (⟦[]:Ctx⟧) by auto.
  replace (size_wtype W1 + size_wtype W2)%nat with (⟦Γ_2⟧).
  replace (size_wtype W1) with (⟦Γ_1⟧).
  replace (size_wtype W2) with (⟦add_fresh_state W2 []⟧).

  specialize denote_compose as DC. unfold denote_circuit in DC. 
  rewrite DC with (Γ1' := Γ_2) (Γ1 := Γ_2) (Γ := Γ_1). 
  set (Γ_3 := pat_to_ctx (fresh_pat W1' Γ_2)).
  rewrite DC with (Γ1' := fresh_state W1' Γ_2) (Γ1 := Γ_3) (Γ := Γ_2). clear DC.

  autounfold with den_db.
  repeat rewrite merge_nil_l.
  (*
  repeat rewrite denote_tensor.
  Search (⟨ _ | _ ⊩ output _ ⟩).
  rewrite denote_output.
  autorewrite with proof_db.*)
  admit (* stuck *). 
  * apply types_g; auto.
  * intros.
    destruct H1. econstructor. reflexivity.
    econstructor. 4: apply H2. assumption. 
    rewrite merge_comm in pf_merge. apply pf_merge.
    unfold Γ_3.
    Search (pat_to_ctx) fresh_pat.
    admit (* need a variant of fresh_pat_typed *).
  * unfold Γ_3.
    assert (valid_Γ_2 : is_valid Γ_2) by admit.
    generalize (fresh_state_decompose W1' Γ_2 valid_Γ_2); intros assertion.
    solve_merge.
    rewrite pf_merge. monoid.
  * apply types_f; auto.
  * intros. eapply compose_typing. apply types_g. apply H0.
    intros. econstructor. reflexivity. econstructor.
    destruct H3. assumption.
    2: apply H2. 2: apply H4. 
    rewrite merge_comm. destruct H3. apply pf_merge.
    destruct H1; constructor; [|rewrite merge_comm]; easy.
  * admit (* this is not true... *).
  * rewrite size_octx_fresh; auto. validate.
  * unfold Γ_1. rewrite size_octx_fresh. auto. validate.
  * unfold Γ_2, Γ_1. repeat rewrite size_octx_fresh. auto.
    validate. validate.
*)
Admitted.


Lemma HOAS_Equiv_inSeq : forall w1 w2 w3 (c1 c1' : Box w1 w2) (c2 c2' : Box w2 w3),
    Typed_Box c1 -> Typed_Box c1' ->  Typed_Box c2 -> Typed_Box c2' -> 
    c1 ≡ c1' -> c2 ≡ c2' -> (c2 · c1) ≡ (c2' · c1').
Proof.
  intros w1 w2 w3 c1 c1' c2 c2' T1 T1' T2 T2' E1 E2.
  intros ρ b.
  simpl_rewrite inSeq_correct; trivial.
  simpl_rewrite inSeq_correct; trivial.
  unfold compose_super.
  unfold HOAS_Equiv in *.
  rewrite E2. 
  rewrite E1. (* uses denote_box morphism *)
  reflexivity.
Qed.  
