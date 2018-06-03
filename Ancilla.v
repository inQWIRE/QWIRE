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

(*
(* Replace given ancilla with an if statement to be filled with a dummy *)
Fixpoint swap_ancilla (loc : nat)  {W} (c dummy : Circuit W) := 
  match loc with 
  (* replace here *)
  | O => match c with 
        | gate assert0 p c' => gate meas p (fun p' => lift p' 
                                             (fun b => if b then dummy else c' unit ))
        | gate assert1 p c' => gate meas p (fun p' => lift p' 
                                             (fun b => if b then c' unit else dummy))
        | c''               => c''
        end
  (* replace later *)
  | S n' => match c with 
           | output p  => output p (* index does not exist *)
           | gate g p c' => gate g p (fun p' => swap_ancilla n' (c' p') dummy)
           | lift p c' => lift p (fun b => swap_ancilla n' (c' b) dummy)
           end
  end.

Definition swap_box_ancilla loc {W1 W2} (b : Box W1 W2) dummy :=
  match b with
  | box c => box (fun p => swap_ancilla loc (c p) dummy)
  end.

Definition Assertion_Correct {W1 W2} (c : Box W1 W2) := forall loc dummy, 
    c ≡ swap_box_ancilla loc c dummy.

Lemma id_correct : forall W, Assertion_Correct (box (fun (p : Pat W) => output p)).
Proof.
  intros W n dummy ρ Mρ.
  induction n; simpl; reflexivity.
Qed.

Lemma ancilla_free_correct : forall W (c : Circuit W), ancilla_free c -> 
                             Assertion_Correct (box (fun (p : Pat W) => c)).
Proof.
  intros W c AF n dummy ρ Mρ.
  induction AF as [|g p c' a0 a1 AF IH].
  + simpl. destruct n; reflexivity.
  + simpl.
    destruct n.
    - replace (swap_ancilla 0 (gate g p c') dummy) with (gate g p c').
      reflexivity.
      dependent destruction g.
      contradiction.
      contradiction.
    - (* true for the continuation from IH *)
      simpl in *.    
      unfold denote_box in *.
      simpl in *.
      unfold compose_super.
Admitted.

Definition init_assert0 :=
  box (fun (_ : Pat One) => 
    gate_ p  ← init0 @();
    gate_ () ← assert0 @p;
    output ()).

Lemma init_assert_correct0 :  Assertion_Correct init_assert0. 
Proof.  
  intros loc dummy ρ Mρ.
  simpl.
  unfold init_assert0.
  destruct loc.
  + simpl. reflexivity.
  + destruct loc. simpl.
    repeat (simpl; autounfold with den_db).
    apply mixed_state_id1 in Mρ. subst.
    Msimpl.
    repeat match goal with 
    | [ |- context[?A : Matrix ?m ?n]] => reduce_aux A
    | [e := _ : C |- _] => unfold e; clear e 
    end.
    unfold Splus.
    cbn.

Arguments Zero {m n}.

Lemma denote_zero : forall W pad input c, @denote_db_circuit W pad input c Zero = Zero.
Proof.
  intros W pad input c.
  induction c.
  + unfold denote_db_circuit.
    repeat (simpl; autounfold with den_db).
    Msimpl.
    rewrite Mmult_0_r.
    rewrite Mmult_0_l.
    reflexivity.
  + unfold denote_db_circuit.
    repeat (simpl; autounfold with den_db).
    Msimpl.
    rewrite Mmult_0_r.
    rewrite Mmult_0_l.
    reflexivity.
    
    Msimpl.
    simpl.
*)

Definition valid_ancillae {W} (c : Circuit W) : Prop := forall Γ Γ0, 
  (* Γ' == Γ0 ∙ Γ -> *) (* necessary? *)
  Γ ⊢ c:Circ -> (* <- is this right? *)
  ⟨ Γ0 | Γ ⊩ c ⟩ = ⟨! Γ0 | Γ ⊩ c !⟩.

Definition valid_ancillae_box {W1 W2} (c : Box W1 W2) := 
  Typed_Box c -> 
  denote_box true c = denote_box false c.

Definition valid_ancillae' {W} (c : Circuit W) := forall Γ Γ0 ρ, 
  Γ ⊢ c:Circ -> (* <- is this right? *)
  Mixed_State ρ ->
  trace (⟨! Γ0 | Γ ⊩ c !⟩ ρ) = 1.

Definition valid_ancillae_box' {W1 W2} (c : Box W1 W2) : Prop := forall ρ, 
  Typed_Box c -> 
  Mixed_State ρ ->
  trace (denote_box false c ρ) = 1.

Print valid_ancillae_box'.

Lemma valid_ancillae_equal : forall W (c : Circuit W), 
  valid_ancillae c <-> valid_ancillae' c.
Proof.
  intros.
  unfold valid_ancillae, valid_ancillae'.
  split.
  - intros VA.
  unfold valid_ancillae, valid_ancillae'.
  induction c.
Admitted.

Lemma valid_ancillae_box_equal : forall W1 W2 (c : Box W1 W2), 
  valid_ancillae_box c <-> valid_ancillae_box' c.
Proof.
  intros.
  destruct c.
Admitted.

Lemma size_fresh_state : forall W (Γ : Ctx), 
  size_ctx (fresh_state W Γ) = (size_ctx Γ + size_wtype W)%nat.
Proof.
  induction W; trivial.
  - intros. simpl. unfold add_fresh_state. simpl. rewrite size_ctx_app. reflexivity.
  - intros. simpl. unfold add_fresh_state. simpl. rewrite size_ctx_app. reflexivity.
  - intros. simpl. rewrite IHW2, IHW1. omega.
Qed.

Lemma size_fresh_state_o : forall W (Γ : OCtx), 
  is_valid Γ ->
  size_octx (fresh_state W Γ) = (size_octx Γ + size_wtype W)%nat.
Proof.
  induction W; trivial.
  - intros. simpl. destruct Γ. invalid_contradiction. simpl. 
    rewrite size_ctx_app. reflexivity.
  - intros. simpl. destruct Γ. invalid_contradiction. simpl. 
    rewrite size_ctx_app. reflexivity.
  - intros. simpl. rewrite IHW2, IHW1; trivial. omega.
    apply is_valid_fresh; easy.
Qed.

(* This relationship should be easy to prove. 
   Alternatively, we could just define one in terms of the other *)
Lemma valid_ancillae_unbox : forall W W' (c : Pat W -> Circuit W'),
  (forall p, valid_ancillae (c p)) <-> valid_ancillae_box (box (fun p => c p)).
Proof.
  intros.
  unfold valid_ancillae, valid_ancillae_box.
  unfold denote_box. unfold denote_circuit.
  unfold denote_db_box.
  unfold hoas_to_db_box.  
  split.
  - intros H T.
    specialize (H (fresh_pat W ∅) (fresh_state W ∅) ∅).
    simpl in *.
    rewrite size_fresh_state_o in H; [| apply valid_empty].
    simpl in H. rewrite H. easy.
    unfold Typed_Box in T. simpl in T. apply T.
    apply fresh_state_pat.
  - intros H p Γ Γ0 T.
    simpl in *.
    Search fresh_state fresh_pat.

    Search fresh_state.

    specialize (is_valid_fresh ∅ W valid_empty) as V.
    destruct (fresh_state W ∅). invalid_contradiction. 
    simpl in H.

Admitted.

Lemma valid_ancillae_unbox' : forall W W' (c : Box W W') (p : Pat W),
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
Admitted.

Lemma id_correct : forall W p, valid_ancillae (@output W p).
Proof.
  intros W p.
  unfold valid_ancillae.
  reflexivity.
Qed.

(* Also in Reversible.v *)
Lemma merge_singleton_append : forall W (Γ : Ctx), 
        Γ ⋓ (singleton (length Γ) W) = Valid (Γ ++ [Some W]). 
Proof. 
  induction Γ.
  - simpl. rewrite merge_nil_l. reflexivity.
  - unlock_merge. simpl in *.
    destruct a; simpl; rewrite IHΓ; reflexivity.
Qed.

Lemma add_fresh_merge : forall Γ W, 
  is_valid Γ ->
  add_fresh_state W Γ == singleton (get_fresh_var W Γ) W ∙ Γ. 
Proof.
  intros Γ W V.
  constructor.
  unfold add_fresh_state.
  simpl.
  destruct Γ.
  apply not_valid in V. contradiction.
  simpl.
  apply valid_valid.
  induction Γ.
  + simpl.
    unfold add_fresh_state.
    reflexivity.
  + unfold add_fresh_state.
    simpl.
    unfold get_fresh_var.
    simpl.
    rewrite <- merge_singleton_append.
    rewrite merge_comm.
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

(*
remove_pat (qubit 4) [None; None; None; None; Qubit] = [None; None; None; None]. !
*)

Lemma remove_bit_merge : forall (Γ Γ' : OCtx) v, Γ' == singleton v Bit ∙ Γ ->
                                            remove_pat (bit v)  Γ' = Γ.
Proof.      
  intros Γ Γ' v H.
  apply merge_fun_ind in H.
  dependent induction H.
  - destruct v; inversion x.
  - induction v.
    + simpl. unfold remove_pat. simpl. admit. (* Now this case isn't true either? *)
    + simpl. 
      unfold remove_pat in *.
      simpl in *.
      inversion IHv.
      (* Bah! 
         This needs to be true: The definition of remove_pat might
         need to be changed to trim trailing Nones. *)
Admitted.

Lemma remove_pat_valid : forall W Γ (p : Pat W), is_valid Γ -> is_valid (remove_pat p Γ).
Proof.
  intros W Γ p H.
  change(exists Γ', (remove_pat p Γ) = Valid Γ').  
  destruct Γ as [|Γ].
  apply not_valid in H. contradiction.
  clear H.
  generalize dependent Γ.
  induction p.
  - unfold remove_pat. simpl. eauto.
  - unfold remove_pat. simpl. eauto.
  - unfold remove_pat. simpl. eauto.
  - intros. 
    unfold remove_pat in *.
    simpl.
    rewrite fold_left_app.
    edestruct IHp1 as [Γ1 H1]. rewrite H1.
    apply IHp2.
Qed.

Lemma remove_bit_pred : forall Γ Γ' v, Γ' == (singleton v Bit) ∙ Γ ->
                        size_octx (remove_pat (bit v) Γ') = (size_octx Γ' - 1)%nat.
Proof.
  intros Γ Γ' v H.
  remember H as H'. clear HeqH'. apply remove_bit_merge in H'.
  destruct H. rewrite pf_merge in *. rewrite size_octx_merge by easy. 
  erewrite remove_bit_merge.
  2: constructor; trivial.
  unfold size_octx at 2. rewrite singleton_size. omega.
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
    erewrite denote_gate_circuit; [|apply pf1|apply t]. 
    erewrite denote_gate_circuit_unsafe; [|apply pf1|apply t].
    destruct Γ1' as [|Γ1']. invalid_contradiction.
    destruct g.
    - simpl. erewrite VA. reflexivity. eapply t0; [apply pf1|apply t].
    - simpl. erewrite VA. reflexivity. eapply t0; [apply pf1|apply t].
    - simpl. erewrite VA. reflexivity.
      eapply t0.
      2: constructor; apply singleton_singleton.
      dependent destruction p.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      unfold process_gate_state. simpl.
      apply (add_fresh_merge Γ1').
      assumption.
    - simpl. erewrite VA. reflexivity.      
      eapply t0. 
      2: constructor; apply singleton_singleton.
      dependent destruction p.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      apply (add_fresh_merge Γ1').
      assumption.
    - simpl. erewrite VA. reflexivity.      
      eapply t0. 
      2: constructor; apply singleton_singleton.
      dependent destruction p.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      apply (add_fresh_merge Γ1').
      assumption.
    - simpl. erewrite VA. reflexivity.
      eapply t0. 
      2: constructor; apply singleton_singleton.
      dependent destruction p.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      apply (add_fresh_merge Γ1').
      assumption.
    - dependent destruction p.
      dependent destruction t.
      simpl. erewrite VA. reflexivity.
      eapply t0.      
      2: constructor; apply singleton_singleton.
      apply singleton_equiv in s; subst.
      destruct Γ.        
      inversion pf1.
      rewrite merge_I_r in pf_merge. rewrite pf_merge in pf_valid. 
        apply not_valid in pf_valid. contradiction.
      eapply update_merge.
      apply pf1.
    - dependent destruction p.
      dependent destruction t.
      simpl. erewrite VA. reflexivity.
      eapply t0.
      2: constructor.
      constructor.
      apply remove_pat_valid. destruct pf1. assumption.
      rewrite merge_nil_l.
      apply remove_bit_merge.
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
    replace (size_octx Γ - 1)%nat with (size_octx (DBCircuits.remove_pat p Γ)).
    erewrite VA.
    erewrite VA.
    reflexivity.
    * dependent destruction WT.
      dependent destruction p.
      dependent destruction t.
      apply singleton_equiv in s. subst.
      apply remove_bit_merge in pf. subst.
      apply t0.
    * dependent destruction WT.
      dependent destruction p.
      dependent destruction t.
      apply singleton_equiv in s. subst.
      apply remove_bit_merge in pf. subst.
      apply t0.
    * dependent destruction WT.
      dependent destruction p.
      dependent destruction t.
      apply singleton_equiv in s. subst.
      eapply remove_bit_pred.
      apply pf.
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

            
(* Subsequent stuff doesn't work - not sure what it was supposed to do.

Lemma add_fresh_union_l : forall W (Γ : Ctx) Γ0 Γ1,
          Γ == Γ0 ∙ Γ1 ->
          add_fresh_state W Γ == (Γ0 ⋓ (singleton (length Γ) W)) ∙ Γ1.
Proof.
      type_check.

(* Not sure how this was supposed to go:
 eapply t0; [apply pf1|apply t].
    - simpl. erewrite VA. reflexivity. eapply t0; [apply pf1|apply t].
    - simpl. erewrite VA. reflexivity. eapply t0; [apply pf1|apply t].
    - simpl. erewrite VA. reflexivity. eapply t0; [apply pf1|apply t].
    - simpl. erewrite VA. reflexivity. eapply t0; [apply pf1|apply t].
    - simpl. erewrite VA. reflexivity. eapply t0; [apply pf1|apply t].
Search (_ ⊢ _ :Circ).


type_check. apply M. eapply t0. apply pf1. apply t.
    - simpl. erewrite VA. reflexivity. apply M. eapply t0. apply pf1. apply t.
    - simpl. erewrite VA. reflexivity.


    erewrite VA.
    Focus 2.
    
    Search process_gate_state process_gate_pat.
*)

Lemma process_gate_typing : forall W W' g p (c : Circuit W) Γ Γ0 Γ', Γ' == Γ0 ∙ Γ ->
                                           Γ ⊢ c :Circ ->
                                           Γ0 ⊢ p :Pat ->
  process_gate_state g p Γ' ⊢ c (process_gate_pat g p Γ') :Circ.

    apply DBCircuits.types_db_gate.


    destruct g.
    - simpl. erewrite VA. reflexivity. apply M. eapply t0. apply pf1. apply t.
    - simpl. erewrite VA. reflexivity. apply M. eapply t0. apply pf1. apply t.
    - simpl. erewrite VA. reflexivity.
      unfold DBCircuits.add_fresh_state.

      
      

 type_check.
      simpl.

apply M. eapply t0. apply pf1. apply t.
    - simpl. reflexivity. 
    - simpl. reflexivity. 
    - simpl. reflexivity. 
    - simpl. reflexivity. 
    - simpl. reflexivity. 
    - simpl. reflexivity. 
    - simpl. reflexivity. 
    - dependent destruction H. inversion H.
    - dependent destruction H. inversion H.


    erewrite H.
    Focus 2.
    unfold DBCircuits.process_gate_pat.
    simpl.
    unfold denote_circuit in *.
    simpl in *.
    erewrite VA. 2: admit.
    destruct g eqn:gE.
    - simpl. reflexivity. 
    - simpl. reflexivity. 
    - simpl. reflexivity. 
    - simpl. reflexivity. 
    - simpl. reflexivity. 
    - simpl. reflexivity. 
    - simpl. reflexivity. 
    - simpl. reflexivity. 
    - dependent destruction H. inversion H.
    - dependent destruction H. inversion H.
  + dependent destruction H.
    unfold valid_ancillae in *.      
    intros Γ0 Γ Γ' H1.
    unfold denote_circuit in *.
    simpl in *.
    replace (size_octx Γ - 1)%nat with (size_octx (DBCircuits.remove_pat p Γ)).
    erewrite H0.
    erewrite H0.
    reflexivity.
    apply H.
Admitted.    

*)
