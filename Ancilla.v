Require Import DBCircuits.
Require Import Denotation.
Require Import TypeChecking.

(*************************)
(* Assertion Correctness *)
(*************************)

Inductive not_assert : forall {W1 W2} (g : Gate W1 W2), Prop :=  
  | na_U       : forall W u, not_assert (@U W u)
  | na_NOT     : not_assert NOT
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

Definition valid_ancillae {W} (c : Circuit W) := forall Γ Γ0, 
  (* Γ' == Γ0 ∙ Γ -> *) (* necessary? *)
  Γ ⊢ c:Circ -> (* <- is this right? *)
  ⟨ Γ0 | Γ ⊩ c ⟩ = ⟨! Γ0 | Γ ⊩ c !⟩.

(*
Definition valid_ancillae {W1 W2} (c : Box W1 W2) := 
  denote_box true c = denote_box false c.
*)

Lemma id_correct : forall W p, valid_ancillae (@output W p).
Proof.
  intros W p.
  unfold valid_ancillae.
  reflexivity.
Qed.

(* Lemmas for ancilla_free_valid *)
Transparent merge.

Lemma append_merge : forall Γ W, 
  Valid (Γ ++ [Some W]) = (Valid Γ) ⋓ singleton (length Γ) W.
Proof.
  intros Γ W.
  induction Γ.
  + simpl.
    reflexivity.
  + simpl.
    simpl in *.
    inversion IHΓ.
    destruct a.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
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
    rewrite append_merge.
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
      2: rewrite merge_nil_r; reflexivity.
      apply valid_valid.
      rewrite merge_nil_r in pf_merge0.
      inversion pf_merge0.
      constructor.
      apply valid_valid.
      rewrite merge_nil_r.
      reflexivity.
    + destruct H.
      constructor.
      apply valid_valid.
      simpl in pf_merge.
      destruct (merge' (singleton v W) Γ) eqn:E. 
      rewrite pf_merge in pf_valid. apply not_valid in pf_valid. contradiction.
      inversion pf_merge.
      simpl.
      edestruct IHv.
      constructor.
      2: symmetry in E; apply E.
      apply valid_valid.
      inversion pf_merge0.
      reflexivity.
Qed.

Lemma remove_bit_merge : forall (Γ Γ' : OCtx) v, Γ' == singleton v Bit ∙ Γ ->
                                            remove_pat (bit v)  Γ' = Γ.
Proof.      
  intros Γ Γ' v H.
  apply merge_fun_ind in H.
  dependent induction H.
  - destruct v; inversion x.
  - induction v.
    + reflexivity. 
    + simpl. 
      unfold remove_pat in *.
      simpl in *.
      inversion IHv.
      (* Bah! 
         I think this needs to be true, the definition of remove_pat might
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

Lemma denote_singleton : forall v W Γ, SingletonCtx v W Γ -> 
                                  denote_OCtx Γ = 1%nat.
Proof.
  intros v W Γ H.
  generalize dependent v.
  induction Γ.
  - intros v H. inversion H.
  - intros v H. 
    inversion H; subst.
    reflexivity.
    simpl.
    eapply IHΓ.
    apply H3.
Qed.  

Lemma remove_bit_pred : forall Γ Γ' v, Γ' == (singleton v Bit) ∙ Γ ->
                        denote_OCtx (remove_pat (bit v) Γ') = (denote_OCtx Γ' - 1)%nat.
Proof.
  intros Γ Γ' v H.
  remember H as H'. clear HeqH'.
  apply denote_OCtx_merge in H.
  apply remove_bit_merge in H'.
  rewrite H, H'.
  rewrite (denote_singleton v Bit) by apply singleton_singleton.
  omega.
Qed.

Opaque merge.

Lemma ancilla_free_valid : forall W (c : Circuit W), 
 (*                          Γ ⊢ c :Circ ->  *)
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
      apply add_fresh_merge.
      assumption.
    - simpl. erewrite VA. reflexivity.      
      eapply t0. 
      2: constructor; apply singleton_singleton.
      dependent destruction p.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      apply add_fresh_merge.
      assumption.
    - simpl. erewrite VA. reflexivity.      
      eapply t0. 
      2: constructor; apply singleton_singleton.
      dependent destruction p.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      apply add_fresh_merge.
      assumption.
    - simpl. erewrite VA. reflexivity.
      eapply t0. 
      2: constructor; apply singleton_singleton.
      dependent destruction p.
      dependent destruction t.
      destruct pf1.
      rewrite merge_nil_l in pf_merge. subst.
      apply add_fresh_merge.
      assumption.
    - dependent destruction p.
      dependent destruction t.
      simpl. erewrite VA. reflexivity.
      eapply t0.      
      destruct Γ1'. destruct pf1. apply not_valid in pf_valid. contradiction.      
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
    replace (denote_OCtx Γ - 1)%nat with (denote_OCtx (DBCircuits.remove_pat p Γ)).
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
            

Lemma add_fresh_union_l : forall W Γ Γ0 Γ1,
          Γ == Γ0 ∙ Γ1 ->
          add_fresh_state W Γ == (Γ0 ⋓ (SingletonCtx (length Γ) W)) ∙ Γ1.

      type_check.
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
    replace (denote_OCtx Γ - 1)%nat with (denote_OCtx (DBCircuits.remove_pat p Γ)).
    erewrite H0.
    erewrite H0.
    reflexivity.
    apply H.
Admitted.    


(* Add a requirement that the circuit is well-typed? *)
Lemma ancilla_free_valid : forall W (c : Circuit W), ancilla_free c -> valid_ancillae c.
Proof.
  intros W c H.
  induction c.  
  + unfold valid_ancillae. reflexivity.
  + assert (forall p : Pat w2, valid_ancillae (c p)) as VA.
      intros p'.
      apply H0.
      dependent destruction H.
      apply H1.
    clear H0.
    intros Γ0 Γ Γ' M.
    unfold valid_ancillae in *. 
    erewrite denote_gate_circuit. 2: admit. 2: admit.
    erewrite denote_gate_circuit_unsafe. 2: admit. 2: admit.
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
    replace (denote_OCtx Γ - 1)%nat with (denote_OCtx (DBCircuits.remove_pat p Γ)).
    erewrite H0.
    erewrite H0.
    reflexivity.
    apply H.
Admitted.    

      
      2: rewrite merge_nil_l.
with (Γ0 := Γ0) (Γ1 := ∅).
      
      rewrite VA.
      simpl.

rewrite VA. reflexivity. 
    - simpl. unfold apply_new0. simpl. 
      unfold DBCircuits.get_fresh_var. simpl. 
      unfold DBCircuits.add_fresh_state. 
      simpl.
      destruct Γ.
      simpl.      
      Search DBCircuits.hoas_to_db Invalid.
      rewrite VA.

rewrite VA. reflexivity.
    - simpl. rewrite VA. reflexivity.
     
    inversion H; subst.
    inversion H6.
    apply H7.
    assumption.
    apply 

    inversion H; subst.
    specialize (H0
    apply H0 in H7.
    apply H7 in H0.



inversion H; subst. clear H. 
  unfold valid_ancillae.
  
  induction (c p).
  + unfold valid_ancillae.
    unfold denote_box. simpl.
    reflexivity.
    simpl.
    reflexivity.
  + unfold valid_ancillae in *.

    inversion H; subst.
    specialize (H0 

    assert ⟦ b ⟧ = ⟨ [] | DBCircuits.fresh_state w1 [] ⊩ unbox b (DBCircuits.fresh_pat w1 []) ⟩


    specialize denote_db_unbox with (b:=(c p)).  (w2:=W).
    replace (denote_box true box_ () ⇒ (c p)) with (⟦(box_ () ⇒ (c p))⟧) in H0.


    (* Apply IH *)
    rewrite denote_db_unbox in H0.
    unfold fresh_pat in IHn.
    unfold fresh_state in IHn.
    rewrite merge_nil_r.
    unfold compose_super.
    rewrite IHn.


    replace (denote_box true box_ () ⇒ (c p)) with (⟦c⟧) in H0.

    unfold denote_box in *.


    destruct g.
    unfold denote_box in *.
    - simpl in *.
      
    simpl in *.
    

(*
C0;
assert0 p;
C1; 
p' <- init0;
C2
output ;

=

C0;
rename p into p';
C1;
C2; 
*)