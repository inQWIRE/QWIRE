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

Lemma init_ket1 : ⟦init true⟧ I1 = |1⟩⟨1|. 
Proof.
  matrix_denote.
  Msimpl.
  reflexivity.
Qed.

(*********************)
(* Identity circuits *)
(*********************)

(* Qubit form *) 
Lemma unitary_transpose_id_qubit : forall (U : Unitary Qubit),
   unitary_transpose U ≡ id_circ.
Proof.
  Locate "≡".
  unfold HOAS_Equiv.
  intros U ρ safe pf_ρ.
  destruct (unitary_gate_unitary U) as [WF inv].
  simpl in *.
  matrix_denote.
  setoid_rewrite denote_unitary_transpose.
  simpl in *; Msimpl.
  repeat rewrite Mmult_assoc; try rewrite inv.
  repeat rewrite <- Mmult_assoc; try rewrite inv.
  Msimpl.     
  reflexivity.
Qed.

(*
Lemma apply_U_trans : forall n W (U : Unitary W) li,
    compose_super (apply_U n U li) (apply_U n (trans U) li) = fun x => x.
Proof.
  intros n W U li.
  unfold compose_super.
  apply functional_extensionality.
  intros ρ.
  destruct W.
  - simpl. Search trans.
    unfold apply_to_first.
    unfold apply_qubit_unitary.
*)    
  
Lemma unitary_transpose_id : forall W (U : Unitary W),
  unitary_transpose U ≡ id_circ.
Proof.
  intros W U ρ safe WF.
  matrix_denote.
  rewrite add_fresh_split.
  rewrite subst_pat_fresh by constructor.
  unfold denote_db_box. simpl.  
  unfold compose_super, super, pad.
  repeat rewrite Nat.add_sub.
  rewrite Nat.sub_diag.
  rewrite Nat.leb_refl.
  Msimpl.
  destruct W; try solve [inversion U].
  - simpl.
    unfold denote_pat; simpl.
    unfold swap_list; simpl.
    unfold swap_two; simpl.
    Msimpl.
    rewrite Mmult_assoc.
    unfold apply_qubit_unitary.
    unfold super. simpl.
    destruct (unitary_gate_unitary U) as [WFU inv].
    assert (WFU' : WF_Matrix _ _ (⟦U⟧†)) by auto with wf_db.
    simpl_rewrite @denote_unitary_transpose.
    simpl in *. Msimpl.
    repeat rewrite Mmult_assoc. rewrite inv.
    repeat rewrite <- Mmult_assoc. rewrite inv.
    Msimpl.
    easy.
  - simpl.
    unfold denote_pat; simpl.
    Msimpl.
    rewrite Mmult_assoc.
    unfold super. simpl.
    remember (W1 ⊗ W2) as W.
    remember (pat_to_list (add_fresh_pat W [])) as li.
    destruct (denote_ctrls_unitary W (⟦W⟧) U li ) as [WFU inv].
      apply forallb_forall. intros.
      rewrite Nat.ltb_lt.
      rewrite Heqli in H.
      simpl.
      rewrite (ctx_wtype_size _ (add_fresh_pat W []) (add_fresh_state W [])).
      eapply pat_to_list_bounded.
      split. validate. rewrite merge_nil_r. easy.
      eapply get_fresh_typed.
      rewrite get_fresh_split.
      specialize (add_fresh_state_merge W [] _ eq_refl) as AFE.
      rewrite merge_nil_l in AFE. inversion AFE. rewrite <- H1. easy.
      rewrite <- add_fresh_pat_eq.
      rewrite subst_pat_fresh by constructor.
      easy.
      apply add_fresh_typed_empty.
      rewrite add_fresh_split. easy.
      subst.
      rewrite size_wtype_length.
      easy.
    replace (size_wtype W1 + size_wtype W2)%nat with  (⟦ W ⟧) by (subst;easy).
    rewrite denote_ctrls_transpose.
    remember (denote_ctrls (⟦ W ⟧) U li) as A.
    remember (swap_list (⟦ W ⟧) li) as S.
    rewrite <- (Mmult_assoc _ _ _ _ _ (A × ρ) _).
    rewrite <- (Mmult_assoc _ _ _ _ _ A ρ).
    rewrite inv. Msimpl.
    rewrite (Mmult_assoc _ _ _ _ ρ _ A).
    rewrite inv. Msimpl.
    rewrite Mmult_assoc.
    easy.
Qed.    

(****************)
(* Coin Tossing *)
(****************)

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
Proof. matrix_denote. Msimpl. solve_matrix. Qed.

Lemma wf_biased_coin : forall c, WF_Matrix 2 2 (biased_coin c).
Proof.
  intros; show_wf.
Qed.

Hint Resolve wf_biased_coin : wf_db.
Hint Unfold super_Zero : den_db. 

(* Uses denote_compose: *)
(*
Proposition flips_correct : forall n, ⟦coin_flips n⟧ I1 = biased_coin (1/(2^n)).
Proof.
  induction n.  
  + matrix_denote. Msimpl. solve_matrix.
  + simpl.
    repeat (simpl; autounfold with den_db). 
    replace 0%nat with (⟦[]:Ctx⟧) by auto.
    specialize denote_compose as DC. unfold denote_circuit in DC.

    rewrite DC with (Γ := []) (Γ1 := []) (Γ1' := []);
    [ | apply unbox_typing; [type_check | apply coin_flips_WT]
    | type_check
    | solve_merge | solve_merge].

       (* Apply IH *)
       rewrite denote_db_unbox in IHn.
       unfold add_fresh_pat in IHn.
       unfold add_fresh_state in IHn.
       unfold compose_super.
       unfold denote_circuit in IHn.
       setoid_rewrite IHn.

    (* Continue reducing *)
    repeat (autounfold with den_db; simpl).
    Msimpl.
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
Abort.
*)

(* The following uses a lemma (scale_safe) that is worth proving, but not yet proven *)
(* We abort this lemma and prove a more general version below *)
Proposition flips_lift_correct : forall n, ⟦coin_flips_lift n⟧ I1 = biased_coin (1/(2^n)).
Proof.
  induction n.
  + matrix_denote. Msimpl. solve_matrix.
  + simpl.
    matrix_denote.
    Msimpl.
    simpl in IHn. unfold denote_box, denote_db_box in IHn. simpl in IHn.
    unfold hoas_to_db_box in IHn. simpl in IHn.
    destruct (coin_flips_lift n) eqn:EC.
    unfold remove_pat. simpl.
    replace ((box c) $ ()) with (c ()) by reflexivity.
    replace (⟨1| × (|0⟩⟨0| × (hadamard × |0⟩⟨0| × hadamard) × |0⟩⟨0| .+ 
                    |1⟩⟨1| × (hadamard × |0⟩⟨0| × hadamard) × |1⟩⟨1|) × |1⟩)
      with ((1/2) .* 'I_1) by solve_matrix. 
    assert (scale_safe : forall safe w i j (c : DeBruijn_Circuit w) a ρ, 
               denote_db_circuit safe i j c (a .* ρ) = a .* denote_db_circuit safe i j c ρ). admit.
    rewrite scale_safe.
    setoid_rewrite IHn.
    solve_matrix.
    - rewrite Cmult_plus_distr_l.
      Csimpl.
      rewrite Cplus_assoc.
      rewrite Cinv_mult_distr; [|nonzero|apply Cpow_nonzero; lra].         
      rewrite <- Copp_mult_distr_r.
      clra.
    - rewrite Cinv_mult_distr; [|nonzero|apply Cpow_nonzero; lra].         
      easy.
Abort.

(* This generalizes the theorem to get around the lemma *)
Lemma flips_lift_correct_gen : forall n a, ⟦coin_flips_lift n⟧ (a .* I1) = a .* biased_coin (1/(2^n)).
Proof.
  induction n.
  + matrix_denote. Msimpl. solve_matrix.
  + intros a.
    simpl.
    matrix_denote.
    Msimpl.
    simpl in IHn. unfold denote_box, denote_db_box in IHn. simpl in IHn.
    unfold hoas_to_db_box in IHn. simpl in IHn.
    destruct (coin_flips_lift n) eqn:EC.
    unfold remove_pat. simpl.
    replace ((box c) $ ()) with (c ()) by reflexivity.
    match goal with 
    [|- _ .+ ?f ?ρ = _] => replace ρ with ((a/2 .* 'I_1))
    end.
    2: solve_matrix; rewrite (Cmult_comm (/√2)), <- Cmult_assoc; autorewrite with C_db; easy.
    setoid_rewrite (IHn (a / 2)).
    solve_matrix.
    - rewrite (Cmult_comm _ a).
      repeat rewrite <- Cmult_assoc.
      rewrite <- Cmult_plus_distr_l.
      autorewrite with C_db.
      rewrite (Cmult_plus_distr_l (/2)).
      autorewrite with C_db.
      rewrite Cplus_assoc.
      autorewrite with C_db.      
      rewrite Cinv_mult_distr; [|nonzero|apply Cpow_nonzero; lra].         
      easy.
    - rewrite Cinv_mult_distr; [|nonzero|apply Cpow_nonzero; lra].         
      rewrite Cmult_assoc.
      easy.
Qed.

Lemma flips_lift_correct : forall n, ⟦coin_flips_lift n⟧ I1 = biased_coin (1/(2^n)).
Proof.
  intros n.
  rewrite <- Mscale_1_l, <- (Mscale_1_l _ _ I1).
  apply flips_lift_correct_gen.
Qed.


(***********)
(* sharing *)
(***********)

(*
Proposition denote_circuit_subst : forall w (c : Circuit w) Γ, Types_Circuit Γ c ->
      forall pad n σ, 
      WF_σ Γ (get_σ σ) ->
      ⟨ 
      ⟨ pad | n | c | σ ⟩ 
    = compose_super ⟨pad | n | c | st_{n}⟩
                    (super (swap_list n (get_σ σ))).
Proof.
  induction 1; intros.
  * simpl. 
    erewrite subst_id; eauto.
    admit. admit.
  * simpl. erewrite H; eauto. admit.
Abort.

Proposition denote_unbox : forall n w1 w2 (b : Box w1 w2) Γ1 p σ, 
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

Abort.
*)
  
Hint Unfold apply_box : den_db.

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
Close Scope matrix_scope.

(*
Proposition share_correct : forall n α β, 
      (@denote _ _ (@Denote_Box _ _) (share n) (pure (α.*|0⟩ .+ β.*|1⟩))
    = pure (α.*(S n ⨂ |0⟩) .+ β.*(S n ⨂ |1⟩)))%M.
Proof.
  induction n; intros.
  * repeat (autounfold with den_db; simpl).
    autorewrite with M_db.
    reflexivity.
  * repeat (autounfold with den_db; simpl).
    autorewrite with M_db. 
    setoid_rewrite kron_adjoint.
    autorewrite with M_db. 

    remember (singleton 1%nat Qubit) as Γ1.
    remember (singleton 0%nat Qubit) as Γ2.
    remember (Γ1 ⋓ Γ2) as Γ1'.

    assert (size_Γ1' : ⟦Γ1'⟧ = 2%nat).
    { subst. auto. }
    
    assert (Γ2 ⊢ qubit 0%nat :Pat).
    { constructor. subst. constructor. }

    unfold add_fresh_state. simpl.
   
    replace 2%nat with (⟦Γ1'⟧) by auto.
    replace (0%nat) with (⟦[]:Ctx⟧) by auto. 
    replace (S (⟦∅⟧)) with 1%nat by auto.
    destruct Γ1' as [|Γ1']. inversion size_Γ1'.
    replace ([Some Qubit; Some Qubit]) with Γ1'. 
    2: subst; unlock_merge; simpl in *; inversion HeqΓ1'; easy. 
    
    unfold process_gate_state. simpl.
    specialize denote_compose as DC. unfold denote_circuit in DC.
    rewrite DC with (Γ0 := []) (Γ := Γ1) (Γ1 := Γ2) (Γ1' := Γ1') (Γ01 := Γ2);
    [ | apply share_WT; type_check; repeat constructor
    | intros; simpl; type_check
    | rewrite HeqΓ1'; solve_merge | solve_merge].
    2: unlock_merge; simpl; validate.
    
    admit (* need padding lemma *).
Abort.
*)

(* Can we multiply 16 x 16 matrices? Yes, we can!
Example test : ((swap ⊗ swap) × (swap ⊗ swap) = 'I_16)%M.
Proof. 
  solve_matrix. 
  all: unfold Nat.ltb; simpl; rewrite andb_false_r; reflexivity.
Qed. *)


(***********************)
(* Deutsch's Algorithm *)
(***********************)


Delimit Scope circ_scope with qc.
Close Scope circ_scope. 
Open Scope matrix_scope.

(* Version on an abstract unitary gate *)

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

(* f(x) = 1. Unitary: Id ⊗ X *)
Definition f3 : Matrix 4 4 := Id 2 ⊗ σx.

Definition U_constant (U : Unitary (Qubit ⊗ Qubit)%qc) := 
  apply_U 2 U [0;1]%nat = super f0 \/ apply_U 2 U [0;1]%nat = super f3.
Definition U_balanced (U : Unitary (Qubit ⊗ Qubit)%qc) := 
  apply_U 2 U [0;1]%nat = super f1 \/ apply_U 2 U [0;1]%nat = super f2.

Lemma f2_WF : WF_Matrix 4 4 f2. Proof. show_wf. Qed.
Hint Resolve f2_WF : wf_db.

Close Scope matrix_scope.
Open Scope circ_scope.  
(* Set Ltac Profiling. *)

(* One could quibble with the following proofs that they're true vacuously since
   we don't have a unitary corresponding to f0, f2 or f3 (though f1 exists).
   However, we could easily add them, and the proofs of each case mirrors that
   of f1 (=CNOT). *)

Lemma U_deutsch_constant : forall U_f, U_constant U_f -> 
                                ⟦U_deutsch U_f⟧ I1 = |0⟩⟨0|.
Proof.
  Opaque apply_U.
  intros U_f H.
  simpl.
  unfold denote_box. unfold denote_db_box. simpl.
  unfold subst_var. simpl.
  destruct H; setoid_rewrite H.
  Transparent apply_U.
  - (* f0 *)
    matrix_denote.
    Msimpl.
    unfold f0.
    solve_matrix.
    rewrite (Cmult_comm (/ √2) _).
    rewrite Cmult_assoc.
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    reflexivity.
  - (* f3 *)
    matrix_denote.
    Msimpl.
    unfold f3.
    solve_matrix.
    rewrite (Cmult_comm (/ √2) _).
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    reflexivity.
Qed.
  
Lemma U_deutsch_balanced : forall U_f, U_balanced U_f -> 
                                ⟦U_deutsch U_f⟧ I1 = |1⟩⟨1|.
Proof.
  Opaque apply_U.
  intros U_f H.
  simpl.
  unfold denote_box. unfold denote_db_box. simpl.
  unfold subst_var. simpl.
  destruct H; setoid_rewrite H.
  Transparent apply_U.
  + (* f1 *)
    matrix_denote.
    Msimpl.
    unfold f1.
    solve_matrix.
    rewrite (Cmult_comm (/ √2) _).
    rewrite Cmult_assoc.
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    reflexivity.
  + (* f2 *)
    matrix_denote.
    Msimpl.
    unfold f2.
    solve_matrix.
    rewrite (Cmult_comm (/ √2) _).
    repeat rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    reflexivity.
Qed.

(* Show Ltac Profile *)

(* Slightly faster to destruct 'balanced' last 
Lemma deutsch_balanced'' : forall U_f, balanced U_f -> 
                                ⟦deutsch U_f⟧ I1 = |1⟩⟨1|.
Proof.
  intros U_f H.
  repeat (simpl; autounfold with den_db). 
  specialize (unitary_gate_unitary U_f). intros [WFU UU].
  simpl in WFU.
  Msimpl.
  solve_matrix.
  all: destruct H; rewrite H; clear.  
  + (* Cell (0,0), f1 *)
    unfold f1.
    autounfold with M_db.
    simpl.
    autorewrite with C_db.
    reflexivity.
  + (* Cell (0,0), f2 *)
    unfold f2.
    autorewrite with C_db.
    reflexivity.
  + (* Cell (1,1), f1 *)
    unfold f1.
    autounfold with M_db.
    simpl.
    autorewrite with C_db.
    rewrite (Cmult_comm (/ √2) _).
    rewrite Cmult_assoc.
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    reflexivity.
  + (* Cell (1,1), f2 *)
    unfold f2.
    simpl.
    autorewrite with C_db.
    rewrite (Cmult_comm (/ √2) _).
    rewrite Cmult_assoc.
    rewrite (Cmult_assoc 2 (/2)).
    autorewrite with C_db. 
    rewrite <- Cmult_assoc.
    autorewrite with C_db. 
    reflexivity.
Qed.
*)

(* A more explicit version that uses concrete boxed circuits *)

Locate "||".

Definition fun_to_box (f : bool -> bool) : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  match (f false), (f true) with
  | false, false => id_circ
  | false, true  => CNOT
  | true,  false => _X ∥ id_circ ;; CNOT ;; _X ∥ id_circ
  | true,  true  => id_circ ∥ _X
  end.                             
                              
Definition constant (f : bool -> bool) := f true = f false.

Definition balanced (f : bool -> bool) := f true <> f false.

Lemma deutsch_constant_concrete : forall f, constant f -> 
                                  ⟦deutsch (fun_to_box f)⟧ I1 = |0⟩⟨0|.
Proof.
  intros f H.
  unfold fun_to_box, constant in *. 
  destruct (f true), (f false); try discriminate H.
  - matrix_denote.
    Msimpl.
    solve_matrix.
    rewrite (Cmult_comm (/√2) _).
    repeat (rewrite (Cmult_assoc 2 (/2)); autorewrite with C_db).
    easy.
  - matrix_denote.
    Msimpl.
    solve_matrix.
    rewrite (Cmult_comm (/√2) _).
    repeat (rewrite (Cmult_assoc 2 (/2)); autorewrite with C_db).
    easy.
Qed.

Lemma deutsch_balanced_concrete : forall f, balanced f -> 
                                  ⟦deutsch (fun_to_box f)⟧ I1 = |1⟩⟨1|.
Proof.
  intros f H.
  unfold fun_to_box, balanced in *. 
  destruct (f true), (f false); try contradiction.
  - matrix_denote.
    Msimpl.
    solve_matrix.
    rewrite (Cmult_comm (/√2) _).
    repeat (rewrite (Cmult_assoc 2 (/2)); autorewrite with C_db).
    easy.
  - matrix_denote.
    Msimpl.
    solve_matrix.
    rewrite (Cmult_comm (/√2) _).
    repeat (rewrite (Cmult_assoc 2 (/2)); autorewrite with C_db).
    easy.
Qed.


(*************************)
(* Quantum Teleportation *)
(*************************)


Definition EPR00 : Matrix 4 4 :=
  fun x y => match x, y with
             | 0, 0 => 1/2
             | 0, 3 => 1/2
             | 3, 0 => 1/2
             | 3, 3 => 1/2
             | _, _ => 0
             end.

Lemma bell00_spec :  ⟦bell00⟧ I1  = EPR00.
Proof.
  repeat (simpl; autounfold with den_db). 
  Msimpl. 
  solve_matrix.
Qed.

(* Works, but commented out for efficient compilation *)
Definition M_alice (ρ : Matrix 4 4) : Matrix 4 4 :=
  fun x y => 
  match x, y with 
  | 0, 0 =>  (ρ 0%nat 0%nat + ρ 3%nat 0%nat + ρ 0%nat 3%nat + ρ 3%nat 3%nat) / 2
  | 1, 1 =>  (ρ 1%nat 1%nat + ρ 2%nat 1%nat + ρ 1%nat 2%nat + ρ 2%nat 2%nat) / 2
  | 2, 2 =>  (ρ 0%nat 0%nat - ρ 3%nat 0%nat - ρ 0%nat 3%nat + ρ 3%nat 3%nat) / 2
  | 3, 3 =>  (ρ 1%nat 1%nat - ρ 2%nat 1%nat - ρ 1%nat 2%nat + ρ 2%nat 2%nat) / 2
  | _, _ => 0
  end.

Lemma alice_spec : forall (ρ : Density 4), WF_Matrix 4 4  ρ -> ⟦alice⟧ ρ = M_alice ρ.
Proof.
  matrix_denote. Msimpl.
  repeat rewrite <- Mmult_assoc; Msimpl.
  repeat rewrite Mmult_assoc; Msimpl.
  solve_matrix.
  all: autorewrite with Cdist_db;
       repeat rewrite (Cmult_comm _ (/√2));
       repeat rewrite Cmult_assoc;
       autorewrite with C_db; clra.
Qed.    

(* Spec computed rather than reasoned about - should confirm correct *)
Definition M_bob (ρ : Density 8) : Density 2 := 
  fun x y => match x, y with
          | 0, 0 => ρ 0%nat 0%nat + ρ 3%nat 3%nat + ρ 4%nat 4%nat + ρ 7%nat 7%nat
          | 0, 1 => ρ 0%nat 1%nat + ρ 3%nat 2%nat - ρ 4%nat 5%nat - ρ 7%nat 6%nat
          | 1, 0 => ρ 1%nat 0%nat + ρ 2%nat 3%nat - ρ 5%nat 4%nat - ρ 6%nat 7%nat
          | 1, 1 => ρ 1%nat 1%nat + ρ 2%nat 2%nat + ρ 5%nat 5%nat + ρ 6%nat 6%nat
          | _, _ => 0
          end.

Lemma bob_spec : forall (ρ : Density 8), WF_Matrix 8 8 ρ -> ⟦bob⟧ ρ = M_bob ρ.
Proof. matrix_denote. Msimpl. solve_matrix. Qed.  


(* We convert the matrices back to functional representation for 
   unification. Simply comparing the matrices may be more efficient,
   however. *)

Lemma teleport_eq : teleport ≡ id_circ.
Proof.
  intros ρ safe WF.
  matrix_denote.
  Msimpl.
  solve_matrix.
  all: rewrite (Cmult_assoc (/ √2));
       autorewrite with C_db;
       rewrite (Cmult_comm _ (/2));
       rewrite (Cmult_assoc 2 (/2));
       autorewrite with C_db;
       rewrite (Cmult_assoc 2 (/2));
       autorewrite with C_db;
       reflexivity.
Qed.

(* Teleport with Dynamic Lifting *)

Open Scope matrix_scope.
Definition M_bob_distant (b1 b2 : bool) (ρ : Density 2) : Matrix 2 2 := 
  match b1, b2 with
  | true, true   => σz × σx × ρ × σx × σz  
  | true, false  => σz × ρ × σz  
  | false, true  => σx × ρ × σx  
  | false, false => ρ
  end.
Close Scope matrix_scope.

Definition bob_distant_spec : forall b1 b2 (ρ : Density 2), 
    WF_Matrix 2 2 ρ -> 
    ⟦bob_distant b1 b2⟧ ρ = M_bob_distant b1 b2 ρ.
Proof.
  intros.
  destruct b1, b2;
  matrix_denote; Msimpl; solve_matrix.
Qed.

Definition teleport_distant_eq : teleport_distant ≡ id_circ.
Proof. 
  intros ρ safe WF.
  matrix_denote.
  Msimpl.
  solve_matrix.
  idtac.
  all: rewrite (Cmult_assoc (/ √2));
       autorewrite with C_db;
       rewrite (Cmult_comm _ (/2));
       rewrite (Cmult_assoc 2 (/2));
       autorewrite with C_db;
       rewrite (Cmult_assoc 2 (/2));
       autorewrite with C_db;
       reflexivity.
Qed.

(*********************)
(* Superdense Coding *)
(*********************)

Lemma superdense_eq : forall (ρ : Density 4),
  Classical ρ ->
  WF_Matrix 4 4 ρ -> 
  ⟦superdense⟧ ρ = ρ.
Proof.
  intros ρ CL WF.
  matrix_denote.
  Msimpl.
  solve_matrix.
  all: try (rewrite CL by omega; easy).
  all: autorewrite with Cdist_db;
       repeat rewrite Cmult_assoc; autorewrite with C_db;
       repeat rewrite <- Cmult_assoc; autorewrite with C_db;    
       clra.
Qed.

Lemma superdense_distant_eq : forall b1 b2, 
  ⟦superdense_distant b1 b2⟧ I1 = bools_to_matrix [b1; b2].
Proof.
  intros b1 b2.
  specialize (WF_bools_to_matrix ([b1;b2])) as WF.
  destruct b1, b2; matrix_denote; Msimpl; solve_matrix.
Qed.


(* Lemmas out of date
Proposition boxed_gate_correct : forall W1 W2 (g : Gate W1 W2) (ρ : Density (2^⟦W1⟧)) ,
      Mixed_State ρ -> ⟦boxed_gate g⟧ ρ = ⟦g⟧ ρ.
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
  Msimpl.
  reflexivity.
Abort.

Proposition lift_meas_correct : lift_meas ≡ boxed_gate meas.
Proof.
  intros ρ wf_ρ.
  simpl.
  repeat (unfold denote_pat_in, swap_list, swap_two; simpl).
  Msimpl.
  unfold super, compose_super, Splus, SZero.
  Msimpl.
  rewrite braket0_adjoint, braket1_adjoint.
  prep_matrix_equality; simpl.
  unfold Mplus, Mmult, Id, adjoint, Zero. simpl.
  autorewrite with C_db.
  rewrite Cplus_comm. reflexivity.
Abort.

Proposition lift_eta_correct : forall (ρ : Density 2), WF_Matrix 2 2 ρ
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
  unfold Mmult, Mplus, Zero, adjoint, ket0, ket1. simpl.
  Csimpl.
  destruct x; Csimpl. 
  destruct y; Csimpl.
*)
*)

