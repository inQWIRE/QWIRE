Require Import HOASLib.
Require Import Composition.

Definition cnot10 (n : nat) : Box ((S (S n) ⨂ Qubit)%qc) ((S (S n) ⨂ Qubit)%qc) :=
  box_ (tar,(ct,u)) ⇒ let_ (ct,tar) ← CNOT $ (ct,tar); (tar,(ct,u)).

Open Scope matrix_scope.

Fixpoint nket (n : nat) (st : Matrix 2 1) : Matrix (2^n) 1 :=
  match n with
  | 0 => I 1
  | S n' => st ⊗ (nket n' st)
  end.

Definition ghz_ket (n : nat) : Matrix (2^(S n)) 1 :=
  1/ √2 .* (nket (S n) qubit0) .+ 1/ √2 .* nket (S n) qubit1.

Definition ghz_state (n : nat) : Density (2^(S n)) :=
  outer_product (ghz_ket n) (ghz_ket n).

Require Import Symmetric.
Open Scope circ_scope.

Fixpoint ghz (n : nat) : Box ((S n) ⨂ One)%qc ((S n) ⨂ Qubit)%qc :=
  match n with
  | 0 => box_ (q,u) ⇒ let_ q ← _H $ init0 $ q; let_ u ← (); (q,u)
  | S n' => (init0 ∥ ghz n') ;; (cnot10 n') 
  end.

Lemma typed_cnot10 :
  forall n : nat, Typed_Box (cnot10 n).
Proof.
  induction n; simpl; type_check.
Qed.

Lemma typed_ghz :
  forall n : nat, Typed_Box (ghz n).
Proof.
  induction n; simpl.
  - type_check.
  - assert (Typed_Box(cnot10 n)). apply typed_cnot10.
    type_check.
Qed.

Lemma wf_nket :
  forall (n : nat)(st : (Matrix 2 1)), WF_Matrix st -> WF_Matrix (nket n st).
Proof.
  intros. induction n.
  - simpl. apply WF_I1.
  - simpl. apply WF_kron.
    + rewrite <- plus_n_O. lia.
    + lia.
    + assumption.
    + assumption.
Qed.

Require Import Denotation.
Open Scope matrix_scope.

(* TODO: Move to Matrix.v *)
Definition notc : Matrix 4 4 :=
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 3 => C1
          | 2, 2 => C1
          | 3, 1 => C1
          | _, _ => C0
          end.      

Lemma wf_notc : WF_Matrix notc.
Proof. show_wf. Qed.

Lemma wf_ghz :
  forall n : nat, WF_Matrix (ghz_state n).
Proof.
  intro.
  unfold ghz_state.
  apply WF_outer_product.
  all : unfold ghz_ket;
    apply WF_plus; apply WF_scale; apply wf_nket;
      try apply WF_qubit0; try apply WF_qubit1.
Qed.

#[export] Hint Resolve wf_ghz wf_nket wf_notc : wf_db.

Lemma ctrl_list_notc :
  forall n : nat, 
    ctrl_list_to_unitary_r (repeat false n ++ [true]) σx = notc ⊗ I (2 ^ n).
Proof.
  induction n.
  - simpl.
    rewrite kron_1_r.
    solve_matrix.
  - simpl. rewrite IHn.
    assert (I (2 ^ n) ⊗ I 2 = I (2 ^ n + (2 ^ n + 0))).
    { rewrite id_kron. rewrite <- plus_n_O.
      replace (2^n*2)%nat with (2^n+2^n)%nat. reflexivity. lia. }
    rewrite <- H.
    assert ((length (repeat false n ++ [true])) = (S n)).
    { rewrite app_length. simpl. rewrite repeat_length. lia. }
    rewrite H0. 
    rewrite Nat.add_1_r. repeat rewrite <- plus_n_O.
    replace (2^S(S n)+2^S (S n))%nat with (4*(2^n)*2)%nat.
    replace (2^n+2^n)%nat with ((2^n)*2)%nat.
    rewrite <- kron_assoc by auto with wf_db.
    reflexivity.
    lia.
    unify_pows_two.
Qed.

Local Close Scope C_scope.
Local Close Scope R_scope.
Lemma cnot10_correct :
  forall n ρ, WF_Matrix ρ -> 
    ⟦cnot10 n⟧ ρ = (notc ⊗ (I (2^n))) × ρ × (notc ⊗ (I (2^n)))†.
Proof.
  intros. 
  induction n.
  - matrix_denote.
    simpl in *.
    Msimpl.
    solve_matrix.
  - matrix_denote. 
    rewrite add_fresh_split.
    simpl.
    matrix_denote.
    rewrite add_fresh_split. simpl. 
    repeat rewrite subst_var_no_gaps.
    simpl.
    unify_pows_two.
    rewrite rev_repeat.
    rewrite size_ntensor. simpl.
    rewrite Nat.mul_1_r. 
    rewrite subst_pat_fresh.
    rewrite swap_fresh_seq.
    simpl.
    rewrite size_ntensor. simpl.
    rewrite Nat.mul_1_r.
    repeat rewrite -> Nat.add_1_r.
    assert(E : forall i j, i > j -> (map (fun z : nat * nat => if match snd z with
                                                | 0 => true
                                                | S _ => false
                                      end then (fst z, j)%core else z) (combine (seq i n) (seq i n))) =
               (combine (seq i n) (seq i n))).
    clear. induction n. simpl. reflexivity. simpl.
    intros. simpl. rewrite IHn by lia. destruct i; try lia. reflexivity.
    rewrite E by lia. clear E.
    assert(E : forall i, i > 1 -> (map (fun z : nat * nat => if match snd z with
                                                | 1 => true
                                                | _ => false
                                      end then (fst z, 1)%core else z) (combine (seq i n) (seq i n))) =
               (combine (seq i n) (seq i n))).
    clear. induction n. simpl. reflexivity. simpl.
    intros. simpl. rewrite IHn by lia. destruct i as [|[|]]; try lia. reflexivity.
    rewrite E by lia. clear E.
    assert(E : forall i, i > 2 -> (map (fun z : nat * nat => if match snd z with
                                                | 2 => true
                                                | _ => false
                                      end then (fst z, 2)%core else z) (combine (seq i n) (seq i n))) =
               (combine (seq i n) (seq i n))).
    clear. induction n. simpl. reflexivity. simpl.
    intros. simpl. rewrite IHn by lia. destruct i as [|[|[|]]]; try lia. reflexivity.
    rewrite E by lia. clear E.

    assert ((2 ^ S (S (S n)))%nat=(4 * 2 ^ S n)%nat). unify_pows_two.
    assert ([false] = (repeat false 1)) by auto.
    
    repeat rewrite Mmult_1_r. repeat rewrite Mmult_1_l. Msimpl.
    rewrite swap_list_aux_id.
    replace (n+2) with (S (S n)) by lia.
    rewrite Nat.sub_diag. rewrite id_kron. rewrite Nat.mul_1_r. rewrite Mmult_1_l.
    rewrite id_adjoint_eq. rewrite Mmult_1_r.

    rewrite H1. rewrite repeat_combine.
    replace (n+1) with (S n) by lia.
    replace (2^S (S (S n))) with (4*2^S n) by unify_pows_two. rewrite ctrl_list_notc. reflexivity.
    
    rewrite H0. apply WF_mult. apply WF_mult. 
    rewrite H1. rewrite repeat_combine. 
    replace (n+1) with (S n) by lia. rewrite ctrl_list_notc. apply WF_kron.
    auto.  auto. show_wf. apply WF_I.
    assumption.
    
    rewrite H1. rewrite repeat_combine. 
    replace (n+1) with (S n) by lia. rewrite ctrl_list_notc.
    apply WF_adjoint. apply WF_kron. auto. auto.
    show_wf. apply WF_I.
    
    rewrite H0. apply WF_mult. apply WF_mult.
    rewrite H1. rewrite repeat_combine. 
    replace (n+1) with (S n) by lia. rewrite ctrl_list_notc.
    apply WF_kron.
    auto. auto. show_wf. apply WF_I.
    assumption.
    
    rewrite H1. rewrite repeat_combine. 
    replace (n+1) with (S n) by lia.
    rewrite ctrl_list_notc.
    apply WF_adjoint.
    apply WF_kron.
    auto. auto.
    show_wf.
    apply WF_I.

    all : try (rewrite swap_list_aux_id; apply WF_I).

    repeat constructor.
    rewrite fresh_state_ntensor.
    rewrite app_length. simpl.
    lia.
    
    apply add_fresh_state_no_gaps.
    repeat constructor.
    rewrite fresh_state_ntensor.
    rewrite app_length. simpl.
    lia.

    apply add_fresh_state_no_gaps.
    repeat constructor.

    rewrite fresh_state_ntensor.
    rewrite app_length.
    simpl. apply Nat.lt_0_succ.

    apply add_fresh_state_no_gaps.
    repeat constructor.
Qed.

Lemma Mmult_outer_product :
  forall (n : nat)  (k : (Matrix n 1)) (M : Matrix n n),
    M × (outer_product k k) × M† = outer_product (M × k) (M × k).
Proof.
  intros. 
  unfold outer_product.
  rewrite Mmult_adjoint.
  repeat rewrite Mmult_assoc. reflexivity.
Qed.

Lemma kron_product :
  forall (m n : nat) (a : (Matrix m 1))(b : (Matrix n 1)),
    (outer_product a a) ⊗ (outer_product b b) = outer_product (a ⊗ b) (a ⊗ b).
Proof.
  intros. unfold outer_product.
  rewrite <- kron_mixed_product.
  rewrite <- kron_adjoint. reflexivity.
Qed.

Lemma outer_eq :
  forall (n : nat)(a b : Matrix n 1),
    a = b -> outer_product a a = outer_product b b.
Proof.
  intros. rewrite H. reflexivity.
Qed.
  
Lemma Mplus_eq :
  forall (m n: nat)(a1 b1 a2 b2 : Matrix m n),
    a1 = a2 -> b1 = b2 -> a1 .+ b1 = a2 .+ b2.
Proof.
  intros. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma Mscale_eq :
  forall (m n: nat)(c : C) (u v : (Matrix m n)),
    u = v -> c .* u = c .* v.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma kron_eq :
  forall (m n: nat)(u1 u2 : (Matrix m 1))(v1 v2 : (Matrix n 1)),
    u1=u2 -> v1=v2 -> u1⊗v1=u2⊗v2.
Proof. 
  intros. rewrite H. rewrite H0. reflexivity.
Qed.

Local Open Scope C_scope.
Local Open Scope R_scope.
Theorem ghz_correct :
  forall n : nat, ⟦ghz n⟧ (I 1) = ghz_state n.
Proof.
  induction n as [| n' IHn'].
  - matrix_denote. Msimpl.
    unfold ghz_state, outer_product, ghz_ket.
    solve_matrix.
  - simpl.
    rewrite inSeq_correct.
    + assert ((I 1) = (I (2^⟦One⟧)) ⊗ (I (2^⟦((S n') ⨂ One)%qc⟧))).
      { Msimpl. rewrite size_ntensor. rewrite Nat.mul_0_r. reflexivity. }
      unfold compose_super.
      assert (⟦init0⟧ (I 1) = ∣0⟩⟨0∣).
      { simpl. Msimpl. solve_matrix. }
      assert (denote_box true (init0 ∥ ghz n') (I 1) = (denote_box true init0 (I (2^⟦One⟧))) ⊗ (denote_box true (ghz n') (I (2^⟦((S n') ⨂ One)%qc⟧)))).
      {
        rewrite -> H.
        apply inPar_correct.
        type_check.
        apply typed_ghz.
        simpl. apply WF_I1. 
        replace (2^⟦(S n' ⨂ One)%qc⟧)%nat with 1%nat by (simpl; rewrite -> size_ntensor; rewrite Nat.mul_0_r; auto).
        apply WF_I1.
      }
      simpl in H1. rewrite -> H1.
      assert (denote_box true init0 (I 1) = ∣0⟩⟨0∣).
      { matrix_denote. solve_matrix. }
      rewrite H2. simpl in IHn'.
      repeat rewrite -> size_ntensor. rewrite Nat.mul_0_r. simpl. rewrite IHn'.
      assert (⟦cnot10 n'⟧ (∣0⟩⟨0∣ ⊗ ghz_state n') = (notc ⊗ (I (2^n'))) × (∣0⟩⟨0∣ ⊗ ghz_state n') × (notc ⊗ (I (2^n')))† ).
      { apply cnot10_correct. apply WF_kron.
        simpl. lia.
        simpl. lia.
        apply WF_braket0. apply wf_ghz.
      }
      simpl in H3. simpl. 
      assert ((size_wtype (n' ⨂ Qubit)%qc)=n').
      { rewrite size_ntensor. simpl.  lia. }
      simpl in H3. rewrite Nat.mul_1_r. simpl. rewrite -> H3.
      unfold ghz_state, ghz_ket.
      replace (∣0⟩⟨0∣) with (outer_product ∣0⟩ ∣0⟩) by (simpl; reflexivity).
      rewrite -> kron_product.
      replace ((2 * 2 ^ S n'))%nat with (4 * 2^n')%nat in * by (simpl; lia).
      rewrite -> Mmult_outer_product.
      rewrite kron_plus_distr_l.
      simpl in *.
      replace (2 ^ n' + (2 ^ n' + (2 ^ n' + (2 ^ n' + 0))))%nat with
          (2 ^ n' + (2 ^ n' + 0) + (2 ^ n' + (2 ^ n' + 0) + 0))%nat by (repeat rewrite <- plus_n_O; repeat rewrite Nat.add_assoc; reflexivity).
      rewrite Mmult_plus_distr_l.
      apply outer_eq.
      apply Mplus_eq.
      *
        remember (nket n' ∣0⟩) as nk0.
        assert ( (∣0⟩ ⊗ (1%R / √ 2 .* (∣0⟩ ⊗ nk0))) = 1%R / √ 2 .* (∣0⟩ ⊗ ((∣0⟩ ⊗ nk0)))).
        { rewrite -> Mscale_kron_dist_r. reflexivity. }     
        simpl in H5. rewrite -> H5.
        (* simpl. *)
        assert ((∣0⟩ ⊗ (∣0⟩ ⊗ nk0)) = (∣0⟩ ⊗ ∣0⟩) ⊗ nk0).
        { rewrite -> kron_assoc; subst; auto with wf_db. }
        simpl in H6. rewrite -> H6.
        rewrite -> Mscale_mult_dist_r.
        apply Mscale_eq.
        assert (notc ⊗ I (2 ^ n') × (∣0⟩ ⊗ ∣0⟩ ⊗ nk0) = (notc × (∣0⟩⊗∣0⟩)) ⊗ ((I (2^n')) × nk0)).
        { rewrite -> kron_mixed_product. reflexivity. }
        simpl in H7. repeat rewrite <- plus_n_O in H7.
        repeat rewrite <- plus_n_O.
        replace (2 ^ n' + 2 ^ n' + (2 ^ n' + 2 ^ n'))%nat with (2 ^ n' + (2 ^ n' + (2 ^ n' + 2 ^ n')))%nat by (repeat rewrite Nat.add_assoc; reflexivity).
        rewrite -> H7.
        apply kron_eq.
        solve_matrix. 
        rewrite Mmult_1_l. reflexivity.
        rewrite Heqnk0. apply wf_nket.
        apply WF_qubit0.
      *
        remember (nket n' ∣1⟩) as nk1.
        assert ( (∣0⟩ ⊗ (1%R / √ 2 .* (∣1⟩ ⊗ nk1))) = 1%R / √ 2 .* (∣0⟩ ⊗ ((∣1⟩ ⊗ nk1)))).
        { rewrite -> Mscale_kron_dist_r. reflexivity. }     
        simpl in H5. rewrite -> H5.
        assert ((∣0⟩ ⊗ (∣1⟩ ⊗ nk1)) = (∣0⟩ ⊗ ∣1⟩) ⊗ nk1).
        { rewrite -> kron_assoc; subst; auto with wf_db. }
        simpl in H6. rewrite -> H6.
        rewrite Mscale_mult_dist_r.
        apply Mscale_eq.
        assert (notc ⊗ I (2 ^ n') × (∣0⟩ ⊗ ∣1⟩ ⊗ nk1) = (notc × (∣0⟩⊗∣1⟩)) ⊗ ((I (2^n')) × nk1)).
        { rewrite -> kron_mixed_product. reflexivity. }
        simpl in H7.
        repeat rewrite <- plus_n_O in H7.
        repeat rewrite <- plus_n_O. 
        replace (2 ^ n' + 2 ^ n' + (2 ^ n' + 2 ^ n'))%nat with (2 ^ n' + (2 ^ n' + (2 ^ n' + 2 ^ n')))%nat by (repeat rewrite Nat.add_assoc; reflexivity).
        rewrite -> H7. 
        assert ((∣1⟩ ⊗ (∣1⟩ ⊗ nk1)) = (∣1⟩ ⊗ ∣1⟩) ⊗ nk1).
        { rewrite -> kron_assoc; subst; auto with wf_db. }
        replace (1 * 1)%nat with 1%nat in H8 by lia.
        replace (2^n'+2^n')%nat with (2*2^n')%nat by lia.
        rewrite -> H8.
        apply kron_eq.
        solve_matrix. 
        rewrite Mmult_1_l. reflexivity.
        rewrite Heqnk1. apply wf_nket. 
        apply WF_qubit1.
    + apply typed_cnot10.
    + apply inPar_WT. type_check. apply typed_ghz.
Qed.
