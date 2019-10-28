Require Import Denotation.

Open Scope matrix_scope.

(* Propositional version (in Set). Could also just have a unitary circuit type and a 
   (trivial) coercion from circuit. *)
Inductive Unitary_Circuit {W} : Circuit W -> Prop :=
| u_output : forall p, Unitary_Circuit (output p)
| u_gate : forall W' c (u : Unitary W') p,
    (forall p', Unitary_Circuit (c p')) ->
    Unitary_Circuit (gate (U u) p c).

Definition Unitary_Box {W} (b : Box W W) : Prop :=
  match b with
  | box c => forall p, (Unitary_Circuit (c p))
  end.

Inductive Unitary_DB_Circuit {W} : DeBruijn_Circuit W -> Prop :=
| u_db_output : forall p, Unitary_DB_Circuit (db_output p)
| u_db_gate : forall W' c (u : Unitary W') p,
    Unitary_DB_Circuit c ->
    Unitary_DB_Circuit (db_gate (U u) p c).

Definition Unitary_DB_Box {W} (b : DeBruijn_Box W W) : Prop :=
  match b with
  | db_box _ c => Unitary_DB_Circuit c
  end.

Fixpoint denote_u_db_circuit {W} (c : DeBruijn_Circuit W) : Square (2^(⟦W⟧)) :=
  match c with
  | db_output p => ⟦p⟧
  | db_gate g p c  => match g with
                     | U u => denote_u_db_circuit c × apply_unitary (⟦W⟧) u (pat_to_list p)
                     | _   => dummy_mat
                     end
  | _   => dummy_mat
  end.

Definition denote_u_db_box {W} (c : DeBruijn_Box W W) : Square (2^⟦W⟧) :=
  match c with
  | db_box _ c' => denote_u_db_circuit c' 
  end.

Lemma unitary_to_db : forall W Γ (c : Circuit W) , Unitary_Circuit c -> Unitary_DB_Circuit (hoas_to_db Γ c).
Proof.
  intros W Γ c U.
  gen Γ.
  induction c; intros.
  - simpl. constructor.
  - simpl.
    destruct (process_gate g p Γ) eqn:E.
    dependent destruction U.
    constructor. 
    apply H.
    apply H0.
  - inversion U.
Qed.

Lemma unitary_box_to_db : forall W (c : Box W W) , Unitary_Box c -> Unitary_DB_Box (hoas_to_db_box c).
Proof.
  intros W c U.
  unfold Unitary_Box, Unitary_DB_Box in *.
  destruct c; simpl in *.
  destruct (add_fresh W []).
  apply unitary_to_db.
  apply U.
Qed.

Definition denote_unitary_box {W} (c : Box W W) : Square (2^⟦W⟧) :=
  denote_u_db_box (hoas_to_db_box c).

Lemma denote_unitary_box_eq : forall W safe (c : Box W W) ρ,
    Unitary_Box c ->
    denote_box safe c ρ = denote_unitary_box c × ρ × (denote_unitary_box c)†.
Proof.
  intros W safe [c] ρ pf.
  simpl in pf.
  unfold denote_unitary_box, denote_box.
  unfold denote_db_box.
  unfold hoas_to_db_box.
  destruct (add_fresh W []) as [p Γ].
  specialize (pf p).
  gen ρ.
  induction (c p).
  - unfold denote_u_db_box.
    simpl.
    rewrite pad_nothing.
    reflexivity.
  - intros ρ.
    simpl.
    dependent destruction pf.
    simpl.
    unfold compose_super, super.
    rewrite Nat.add_sub.
    rewrite H0 by auto.
    unfold denote_u_db_box.
    simpl.
    unfold apply_U, super.
    rewrite Mmult_adjoint.
    repeat rewrite Mmult_assoc.
    reflexivity.
  - inversion pf.
Qed.

(* Example *)
Definition HZH : Box Qubit Qubit := 
  box_ q ⇒ _H $ _Z $ _H $ q.

Lemma U_HZH : Unitary_Box HZH.
Proof. repeat constructor. Qed.



(***********************************************)
(** Isometry Semantics - adds init and assert **)
(** Corresponds to the safe density semantics **)
(***********************************************)

Inductive Isometry_Gate : forall W W', Gate W W' -> Prop :=
  | iso_u : forall W u, Isometry_Gate W W (U u)
  | iso_init0 : Isometry_Gate _ _ init0
  | iso_init1 : Isometry_Gate _ _ init1
  | iso_assert0 : Isometry_Gate _ _ assert0
  | iso_assert1 : Isometry_Gate _ _ assert1.

Inductive Isometry_Circuit {W} : Circuit W -> Prop :=
| iso_output : forall p, Isometry_Circuit (output p)
| iso_gate : forall W' W'' c (g : Gate W' W'') p,
    Isometry_Gate _ _ g ->
    (forall p', Isometry_Circuit (c p')) ->
    Isometry_Circuit (gate g p c).

Lemma Unitary_Circuit_is_Isometry : forall W (c : Circuit W),
    Unitary_Circuit c -> Isometry_Circuit c.
Proof.
  intros.
  induction c as [p | W1 W2 g p c IH |].
  - constructor.
  - dependent destruction H.
    constructor.
    constructor.
    intros p'.
    apply IH.
    apply H.
  - inversion H.
Qed.
    
Definition Isometry_Box {W W'} (b : Box W W') : Prop :=
  match b with
  | box c => forall p, (Isometry_Circuit (c p))
  end.

Inductive Isometry_DB_Circuit {W} : DeBruijn_Circuit W -> Prop :=
| iso_db_output : forall p, Isometry_DB_Circuit (db_output p)
| iso_db_gate : forall W' W'' c (g : Gate W' W'') p,
    Isometry_Gate _ _ g ->
    Isometry_DB_Circuit c ->
    Isometry_DB_Circuit (db_gate g p c).

Definition Isometry_DB_Box {W W'} (b : DeBruijn_Box W W') : Prop :=
  match b with
  | db_box _ c => Isometry_DB_Circuit c
  end.

Definition denote_init0 (n : nat) : Matrix (2^(n+1)) (2^n) :=
  (I (2 ^ n) ⊗ ∣0⟩).

Definition denote_init1 (n : nat) : Matrix (2^(n+1)) (2^n) :=
  (I (2 ^ n) ⊗ ∣1⟩).

Definition denote_assert0 (n k : nat) : Matrix (2^(n-1)) (2^n) :=
  I (2 ^ k) ⊗ ⟨0∣ ⊗ I (2 ^ (n - k - 1)).

Definition denote_assert1 (n k : nat) : Matrix (2^(n-1)) (2^n) :=
  I (2 ^ k) ⊗ ⟨1∣ ⊗ I (2 ^ (n - k - 1)).

(* n is the number of input wires *)
(* ⟦W⟧ is the number of output wires *)               
(* The padding in db_output should be unnecessary in a well-typed circuit :
   there the input should equal the output (if the right n was provided).
   For now it's convenient for later proofs *)
Fixpoint denote_iso_db_circuit {W} (n : nat) (c : DeBruijn_Circuit W) :
  Matrix (2^(⟦W⟧)) (2^n) :=
  match c with
  | db_output p    => pad n (⟦p⟧)
  | db_gate g p c  => match g with
                     | U u     => denote_iso_db_circuit n c × apply_unitary n u (pat_to_list p)
                     | init0   => (denote_iso_db_circuit (S n) c) × denote_init0 n 
                     | init1   => (denote_iso_db_circuit (S n) c) × denote_init1 n
                     | assert0 => (denote_iso_db_circuit (n - 1)%nat c) × denote_assert0 n (hd O (pat_to_list p))
                     | assert1 => (denote_iso_db_circuit (n - 1)%nat c) × denote_assert1 n (hd O (pat_to_list p))
                     | _   => dummy_mat
                     end
  | _   => dummy_mat
  end.

Definition denote_iso_db_box {W W'} (c : DeBruijn_Box W W') : Matrix (2^⟦W'⟧) (2^⟦W⟧) :=
  match c with
  | db_box _ c' => denote_iso_db_circuit (⟦W⟧) c' 
  end.

Lemma isometry_to_db : forall W Γ (c : Circuit W) , Isometry_Circuit c -> Isometry_DB_Circuit (hoas_to_db Γ c).
Proof.
  intros W Γ c U.
  gen Γ.
  induction c; intros.
  - simpl. constructor.
  - simpl.
    destruct (process_gate g p Γ) eqn:E.
    dependent destruction U.
    constructor; trivial.
    apply H.
    apply H1.
  - inversion U.
Qed.

Lemma isometry_box_to_db : forall W W' (c : Box W W') , Isometry_Box c -> Isometry_DB_Box (hoas_to_db_box c).
Proof.
  intros W W' c U.
  unfold Isometry_Box, Isometry_DB_Box in *.
  destruct c; simpl in *.
  destruct (add_fresh W []).
  apply isometry_to_db.
  apply U.
Qed.

Definition denote_isometry_box {W W'} (c : Box W W') :=
  denote_iso_db_box (hoas_to_db_box c).

Lemma denote_unitary_isometry_box_eq : forall W (c : Box W W),
    Unitary_Box c ->
    denote_unitary_box c = denote_isometry_box c.
Proof.
  intros W [f] pf.
  unfold Unitary_Box in pf.
  unfold denote_unitary_box, denote_isometry_box.
  unfold hoas_to_db_box.
  destruct (add_fresh W []) as [p Γ].
  specialize (pf p).
  remember (f p) as c. clear Heqc f p. 
  induction c.
  - unfold denote_iso_db_box, denote_u_db_box.
    simpl.
    rewrite pad_nothing.
    reflexivity.
  - dependent destruction pf.
    simpl in *.
    rewrite H0; easy.
  - inversion pf.
Qed.

Lemma denote_isometry_box_eq : forall W W' (c : Box W W') ρ,
    Isometry_Box c ->
    denote_box false c ρ = denote_isometry_box c × ρ × (denote_isometry_box c)†.
Proof.
  intros W W' [f] ρ pf.
  simpl in pf.
  unfold denote_isometry_box, denote_box.
  unfold denote_db_box.
  unfold hoas_to_db_box.
Abort.

(*
  (* new proof *)
  
  rewrite add_fresh_split.
  remember (add_fresh_state W []) as Γ.
  remember (add_fresh_pat W []) as p.
  specialize (size_fresh_ctx W []) as S__Γ.
  rewrite <- HeqΓ in S__Γ. simpl in S__Γ.
  clear HeqΓ Heqp.
  specialize (pf p).
  remember (f p) as c. clear Heqc f p. (* might want a general version - start here *)
  gen W ρ Γ.
  induction c.
  - intros.
    unfold denote_iso_db_box.
    simpl. reflexivity.
  - intros W ρ Γ SE.
    simpl.
    dependent destruction pf.
    dependent destruction H0.
    + simpl.
      unfold compose_super, super.
      rewrite Nat.add_sub.
      rewrite H; auto.
      unfold denote_iso_db_box.
      simpl.
      unfold apply_U, super.
      rewrite Mmult_adjoint.
      repeat rewrite Mmult_assoc.
      reflexivity.
    + simpl.
      unfold compose_super, super.
      rewrite Nat.sub_0_r.
      replace (size_wtype W + 1)%nat with (⟦ W ⊗ Qubit⟧)%qc by easy.
      rewrite H; auto.
      2: rewrite size_ctx_app; simpl; auto. 
      unfold denote_iso_db_box.
      simpl.
      unfold apply_new0, denote_init0, super.
      rewrite Nat.add_1_r.
      repeat rewrite Mmult_adjoint.
      remember (denote_iso_db_circuit (S (size_wtype W)) (hoas_to_db (Γ ++ [Some Qubit]) (c (qubit (length Γ))))) as A.
      repeat rewrite Mmult_assoc.
      Msimpl.
      Set Printing All. (* This is terrible messy. Tactics needed *)
      rewrite Nat.add_0_r.
      match goal with
      | [|- context[@adjoint ?a ?b (@kron ?c ?d ?e ?f ?B ?C)]] =>
        replace (@adjoint a b (@kron c d e f B C)) with
                (@adjoint (c*e) (d*f) (@kron c d e f B C))
      end.
      2: match goal with
         | [|- @adjoint ?a ?b ?B = @adjoint ?a' ?b' ?B] =>
           replace a with a' by unify_pows_two;
           replace b with b' by unify_pows_two;
           reflexivity
         end.      
      rewrite kron_adjoint.
      Msimpl.
      unify_pows_two.
      rewrite Nat.add_1_r.
      replace (2 ^ S (size_wtype W))%nat with (2 ^ (size_wtype W) * 2)%nat by unify_pows_two.
      repeat rewrite Mmult_assoc.
      reflexivity.
      Unset Printing All.
    + simpl.
      unfold compose_super, super.
      rewrite Nat.sub_0_r.
      replace (size_wtype W + 1)%nat with (⟦ W ⊗ Qubit⟧)%qc by easy.
      rewrite H; auto.
      2: rewrite size_ctx_app; simpl; auto. 
      unfold denote_iso_db_box.
      simpl.
      unfold apply_new1, denote_init1, super.
      rewrite Nat.add_1_r.
      repeat rewrite Mmult_adjoint.
      remember (denote_iso_db_circuit (S (size_wtype W)) (hoas_to_db (Γ ++ [Some Qubit]) (c (qubit (length Γ))))) as A.
      repeat rewrite Mmult_assoc.
      Msimpl.
      rewrite Nat.add_0_r.
      match goal with
      | [|- context[@adjoint ?a ?b (@kron ?c ?d ?e ?f ?B ?C)]] =>
        replace (@adjoint a b (@kron c d e f B C)) with
                (@adjoint (c*e) (d*f) (@kron c d e f B C))
      end.
      2: match goal with
         | [|- @adjoint ?a ?b ?B = @adjoint ?a' ?b' ?B] =>
           replace a with a' by unify_pows_two;
           replace b with b' by unify_pows_two;
           reflexivity
         end.      
      rewrite kron_adjoint.
      Msimpl.
      unify_pows_two.
      rewrite Nat.add_1_r.
      replace (2 ^ S (size_wtype W))%nat with (2 ^ (size_wtype W) * 2)%nat by unify_pows_two.
      repeat rewrite Mmult_assoc.
      reflexivity.
    + simpl.
      unfold compose_super, super.
      rewrite Nat.add_0_r.
      replace (size_wtype W - 1)%nat with (⟦(size_wtype W - 1) ⨂ Qubit⟧)%qc.
      Focus 2. rewrite size_ntensor. simpl. lia.
      rewrite H; auto.
      Focus 2. rewrite size_ntensor. simpl.
      rewrite <- SE. rewrite Nat.mul_1_r. dependent destruction p.
      eapply remove_qubit_pred.
      (* nope. Need a lot more info about Γ. *)

      Search size_ctx remove_pat. 
      lia.
      simpl.
      rewrite size_ntensor. simpl.
      rewrite Nat.mul_1_r.
      unfold denote_iso_db_box.
      simpl.
      unfold apply_assert0, denote_assert0, super.
      remember (denote_iso_db_circuit (size_wtype W - 1) (hoas_to_db (remove_pat p Γ) (c ()))) as A.
      remember (hd O (pat_to_list (subst_pat Γ p))) as k.
      Msimpl.
      match goal with
      | [|- context[@adjoint ?a ?b (@kron ?c ?d ?e ?f ?B ?C)]] =>
        replace (@adjoint a b (@kron c d e f B C)) with
                (@adjoint (c*e) (d*f) (@kron c d e f B C))
      end.
      Focus 2.
      match goal with
         | [|- @adjoint ?a ?b ?B = @adjoint ?a' ?b' ?B] =>
           replace a with a'; 
           replace b with b';
           unify_pows_two;  
           try reflexivity
         end.      

      (* aha! issue. *)
      (* We need premises about the contents of gamma being bounded *)
      (* Specifically, k < [W] *)
      (* We know from pat_to_list_bounded that k < [Γ] (or [Γ] = k = 0) *)
      (* We also have size_ctx (add_fresh_state w Γ) = (size_ctx Γ + size_wtype w)%nat *)  

(* old proof *)  
  destruct (add_fresh W []) as [p Γ].
  specialize (pf p).
  remember (f p) as c. clear Heqc f p. (* might want a general version - start here *)
  gen W ρ Γ.
  induction c.
  - intros.
    unfold denote_iso_db_box.
    simpl. reflexivity.
  - intros W ρ Γ.
    simpl.
    dependent destruction pf.
    dependent destruction H0.
    + simpl.
      unfold compose_super, super.
      rewrite Nat.add_sub.
      rewrite H by auto.
      unfold denote_iso_db_box.
      simpl.
      unfold apply_U, super.
      rewrite Mmult_adjoint.
      repeat rewrite Mmult_assoc.
      reflexivity.
    + simpl.
      unfold compose_super, super.
      rewrite Nat.sub_0_r.
      replace (size_wtype W + 1)%nat with (⟦ W ⊗ Qubit⟧)%qc by easy.
      rewrite H by auto.
      unfold denote_iso_db_box.
      simpl.
      unfold apply_new0, denote_init0, super.
      rewrite Nat.add_1_r.
      repeat rewrite Mmult_adjoint.
      remember (denote_iso_db_circuit (S (size_wtype W)) (hoas_to_db (Γ ++ [Some Qubit]) (c (qubit (length Γ))))) as A.
      repeat rewrite Mmult_assoc.
      Msimpl.
      Set Printing All. (* This is terrible messy. Tactics needed *)
      rewrite Nat.add_0_r.
      match goal with
      | [|- context[@adjoint ?a ?b (@kron ?c ?d ?e ?f ?B ?C)]] =>
        replace (@adjoint a b (@kron c d e f B C)) with
                (@adjoint (c*e) (d*f) (@kron c d e f B C))
      end.
      2: match goal with
         | [|- @adjoint ?a ?b ?B = @adjoint ?a' ?b' ?B] =>
           replace a with a' by unify_pows_two;
           replace b with b' by unify_pows_two;
           reflexivity
         end.      
      rewrite kron_adjoint.
      Msimpl.
      unify_pows_two.
      rewrite Nat.add_1_r.
      replace (2 ^ S (size_wtype W))%nat with (2 ^ (size_wtype W) * 2)%nat by unify_pows_two.
      repeat rewrite Mmult_assoc.
      reflexivity.
      Unset Printing All.
    + simpl.
      unfold compose_super, super.
      rewrite Nat.sub_0_r.
      replace (size_wtype W + 1)%nat with (⟦ W ⊗ Qubit⟧)%qc by easy.
      rewrite H by auto.
      unfold denote_iso_db_box.
      simpl.
      unfold apply_new1, denote_init1, super.
      rewrite Nat.add_1_r.
      repeat rewrite Mmult_adjoint.
      remember (denote_iso_db_circuit (S (size_wtype W)) (hoas_to_db (Γ ++ [Some Qubit]) (c (qubit (length Γ))))) as A.
      repeat rewrite Mmult_assoc.
      Msimpl.
      rewrite Nat.add_0_r.
      match goal with
      | [|- context[@adjoint ?a ?b (@kron ?c ?d ?e ?f ?B ?C)]] =>
        replace (@adjoint a b (@kron c d e f B C)) with
                (@adjoint (c*e) (d*f) (@kron c d e f B C))
      end.
      2: match goal with
         | [|- @adjoint ?a ?b ?B = @adjoint ?a' ?b' ?B] =>
           replace a with a' by unify_pows_two;
           replace b with b' by unify_pows_two;
           reflexivity
         end.      
      rewrite kron_adjoint.
      Msimpl.
      unify_pows_two.
      rewrite Nat.add_1_r.
      replace (2 ^ S (size_wtype W))%nat with (2 ^ (size_wtype W) * 2)%nat by unify_pows_two.
      repeat rewrite Mmult_assoc.
      reflexivity.
    + simpl.
      unfold compose_super, super.
      rewrite Nat.add_0_r.
      Search size_wtype NTensor.
      replace (size_wtype W - 1)%nat with (⟦(size_wtype W - 1) ⨂ Qubit⟧)%qc.
      Focus 2. Search size_wtype NTensor. rewrite size_ntensor. simpl. lia.
      rewrite H by auto.
      simpl.
      rewrite size_ntensor. simpl.
      rewrite Nat.mul_1_r.
      unfold denote_iso_db_box.
      simpl.
      unfold apply_assert0, denote_assert0, super.
      remember (denote_iso_db_circuit (size_wtype W - 1) (hoas_to_db (remove_pat p Γ) (c ()))) as A.
      remember (hd O (pat_to_list (subst_pat Γ p))) as k.
      Msimpl.
      match goal with
      | [|- context[@adjoint ?a ?b (@kron ?c ?d ?e ?f ?B ?C)]] =>
        replace (@adjoint a b (@kron c d e f B C)) with
                (@adjoint (c*e) (d*f) (@kron c d e f B C))
      end.
      Focus 2.
      match goal with
         | [|- @adjoint ?a ?b ?B = @adjoint ?a' ?b' ?B] =>
           replace a with a'; 
           replace b with b';
           unify_pows_two;  
           try reflexivity
         end.      

      (* aha! issue. *)
      (* We need premises about the contents of gamma being bounded *)
      (* Specifically, k < [W] *)
      (* We know from pat_to_list_bounded that k < [Γ] (or [Γ] = k = 0) *)
      (* We also have size_ctx (add_fresh_state w Γ) = (size_ctx Γ + size_wtype w)%nat *)
      
      Search pat_to_list.
      Search add_fresh_state.

      reflexivity.
      match goal with
      | [@Mmult ?a ?b ?c ]
      Mmult_assoc.
      apply f_equal2; trivial.
      reflexivity.
  - inversion pf.
Qed.
*)
