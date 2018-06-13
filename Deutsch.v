Require Import Prelim.
Require Import Monad.
Require Import Matrix.
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Complex.
Require Import TypeChecking.
Require Import Denotation.
Require Import DBCircuits.

Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.
Delimit Scope matrix_scope with M.


Delimit Scope circ_scope with qc.
Close Scope circ_scope. 
Open Scope matrix_scope.
Open Scope C_scope.

  Lemma arithmetic_fact :   2 * (2 * (/ √ 2 * (2 * (/ 2 * / 2))) * / √ 2) = 1. 
  Proof.
    assert ((2:C) <> (0:C))%C by admit.
    replace (2 * (/2 * /2)) with ((2 * /2) * /2)
      by (rewrite Cmult_assoc; reflexivity).
    rewrite Cinv_r; auto.
    rewrite Cmult_1_l; auto.
    rewrite (Cmult_comm (/√ 2) (/2)).
    replace (2 * (/2 * /√2)) with ((2 * /2) * /√2)
      by (rewrite Cmult_assoc; reflexivity).
    rewrite Cinv_r; auto.
    rewrite Cmult_1_l; auto.
    rewrite square_rad2.
    rewrite Cinv_r; auto.
  Admitted.

Lemma size_octx_0 : forall Γ, Γ = ∅ -> size_octx Γ = 0%nat.
Proof.
  intros. 
  subst.
  reflexivity.
Qed.



Ltac denote_compose :=
  match goal with
  | [ |- context[denote_db_circuit ?safe ?n_Γ0 ?n_Γ1' (hoas_to_db ?Γ1' (compose ?c ?f))] ]  
         => let Γ1 := fresh "Γ1" in evar (Γ1 : OCtx);
            (* instantiate Γ1 *)
            assert (pf_f : Γ1 ⊢ f :Fun) by (unfold Γ1; type_check);
            let Γ := fresh "Γ" in evar (Γ : OCtx);
            (* instantiate Γ *)
            assert (pf_merge : Γ1' == Γ1 ∙ Γ) by (unfold Γ, Γ1; solve_merge);
            let pf_c := fresh "pf_c" in
            assert (pf_c : Γ ⊢ c :Circ); [ | 
            let Γ0 := fresh "Γ0" in evar (Γ0 : OCtx);
            let DC := fresh "DC" in
            specialize (@denote_compose safe _ c Γ pf_c _ f Γ0 Γ1 Γ1' pf_f  pf_merge)
              as DC;
            unfold denote_circuit in DC;
            assert (size_Γ0 : size_octx Γ0 = n_Γ0);
            unfold Γ1, Γ, Γ0 in *
            ]
  end.

Lemma matrix_1_1_Id : forall (ρ : Matrix 1 1), Mixed_State ρ -> ρ = Id 1.
Admitted.

(* U (|x⟩⊗|y⟩) = |x⟩⊗|f x ⊕ y⟩ 
  If f is constant, deutsch U returns 0 
  If f is balanced, deutsch U returns 1 
*)
Section Deutsch.

  Definition M_balanced_neg : Matrix 4 4 := 
    list2D_to_matrix [[C0;C1;C0;C0]
                    ;[C1;C0;C0;C0]
                    ;[C0;C0;C1;C0]
                    ;[C0;C0;C0;C1]].
  Definition toUnitary (f : bool -> bool) : Matrix 4 4 :=
    match f true, f false with
    | true, true => (* constant true *) Id 2 ⊗ σx
    | false, false => (* constant false *) Id 4
    | true, false  => (* balanced id *)    cnot
    | false, true  => (* balanced other *) M_balanced_neg
    end.

  Lemma toUnitary_unitary : forall f, is_unitary (toUnitary f).
  Admitted.

  Hint Unfold apply_box : den_db.

Lemma deutsch_constant : forall (f : bool -> bool) 
                                (U : Box (Qubit ⊗ Qubit)%qc (Qubit ⊗ Qubit)%qc),
      Typed_Box U ->
      (f = fun _ => true) \/ (f = fun _ => false) -> 
      (forall ρ, ⟦U⟧ ρ = (toUnitary f) × ρ × (toUnitary f)†) ->
      ⟦deutsch U⟧ I1 = |0⟩⟨0|.
Proof.
  intros f U pf_U pf_constant H_U.

   (* simplify definition of deutsch U *)
    repeat (simpl; autounfold with den_db).
    Msimpl.

  denote_compose.
  - unfold Γ. apply pf_U.
    apply types_pair with (Γ1 := Valid [Some Qubit]) 
                          (Γ2 := Valid [None ; Some Qubit]);
    [ validate | reflexivity
    | type_check; constructor 
    | type_check; repeat constructor 
    ].
  - apply size_octx_0. reflexivity.
  - simpl in DC. rewrite DC. clear DC.
    repeat (simpl; autounfold with den_db).
    rewrite merge_nil_r. simpl.
    

    (* rewrite by the semantics of U *)
    rewrite denote_db_unbox in H_U. simpl in H_U.

    repeat (simpl in H_U; autounfold with den_db in H_U).
    unfold denote_circuit in H_U. simpl in H_U.
    rewrite H_U.

    (* simplify the goal *)
    destruct (toUnitary_unitary f) as [WFU UU]; simpl in WFU.
    Msimpl.

    (* if f is constant, then it is either always true or false *)
    destruct pf_constant as [pf_true | pf_false].
    + (* f = fun _ => true *)
      subst. unfold toUnitary. 
      solve_matrix.
      (* Arithmetic: 2 * 2 * 1/√2 * 2 * 1/2 * 1/2 * 1/√2 = 1 *)
      apply arithmetic_fact.
   + (* f = fun _ => false *)
     subst. unfold toUnitary.
     solve_matrix.
      (* Arithmetic: 2 * 2 * 1/√2 * 2 * 1/2 * 1/2 * 1/√2 = 1 *)
      apply arithmetic_fact.
  Qed.



Lemma deutsch_balanced : forall (f : bool -> bool) (U : Box (Qubit ⊗ Qubit)%qc (Qubit ⊗ Qubit)%qc),
      Typed_Box U ->
      (f = fun x => x) \/ (f = fun x => negb x) ->
      (forall ρ, ⟦U⟧ ρ = (toUnitary f) × ρ × (toUnitary f)†) ->
      ⟦deutsch U⟧ I1 = |1⟩⟨1|.
Proof.
  intros f U pf_U pf_constant H_U.

   (* simplify definition of deutsch U *)
    repeat (simpl; autounfold with den_db).
    Msimpl.

  denote_compose.
  - unfold Γ. apply pf_U.
    apply types_pair with (Γ1 := Valid [Some Qubit]) 
                          (Γ2 := Valid [None ; Some Qubit]);
    [ validate | reflexivity
    | type_check; constructor 
    | type_check; repeat constructor 
    ].
  - apply size_octx_0. reflexivity.
  - simpl in DC. rewrite DC. clear DC.
    repeat (simpl; autounfold with den_db).
    rewrite merge_nil_r. simpl.
    

    (* rewrite by the semantics of U *)
    rewrite denote_db_unbox in H_U. simpl in H_U.

    repeat (simpl in H_U; autounfold with den_db in H_U).
    unfold denote_circuit in H_U. simpl in H_U.
    rewrite H_U.

    (* simplify the goal *)
    destruct (toUnitary_unitary f) as [WFU UU]; simpl in WFU.
    Msimpl.

    (* if f is balanced, then it is either always identity or negation *)
    destruct pf_constant as [pf_id | pf_neg].
    + (* f = fun x => x *)
      subst. unfold toUnitary. 
      solve_matrix.
      (* Arithmetic: 2 * 2 * 1/√2 * 2 * 1/2 * 1/2 * 1/√2 = 1 *)
      apply arithmetic_fact.
   + (* f = fun x => ¬ x *)
     subst. unfold toUnitary. simpl. unfold M_balanced_neg, list2D_to_matrix. simpl.
     solve_matrix.
      (* Arithmetic: 2 * 2 * 1/√2 * 2 * 1/2 * 1/2 * 1/√2 = 1 *)
      apply arithmetic_fact.
  Qed.

        

End Deutsch.
