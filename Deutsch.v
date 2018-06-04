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

  Variable U : Box (Qubit ⊗ Qubit)%qc (Qubit ⊗ Qubit)%qc.
  Hypothesis U_WT : Typed_Box U.
  Variable f : bool -> bool.
  Variable M : Matrix 4 4. 

  Definition constant := (f = fun _ => true) \/ (f = fun _ => false).
  Definition balanced := (f = fun b => b) \/ (f = fun b => negb b).

  Lemma f_constant_true_M : (f = fun _ => true) -> M = Id 2 ⊗ σx.
  Admitted.

  Lemma f_constant_false_M : (f = fun _ => false) -> M = Id 4.
  Admitted.

  Lemma f_balanced_id_M : (f = fun x => x) -> M = cnot.
  Admitted.

  Definition M_balanced_neg : Matrix 4 4 := 
    list2D_to_matrix [[C0;C1;C0;C0]
                    ;[C1;C0;C0;C0]
                    ;[C0;C0;C1;C0]
                    ;[C0;C0;C0;C1]].
  Lemma f_balanced_neg_M : (f = fun x => negb x) -> M = M_balanced_neg.
  Admitted.



  Hypothesis M_encodes_f : forall x y,
             M × (bool_to_ket x ⊗ bool_to_ket y) 
           = bool_to_ket x ⊗ bool_to_ket (f x ⊕ y).

  Lemma M_unitary : is_unitary M.
  Admitted.

  Hypothesis U_encodes_M : ⟦U⟧ = super M.




  Lemma deutsch_constant : (f = fun _ => true) \/ (f = fun _ => false) -> 
                           forall ρ, Mixed_State ρ -> 
                           ⟦deutsch U⟧ ρ = ⟦new false⟧ ρ.
  Proof.
    intros pf_constant ρ pf_ρ. simpl in ρ.
    replace ρ with I1 by (symmetry; apply matrix_1_1_Id; auto).
    clear ρ pf_ρ.

    repeat (simpl; autounfold with den_db).
    Msimpl.

  denote_compose.
  - unfold Γ. apply apply_box_WT; auto. econstructor; [reflexivity | ].
    apply types_pair with (Γ1 := Valid [Some Qubit]) 
                          (Γ2 := Valid [None ; Some Qubit]);
    [ validate | reflexivity
    | type_check; constructor 
    | type_check; repeat constructor 
    ].
  - apply size_octx_0. reflexivity.
  - simpl in DC. rewrite DC. clear DC.

    (* rewrite by the semantics of U w/ respect to M *)
    rewrite denote_db_unbox in U_encodes_M.
    unfold denote_circuit in U_encodes_M.

    repeat (simpl in *; autounfold with den_db in *).

    (* rewrite defn of U *)
    rewrite merge_nil_r.
    unfold apply_box; simpl. 
    rewrite U_encodes_M. 

    (* simplify the goal *)
    destruct M_unitary as [WFU UU]; simpl in WFU.
    Msimpl.

    (* if f is constant, then it is either always true or false *)
    destruct pf_constant as [pf_true | pf_false].
    + (* f = fun _ => true *)
      assert (M_eq : M = Id 2 ⊗ σx) by (apply f_constant_true_M; auto).
      rewrite M_eq.
      solve_matrix.
      (* Arithmetic: 2 * 2 * 1/√2 * 2 * 1/2 * 1/2 * 1/√2 = 1 *)
      apply arithmetic_fact.
   + (* f = fun _ => false *)
     assert (M_eq : M = Id 4) by (apply f_constant_false_M; auto).
     rewrite M_eq.
     solve_matrix.
      (* Arithmetic: 2 * 2 * 1/√2 * 2 * 1/2 * 1/2 * 1/√2 = 1 *)
      apply arithmetic_fact.

  Qed.

        

  Lemma deutsch_balanced : (f = fun x => x) \/ (f = fun x => negb x) -> 
                           forall ρ, Mixed_State ρ -> 
                           ⟦deutsch U⟧ ρ = ⟦new true⟧ ρ.
    intros pf_balanced ρ pf_ρ. simpl in ρ.
    replace ρ with I1 by (symmetry; apply matrix_1_1_Id; auto).
    clear ρ pf_ρ.

    repeat (simpl; autounfold with den_db).
    Msimpl.

  denote_compose.
  - unfold Γ. apply apply_box_WT; auto. econstructor; [reflexivity | ].
    apply types_pair with (Γ1 := Valid [Some Qubit]) 
                          (Γ2 := Valid [None ; Some Qubit]);
    [ validate | reflexivity
    | type_check; constructor 
    | type_check; repeat constructor 
    ].
  - apply size_octx_0. reflexivity.
  - simpl in DC. rewrite DC. clear DC.

    (* rewrite by the semantics of U w/ respect to M *)
    rewrite denote_db_unbox in U_encodes_M.
    unfold denote_circuit in U_encodes_M.

    repeat (simpl in *; autounfold with den_db in *).

    (* rewrite defn of U *)
    rewrite merge_nil_r.
    unfold apply_box; simpl. 
    rewrite U_encodes_M. 

    (* simplify the goal *)
    destruct M_unitary as [WFU UU]; simpl in WFU.
    Msimpl.

    (* if f is balanced, then it is either always identity or negation *)
    destruct pf_balanced as [pf_id | pf_neg].
    + (* f = fun x => x *)
      assert (M_eq : M = cnot) by (apply f_balanced_id_M; auto).
      rewrite M_eq.
      solve_matrix.
      (* Arithmetic: 2 * 2 * 1/√2 * 2 * 1/2 * 1/2 * 1/√2 = 1 *)
      apply arithmetic_fact.
   + (* f = fun x => ¬b *)
     assert (M_eq : M = M_balanced_neg) by (apply f_balanced_neg_M; auto).
     rewrite M_eq.
     solve_matrix.
     unfold M_balanced_neg. unfold list2D_to_matrix. simpl.
     solve_matrix.

      (* Arithmetic: 2 * 2 * 1/√2 * 2 * 1/2 * 1/2 * 1/√2 = 1 *)
      autorewrite with C_db. 
      apply arithmetic_fact.

  Qed.

End Deutsch.