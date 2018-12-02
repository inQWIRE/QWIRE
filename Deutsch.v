Require Import Prelim.
Require Import Monad.
Require Import Matrix.
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Complex.
Require Import TypeChecking.
Require Import Denotation.
Require Import Composition.
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
  rewrite (Cmult_comm (/√2) _).
  repeat (rewrite (Cmult_assoc 2 (/2)); autorewrite with C_db).
  easy.
Qed.

Lemma size_octx_0 : forall Γ, Γ = ∅ -> size_octx Γ = 0%nat.
Proof.
  intros. 
  subst.
  reflexivity.
Qed.

(* With edge cases that break monoid *)
Ltac solve_merge' :=
  match goal with
  | [ |- ?Γ == ∅ ∙ ?Γ2] => split; [validate|rewrite merge_nil_l; easy]
  | [ |- ?Γ == ?Γ1 ∙ ∅] => split; [validate|rewrite merge_nil_r; easy]
  | _                  => solve_merge
  end.

Ltac compose_denotations :=
  match goal with
  | [ |- context[denote_db_circuit ?safe ?n_Γ0 ?n_Γ1' (hoas_to_db ?Γ1' (compose ?c ?f))] ]  
         => let Γ1 := fresh "Γ1" in evar (Γ1 : Ctx);
            (* instantiate Γ1 *)
            assert (pf_f : Γ1 ⊢ f :Fun) by (unfold Γ1; type_check);
            let Γ := fresh "Γ" in evar (Γ : Ctx);
            (* instantiate Γ *)
            assert (pf_merge : Valid Γ1' == Γ1 ∙ Γ) by (unfold Γ, Γ1; solve_merge');
            let pf_c := fresh "pf_c" in
            assert (pf_c : Γ ⊢ c :Circ); [ | 
            let Γ0 := fresh "Γ0" in evar (Γ0 : Ctx);
            let Γ01 := fresh "Γ01" in evar (Γ01 : Ctx);
            let DC := fresh "DC" in
            specialize (@denote_compose safe _ c Γ pf_c _ f Γ0 Γ1 Γ1' Γ01 
                                        pf_f pf_merge) as DC;
            unfold denote_circuit in DC;
            assert (size_Γ0 : size_ctx Γ0 = n_Γ0);
            unfold Γ1, Γ, Γ0 in *
            ]
  end.

(*
Ltac compose_denotations :=
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
*)

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
  | true, true => (* constant true *) I 2 ⊗ σx
  | false, false => (* constant false *) I 4
  | true, false  => (* balanced id *)    cnot
  | false, true  => (* balanced flip *) M_balanced_neg
  end.

Lemma toUnitary_unitary : forall f, WF_Unitary (toUnitary f).
Proof.
  intros. 
  unfold toUnitary, WF_Unitary.
  destruct (f true), (f false); Msimpl.
  all: split; auto with wf_db.
  replace (σx × σx) with (I 2) by solve_matrix. rewrite id_kron. reflexivity.
  solve_matrix.
  unfold M_balanced_neg.
  apply WF_list2D_to_matrix.
  easy.
  intros li H.
  repeat (destruct H; subst; trivial). 
  unfold M_balanced_neg.  
  solve_matrix.
Qed.  

  Hint Unfold apply_box : den_db.

Lemma deutsch_constant : forall (f : bool -> bool) 
                                (U : Box (Qubit ⊗ Qubit)%qc (Qubit ⊗ Qubit)%qc),
      Typed_Box U ->
      (f = fun _ => true) \/ (f = fun _ => false) -> 
      (forall ρ, ⟦U⟧ ρ = (toUnitary f) × ρ × (toUnitary f)†) ->
      ⟦deutsch U⟧ I1 = ∣0⟩⟨0∣.
Proof.
  intros f U pf_U pf_constant H_U.

   (* simplify definition of deutsch U *)
  repeat (simpl; autounfold with den_db).
  Msimpl.

  compose_denotations.
  - unfold Γ. apply pf_U.
    apply types_pair with (Γ1 := Valid [Some Qubit]) 
                          (Γ2 := Valid [None ; Some Qubit]);
    [ validate | reflexivity
    | type_check; constructor 
    | type_check; repeat constructor 
    ].
  - instantiate (1:=[]). easy.
  - simpl in DC. rewrite DC. clear DC.
    repeat (simpl; autounfold with den_db).
    2: unfold Γ01; solve_merge'. 
    unfold Γ01. simpl.

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
      ⟦deutsch U⟧ I1 = ∣1⟩⟨1∣.
Proof.
  intros f U pf_U pf_constant H_U.

   (* simplify definition of deutsch U *)
    repeat (simpl; autounfold with den_db).
    Msimpl.

  compose_denotations.
  - unfold Γ. apply pf_U.
    apply types_pair with (Γ1 := Valid [Some Qubit]) 
                          (Γ2 := Valid [None ; Some Qubit]);
    [ validate | reflexivity
    | type_check; constructor 
    | type_check; repeat constructor 
    ].
  - instantiate (1:=[]). easy.
  - simpl in DC. rewrite DC. clear DC.
    repeat (simpl; autounfold with den_db).
    2: unfold Γ01; solve_merge'. 
    unfold Γ01. simpl.
    
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
