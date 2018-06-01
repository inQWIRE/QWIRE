Require Export HOASCircuits.
Require Import Monoid.
Require Import IndexContext.

(** Typechecking Tactic **)

(* Prevent compute from unfolding important fixpoints *)
Open Scope circ_scope.

Definition wproj {W1 W2} (p : Pat (W1 ⊗ W2)) : Pat W1 * Pat W2 :=
  match p with
  | pair p1 p2 => (p1, p2)  
  end.

Fixpoint pair_circ' {W1 W2} (p : Pat W1) (c2 : Circuit W2) : Circuit (W1 ⊗ W2) :=
  match c2 with
  | output p2   => output (pair p p2)
  | gate g p1 f => gate g p1 (fun p2 => pair_circ' p (f p2))
  | lift p1 f   => lift p1 (fun x => pair_circ' p (f x))
  end.
Fixpoint pair_circ {W1 W2} (c1 : Circuit W1) (c2 : Circuit W2) : Circuit (W1 ⊗ W2) :=
  match c1 with
  | output p1   => pair_circ' p1 c2
  | gate g p1 f => gate g p1 (fun p2 => pair_circ (f p2) c2)
  | lift p f    => lift p (fun b => pair_circ (f b) c2)
  end.
Notation "( x , y , .. , z )" := (pair_circ .. (pair_circ x y) .. z) (at level 0) : circ_scope.

Opaque wproj.

Delimit Scope circ_scope with qc.

(* Compose Typing *)

Notation OCtx := (IdxCtx VType).

Definition unsome (Γ : OCtx) : Ctx :=
  match Γ with
  | Some Γ' => Γ'
  | None    => []
  end.

 Lemma some_unsome : forall Γ, is_valid Γ ->
                          Some (unsome Γ) = Γ.
 Proof. intros Γ H. destruct Γ; [easy | inversion H]. Qed.

Lemma merge_valid : forall (Γ : Ctx) (Γ' : IdxCtx VType), Some Γ = Γ' ->
                                                     is_valid (Γ'). 
Proof. intros. subst. constructor. Qed.

(* Validate from TypingContexts is useless when your contexts aren't singletons. 
   Here is the old validate, updated with typeclasses! [grumble grumble] *)
Ltac validate :=
  repeat match goal with
  (* Solve trivial *)
  | [H : is_valid ?Γ |- is_valid ?Γ ]                  => exact H
  | [H: is_valid (?Γ1 ∙ ?Γ2) |- is_valid (?Γ2 ∙ ?Γ1) ] => rewrite M_comm; exact H
  (* Do substitutions *)
  | [H : ?Γ = ?Γ1 ∙ ?Γ2 |- _]          => rewrite H in *; clear H
  (* Remove ones *)
  | [|- context [⊤ ∙ ?Γ] ]             => rewrite M_unit_l by auto
  | [|- context [?Γ ∙ ⊤] ]             => rewrite M_unit_r by auto
  (* Reduce hypothesis to binary disjointness *)
  | [H: is_valid (?Γ1 ∙ (?Γ2 ∙ ?Γ3)) |- _ ] => rewrite (M_assoc Γ1 Γ2 Γ3) in H
  | [H: is_valid (?Γ1 ∙ ?Γ2 ∙ ?Γ3) |- _ ]   => apply (is_valid3 Var VType OCtx Γ1 Γ2 Γ3) in H as [? [? ?]]
  (* Reduce goal to binary disjointness *)
  | [|- is_valid (?Γ1 ∙ (?Γ2 ∙ ?Γ3)) ] => rewrite (M_assoc Γ1 Γ2 Γ3)
  | [|- is_valid (?Γ1 ∙ ?Γ2 ∙ ?Γ3) ]   => apply (is_valid3_forward Var VType OCtx Γ1 Γ2 Γ3); validate
end.

(* Not sure if these are useful *)
Lemma index_wrt_cons : forall (values : list OCtx) (i : nat) (idxs : list nat), 
    i < length values ->
    ⟨ index_wrt values (i :: idxs) ⟩ = nth i values ⊤ ∙ ⟨index_wrt values idxs⟩.
Proof.
  intros.
  replace (i :: idxs) with ([i] ++ idxs) by reflexivity.
  rewrite split_list by auto.
  replace (⟨ index_wrt values [i] ⟩) with (nth i values ⊤). easy.  
  simpl.
  gen i.
  induction values.
  - intros. inversion H. 
  - intros.
    destruct i.
    + simpl. destruct a. rewrite mergeIdxMap_nil_r. reflexivity. reflexivity.
    + simpl in *. rewrite IHvalues. reflexivity. omega.
Qed.

Lemma index_wrt_nil : forall (values : list OCtx), ⟨index_wrt values []⟩ = ⊤.
Proof. intros. reflexivity. Qed.

Opaque m.
Opaque one.

Ltac mk_evar t T := match goal with _ => evar (t : T) end.

Ltac safe_replace Γ Γ' := 
  repeat match goal with
  | [H : context[Γ] |- _] => tryif has_evar Γ then fail else replace Γ with Γ' in H by reflexivity
  | [|- context[Γ]]       => tryif has_evar Γ then fail else replace Γ with Γ' by reflexivity
  end.

Ltac ocontextify := 
  repeat match goal with
  (* Inductive Merges become merges *)
  | [|- ?Γ == ?Γ1 ⋓ ?Γ2] => idtac "1-1"; apply merge_fun_ind
  | [H : ?Γ == ?Γ1 ⋓ ?Γ2 |- _] => idtac "1-2"; apply merge_ind_fun in H
  (* Replace Ctx merges with OCtx merges *)
  | [|- context[mergeIdxMap ?Γ ?Γ']]       => idtac "2-1"; replace (mergeIdxMap Γ Γ') with (Some Γ ∙ Some Γ') by reflexivity
  | [H : context[mergeIdxMap ?Γ ?Γ'] |- _] => idtac "2-2"; replace (mergeIdxMap Γ Γ') with (Some Γ ∙ Some Γ') in H by reflexivity
  (* Remove "Some unsome"s *)
  | [H : is_valid (Some (unsome ?Γ)) |- _] => idtac "3-1"; clear H
  | [Γ := Some (unsome ?Γ') |- _ ]         => idtac "3-2"; unfold Γ in *; clear Γ
  | [H : context[Some (unsome ?Γ)] |- _ ]  => idtac "3-3"; rewrite some_unsome in H by (simpl; validate)
  (* Remove "Some"s *)
  | [H : context[Some ?Γ] |- _] => idtac "4";
                                 tryif is_evar Γ then fail else
                                       let V := fresh "V" in
                                       let Γ' := fresh "Γ" in 
                                       assert (V: is_valid (Some Γ)) by constructor;
                                       set (Γ' := Some Γ);
                                       safe_replace (Some Γ) Γ'
  end;
  try match goal with
  | [|- context[Some ?Γ]] => is_evar Γ; 
                                   let V := fresh "V" in
                                   let Γ' := fresh "Γ" in 
                                   let none := mk_evar Γ' (IdxCtx VType) in        
                                   assert (V: is_valid (Some Γ)) by constructor;
                                   replace (Some Γ) with Γ' in *;
                                   cbv [Γ'] 
  end.


Lemma compose_typing : forall Γ1 Γ1' Γ W W' (c : Circuit W) (f : Pat W -> Circuit W'),
        Γ1 ⊢ c :Circ -> 
        Γ ⊢ f :Fun -> 
        forall {pf : Γ1' == Γ1 ⋓ Γ},
        Γ1' ⊢ compose c f :Circ.
Proof.
  intros Γ1 Γ1' Γ W W' c f types_c.
  gen Γ1' Γ.
  dependent induction types_c; intros Γ0 Γ01' types_f pf0.
  * simpl. subst. eapply types_f; eauto. 
  * simpl. 

    eapply types_gate.
    apply t.
    intros.   
    eapply X.
    2: apply X1.
    2: apply types_f.
    Focus 3.

    ocontextify.
    rewrite pf0, m.
    monoid.
    symmetry.
    apply some_unsome.

    simpl in *.
    validate.

  Focus 1.

    simpl in *.
    ocontextify.
    
Ltac clear_unsomes :=
  simpl in *;
  repeat match goal with
  (* Remove "Some (unsomes)" *)
  | [V : is_valid (Some (unsome _)) |- _]  => clear V
  | [Γ := Some (unsome _) |- _ ]           => unfold Γ in *; clear Γ
  | [H : context[Some (unsome _)] |- _ ]   => rewrite some_unsome in H by (simpl; validate)

  end.

    clear_unsomes.
    ocontextify.
    
    reflexivity. (* monoid !!!!!! *)
    symmetry.
    apply some_unsome.

    (* This needs to be automated - "clear unsomes"?*)
    simpl in *.
    unfold Γ5 in *. clear Γ5.
    rewrite some_unsome in X0 by (simpl; validate). 
    simpl in X0.
    clear V1. (* useless *)
    safe_replace (Some Γ) Γ10.
    safe_replace (Some Γ2) Γ4.
    safe_replace (Some Γ01') Γ8.
    validate.

  Focus 1.
    simpl in *.
    ocontextify.
    rewrite X0.
    unfold Γ5 in *.
    


    subst.

    cbv [Γ5].

    simpl in Γ5.
    unfold Γ5. rewrite some_unsome in Γ5.

    rewrite m in pf0; clear m.
    simpl in *.
    safe_replace (Some Γ) Γ10.
    safe_replace (Some Γ2) Γ4.
    simpl in Γ5.
    
    validate.

    symmetry.
    apply some_unsome.
    simpl in *.
    rewrite m in *; rewrite pf0 in *.
    validate.
  


  Focus 2.
    simpl in X0.
    rewrite mergeIdxMap_nil_r in X0.
    rewrite merge_n
    ocontextify.
    simpl in A1.
    subst.

  ocontextify.


  match goal with 
  | [|- context[mergeIdxMap ?Γ ?Γ']]       => replace (mergeIdxMap Γ Γ') with (Γ ∙ Γ') by reflexivity
  end.

  validate.


(* stuff that works but that we are trying to tacticify *)
      apply merge_fun_ind.
      apply merge_ind_fun in pf0. rewrite pf0.
      apply merge_ind_fun in m. rewrite m.
      evar (Δ : OCtx).
      (*  match goal with
          [|- context  [Some ?Δ']] => is_evar Δ'; idtac Δ'; replace (Some Δ') with Δ
          end. (* WTF?      ?? *) *)
      match goal with
        [|- context[Some ?Δ']] => is_evar Δ'; idtac Δ'; remember (Some Δ') as Δ''; replace Δ'' with Δ    
      end. 
      cbv [Δ].
      monoid.
      subst.
      unfold Δ.
      symmetry.
      simpl.
      apply some_unsome.
      replace (mergeIdxMap Γ Γ01') with (Some Γ ∙ Some Γ01') by reflexivity.
      subst.
      validate.
  Focus 1.
      apply merge_fun_ind.
      apply merge_ind_fun in m.
      apply merge_ind_fun in X0.
      apply merge_ind_fun in pf0.
      evar (Δ : OCtx).
      match goal with
        [|- context[Some ?Δ']] => is_evar Δ'; idtac Δ'; remember (Some Δ') as Δ''; replace Δ'' with Δ    
      end.       
      cbv [Δ].
      (* why is monoid failing??? *) (* monoid. *) reflexivity.
      subst.
      unfold Δ.
      symmetry.
      simpl.
      apply some_unsome.
      replace (mergeIdxMap Γ2 Γ) with (Some Γ2 ∙ Some Γ) by reflexivity.
      subst.
      rewrite some_unsome in X0 by validate.
      replace (mergeIdxMap Γ Γ01') with (Some Γ ∙ Some Γ01') in X0 by reflexivity.
      validate.
   Focus 1.
      apply merge_fun_ind.
      apply merge_ind_fun in m.
      apply merge_ind_fun in X0.
      apply merge_ind_fun in pf0.
      replace (mergeIdxMap Γ2 Γ) with (Some Γ2 ∙ Some Γ) by reflexivity.
      replace (mergeIdxMap Γ Γ01') with (Some Γ ∙ Some Γ01') in X0 by reflexivity.
      rewrite some_unsome in X0 by validate.
      rewrite some_unsome by validate.
      rewrite X0.
      monoid.
  * simpl.
    econstructor.
    apply t.
    Focus 2.
      apply merge_fun_ind.
      apply merge_ind_fun in m.
      apply merge_ind_fun in pf0.
      evar (Δ : OCtx).
      match goal with
        [|- context[Some ?Δ']] => is_evar Δ'; idtac Δ'; remember (Some Δ' : OCtx) as Δ'' (*; replace Δ'' with Δ*)    
      end. 
(*    match goal with
        [|- context[Some ?Δ']] => is_evar Δ'; rewrite <- HeqΔ''    
      end. *)
      remember (Some Γ0) as NO. remember (@Some (IdxMap VType) Γ1) as STOP. 
      rewrite <- HeqΔ''. 
      replace Δ'' with Δ.
      cbv [Δ].
      rewrite pf0.
      rewrite m.
      subst.
      monoid.
      subst.
      unfold Δ.
      symmetry.
      simpl.
      apply some_unsome.
      rewrite mergeIdxMap_nil_r.
      replace (mergeIdxMap Γ2 Γ01') with (Some Γ2 ∙ Some Γ01') by reflexivity.
      validate.
    Focus 1.
      intros b.
      rewrite mergeIdxMap_nil_r.
      eapply X.
      apply types_f.
      apply merge_fun_ind.
      apply merge_ind_fun in m.
      apply merge_ind_fun in pf0.
      rewrite some_unsome by validate.
      replace (mergeIdxMap Γ2 Γ01') with (Some Γ2 ∙ Some Γ01') by reflexivity.
      (* monoid !!! *) reflexivity.
Qed.      
      

(* Automation *)

Ltac goal_has_evars := 
  match goal with 
  [|- ?G ] => has_evars G
  end.

Ltac invert_patterns := 
  repeat match goal with
  | [ p : Pat One |- _ ] => dependent destruction p
  | [ p : Pat Qubit |- _] => dependent destruction p
  | [ p : Pat Bit |- _] => dependent destruction p
  | [ p : Pat (_ ⊗ _) |- _ ] => dependent destruction p
  | [ H : Types_Pat ?Γ () |- _ ]           => is_var Γ; inversion H; subst
  | [ H : Types_Pat ?Γ (qubit _) |- _ ]    => is_var Γ; inversion H; subst
  | [ H : Types_Pat ?Γ (bit _)   |- _ ]    => is_var Γ; inversion H; subst
  | [ H : Types_Pat ?Γ (pair _ _) |- _ ]   => is_var Γ; dependent destruction H
  end.

Create HintDb typed_db.

Ltac type_check_once := 
  intros;
  try match goal with 
  | [|- Typed_Box _ ]           => solve [eauto with typed_db] (* extensible *)
  | [|- @Typed_Box ?W1 ?W2 ?c]  => unfold Typed_Box in *; try unfold c
  end;
  intros;
  simpl in *;
  subst; 
  invert_patterns;
  repeat match goal with 
  (* Should break this down by case - in lift case, 
     need to choose bit or qubit as appropriate *)
  | [ b : bool |- _ ]              => destruct b 
  | [ H : _ == _ ⋓ _ |- _ ]     => destruct H
  | [ |- @Types_Circuit _ _ _ ] => econstructor; type_check_once

  | [ |- @Types_Circuit _ _ (if ?b then _ else _) ]
                                => destruct b; type_check_once

  (* compose_typing : specify goal. *)                                  
  | [ |- @Types_Circuit _ _ _ ] =>  eapply compose_typing; type_check_once 

  | [ H : forall a b, Types_Pat _ _ -> Types_Circuit _ _ |- Types_Circuit _ _] 
                                => apply H; type_check_once

  | [ H : @Types_Pat _ _ ?p |- @Types_Pat _ _ ?p ] 
                                => exact H
  | [ H : @Types_Pat ?Γ1 _ ?p |- @Types_Pat ?Γ2 _ ?p ] 
                                   (* in case they don't line up exactly *)
                                => replace Γ2 with Γ1; [exact H | monoid]

  | [ |- Types_Pat _ _ ]        => econstructor; type_check_once
  | [ |- ?Γ == ?Γ1 ⋓ ?Γ2 ]      => has_evars (Γ1 ∙ Γ2 ∙ Γ)
(*  | [ |- _ = _ ∙ _ ]            => solve_merge *)
  end; 
  (* Runs monoid iff a single evar appears in context *)
  match goal with 
  | [|- is_valid ?Γ] => tryif (has_evar Γ)   
                        then (idtac (*"can't validate"; print_goal*))
                        else (idtac (*"validate"; print_goal*); validate)
  | [|- ?G ]         => tryif (has_evars G)  
                        then (idtac (*"can't monoid"; print_goal*))
                        else (idtac (*"monoid"; print_goal*); monoid)
  end.

(* Useful for debugging *)
Ltac type_check_num := 
  let pre := numgoals in idtac "Goals before: " pre "";
  [> type_check_once..];
  let post := numgoals in idtac "Goals after: " post "";
  tryif (guard post < pre) then type_check_num else idtac "done".

(* Easiest solution *)

Ltac type_check := let n := numgoals in do n [> type_check_once..].
