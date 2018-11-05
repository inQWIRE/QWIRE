Require Import Prelim.
Require Import Denotation.
Require Import HOASLib.
Require Import TypeChecking.
Require Import DBCircuits.
Require Import Composition.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

(*** Identity transformation ***)

Fixpoint transform_identity' {W : WType} (c : Circuit W) : Circuit W :=
  match c with
  | output p => output p
  | gate g p c' => gate g p (fun p => transform_identity' (c' p))
  | lift p c' => lift p (fun bs => transform_identity' (c' bs))
  end.

Definition transform_identity {W1 W2 : WType} (b : Box W1 W2) : Box W1 W2 :=
  match b with
  | box f => box (fun p => transform_identity' (f p))
  end.

Lemma transform_identity_WT : forall {W1 W2 : WType} (b : Box W1 W2), 
  Typed_Box b -> Typed_Box (transform_identity b).
Proof. 
  intros W1 W2 b.
  destruct b.
  unfold Typed_Box; simpl.
  intros H Γ p TP.
  specialize (H Γ p TP).
  remember (c p) as c'.
  clear - H.
  generalize dependent Γ.
  induction c'.
  - (* output p *)
    simpl. easy.
  - (* gate g p c' *)
    intros Γ H0.
    dependent destruction H0.
    econstructor.
    + apply t.
    + intros.
      apply H.
      eapply t0.
      apply pf2.
      assumption.
    + apply pf1. 
  - (* lift p c' *)
    intros Γ H0.
    dependent destruction H0.
    econstructor.
    + apply t.
    + intros.
      apply H.
      apply t0.
    + apply pf.
Qed.

(* We need some lemma like the following for the correctness proof. I don't think that
   this lemma follows directly from transform_identity_WT because transform_identity_WT
   says that

       (forall (Γ : OCtx) (p : Pat W1), Γ ⊢ p :Pat -> Γ ⊢ c p :Circ) ->
       forall (Γ : OCtx) (p : Pat W1), Γ ⊢ p :Pat -> Γ ⊢ transform_identity' (c p) :Circ.

   But the lemma below says that 

       Γ1 ⊢ p :Pat -> ... -> Γ12 ⊢ transform_identity' (f p) :Circ.
   
   In this statement, the environment that types (transform_identity' (f p)) is different
   from the environment that types p.
*)
Lemma transform_identity_circuit_WT : forall {W1 W2 : WType} (f : Pat W1 -> Circuit W2)
  (Γ1 Γ2 Γ12 : OCtx) (p : Pat W1),
    Γ1 ⊢ p :Pat ->
    Γ2 ⊢ f :Fun ->
    Γ12 == Γ1 ∙ Γ2 ->
    Γ12 ⊢ transform_identity' (f p) :Circ.             
Proof. Admitted.

Lemma transform_identity_circuit_correct : forall W (c : Circuit W) (Γ0 Γ : Ctx), 
    Γ ⊢ c :Circ ->
    ⟨ Γ0 | Γ ⊩ c⟩ = ⟨ Γ0 | Γ ⊩ (transform_identity' c)⟩.
Proof.
  intros W c Γ0 Γ WT.
  dependent induction WT.
  - (* output p *)
    reflexivity.
  - (* gate g p c' *)
    simpl. 
    replace (gate g p1 f) with (compose (gate g p1 (fun p => output p)) f) by auto.
    replace (gate g p1 (fun p => transform_identity' (f p))) with (compose (gate g p1 (fun p => output p)) (fun p => transform_identity' (f p))) by auto.    
    destruct Γ2 as [|Γ2]; try invalid_contradiction.
    assert (H1 : Γ == Γ2 ∙ Γ1). destruct pf1.
    rewrite merge_comm in pf_merge.
    easy. clear pf1.
    remember (Γ0 ⋓ Γ2) as Γ02.
    assert (Γ02 == Γ0 ∙ Γ2).
    (* Here we need to show that Γ0 ⋓ Γ2 is valid (where Γ0 is padding, and  Γ2 types f).
       I don't think there is enough information in the context to prove this... though
       I'm not sure. Maybe we need an additional assumption about Γ0? 
    *) 
    admit. 
    assert (Γ1 ⊢ gate_ p ← g @ p1; p :Circ) by type_check.
    destruct Γ1 as [|Γ1]; try invalid_contradiction.
    destruct Γ02 as [|Γ02]; try invalid_contradiction.
    repeat rewrite denote_compose with (Γ:=Γ1) (Γ0:=Γ0) (Γ1:=Γ2) (Γ1':=Γ) (Γ01:=Γ02); try assumption.    
    apply f_equal2.
    2: reflexivity.
    rewrite H with (Γ3:=(get_fresh_state w2 Γ2)) (Γ2':=(add_fresh_state w2 Γ2)). 
    reflexivity.
    3: reflexivity.
    split.
    { validate. }
    { rewrite add_fresh_state_merge with (w:=w2)
                                         (Γ':=add_fresh_state w2 Γ2)
                                         (Γ:=Γ2).
      rewrite merge_comm; reflexivity.
      reflexivity. }
    rewrite add_fresh_pat_eq.
    apply get_fresh_typed with (w:=w2) (Γ0:=Γ2).
    rewrite get_fresh_split; reflexivity.
    (* For this last part, we need to apply some well-typedness lemma about transform_identity
       over circuits. The lemma I am applying here is admitted above. 
    *)
    intros.
    apply (transform_identity_circuit_WT _ Γ3 Γ2 _ _); assumption.
  - (* lift p c' *)
    admit.
Admitted.

(*** Replace-one transformation ***)

(* If we have the identity transformation proven correct, then it should be 
   straight-forward(?) to prove that the following transformation, which replaces
   occurrences of the gate grep with the circuit crep, is correct as well. 


Fixpoint transform_replace_gate' {W w1 w2: WType} (c : Circuit W)
         (grep : Gate w1 w2) (crep : Circuit w2) : Circuit W :=
  match c with
  | output p => output p
  | gate g p c' =>  if g == grep (* some kind of equality over gates *)
                    then compose crep (fun p => transform_replace_gate' (c' p))
                    else gate g p (fun p => transform_replace_gate' (c' p))
  | lift p c' => lift p (fun bs => transform_replace_gate' (c' bs))
  end.

Definition transform_replace_gate {W1 W2 w1 w2 : WType} (b : Box W1 W2)
           (grep : Gate w1 w2) (crep : Circuit w2) : Box W1 W2 :=
  match b with
  | box f => box (fun p => transform_replace_gate' (f p) grep crep)
  end.


   The only difference between this transformation and the identity transformation
   is that, in the gate case, we may replace g by crep. So the only part of the 
   correctness proof that would need to change  is the part immediately after the 
   application of denote_compose in the "gate" case. 

   A more general replacement function would be able to replace an arbitrary 
   subcircuit by crep. 
*)

