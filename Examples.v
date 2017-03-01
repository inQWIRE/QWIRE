Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import TypedCircuits.
Import TC.
Import ListNotations.
Open Scope list_scope.
        
(* Merging Contexts *)
Program Definition mmerge_atom (o1 o2 : option WType) {dis : [o1] ∥ [o2]} :=
  match o1, o2 with
  | None, None   => None
  | None, Some W => Some W 
  | Some W, None => Some W
  | Some W1, Some W2 => _
  end.
Next Obligation. inversion dis. inversion H0; subst. inversion H6. Defined.

Program Fixpoint mmerge (Γ1 Γ2 : Ctx) (dis : Γ1 ∥ Γ2) := 
  match Γ1, Γ2 with 
  | [], _ => Γ2
  | _, [] => Γ1
  | (o1 :: Γ1'), (o2 :: Γ2') => @mmerge_atom o1 o2 _ :: mmerge Γ1' Γ2' _
  end.
Next Obligation. destruct dis. inversion m; subst.
                 exists [o]. constructor; trivial. constructor. Defined.
Next Obligation. destruct dis. inversion m; subst.
                 exists g; assumption. Defined.

Notation "Γ1 ⋓ Γ2" := (mmerge Γ1 Γ2 _) (at level 30).

Lemma merge_atom_irrelevant : forall o1 o2 D1 D2, 
                                @mmerge_atom o1 o2 D1 = @mmerge_atom o1 o2 D2.
Proof.
  intros.
  inversion D1. inversion H0; subst. inversion H6; subst; reflexivity.
Qed.  

Lemma merge_irrelevant : forall Γ1 Γ2 D1 D2, mmerge Γ1 Γ2 D1 = mmerge Γ1 Γ2 D2.
Proof.
  induction Γ1. reflexivity.
  intros.
  destruct Γ2.
  simpl. reflexivity.
  simpl. 
  erewrite merge_atom_irrelevant.
  erewrite IHΓ1.
  reflexivity.
Qed.  

Lemma mmerge_atom_refl : forall o1 o2 (dis: [o1] ∥ [o2]), 
                        MergeOption o1 o2 (@mmerge_atom o1 o2 dis).
Proof.
  intros.
  destruct o1, o2; (try constructor).
  destruct dis.
  inversion m; subst.
  inversion H5.
Qed.

Lemma mmerge_refl : forall Γ1 Γ2 (dis: Γ1 ∥ Γ2), MergeCtx Γ1 Γ2 (@mmerge Γ1 Γ2 dis).
Proof.
  induction Γ1.
  intros. simpl. constructor.
  intros.
  destruct Γ2.
  simpl. constructor.
  simpl.
  constructor.
  apply mmerge_atom_refl.
  apply IHΓ1.
Qed.

Lemma mmerge_symm : forall Γ1 Γ2 (D: Γ1 ∥ Γ2), 
                      mmerge Γ1 Γ2 D = mmerge Γ2 Γ1 (disjoint_symm _ _ D). 
Proof.
  induction Γ1.
  intros. simpl. 
  destruct Γ2; reflexivity.
  intros.
  destruct Γ2.
  reflexivity.
  simpl.
  rewrite IHΓ1.
  destruct D.
  inversion m; subst.
  inversion H5; subst; simpl; erewrite merge_irrelevant; reflexivity.
Qed.  

(*
Lemma mmerge_assoc_r : forall Γ1 Γ2 Γ3 Γ4 D, MergeCtx (mmerge Γ1 Γ2 D) Γ3 Γ4 ->
                                        {D' : _ & MergeCtx Γ1 (mmerge Γ2 Γ3 D') Γ4}.
Proof.
  intros.
 *) 
  

Lemma mmerge_merge3 : forall Γ1 Γ2 Γ3 Γ4 D, MergeCtx (mmerge Γ1 Γ2 D) Γ3 Γ4 -> 
                                       merge3 Γ1 Γ2 Γ3 Γ4.
Proof.
  intros.
  unfold merge3.
  exists (mmerge Γ1 Γ2 D).
  split.
  apply mmerge_refl.
  assumption.
Qed.  

Lemma merge3_mmerge : forall Γ1 Γ2 Γ3 Γ4, merge3 Γ1 Γ2 Γ3 Γ4 -> 
                                     {D : _ & MergeCtx (mmerge Γ1 Γ2 D) Γ3 Γ4}.
Proof.
  intros.
  destruct H0 as [Γ [H1 H2]].
  assert (Γ1 ∥ Γ2) as D1. exists Γ. assumption.
  exists D1.
  specialize (mmerge_refl _ _ D1). intros.
  apply (merge_functional H1) in H0.
  subst.
  assumption.  
Qed.  


(*
Lemma mmerge_assoc : forall Γ1 Γ2 Γ3 Γ4 dis dis', MergeCtx (mmerge Γ1 Γ2 dis) Γ3 Γ4 ->
                                             MergeCtx Γ1 (mmerge Γ2 Γ3 dis') Γ4.
Proof.
*)  

(* Projecting out elements of tensors *)
Inductive sigT23 (A:Type) (P Q R : A -> A -> Type) : Type :=
    existT23 : forall (x y : A), P x y -> Q x y -> R x y -> sigT23 A P Q R.

(*
Notation "{ x, y : A & P & Q & R }" := (sigT23 A (fun x y => P) (fun x y => Q) (fun x y => R)).
*)

Arguments existT23 {A} {P Q R} x y p1 p2 M.

Program Definition wproj {Γ W1 W2} (p : Pat Γ (Tensor W1 W2)) : 
  sigT23 Ctx (fun x y => Pat x W1) (fun x y => Pat y W2) (fun x y => MergeCtx x y Γ) :=
(*  {Γ1 Γ2 : Ctx & Pat Γ1 W1 & Pat Γ2 W2 & MergeCtx Γ1 Γ2 Γ} *)
  match p with 
  | unit => _
  | qubit _ _ _ => _
  | bit _ _ _ => _
  | pair Γ1 Γ2 Γ W1 W2 M p1 p2 => 
    existT23 Γ1 Γ2 p1 p2 M  
  end.

Check wproj.

(*
Notation "⟨ w1 , w2 ⟩" := (pair _ _ _ _ _ _ w1 w2) (at level 11, left associativity) : circ_scope. *)
(*
Notation "w1 & w2" := (pair _ _ _ _ _ _ w1 w2) (at level 11, left associativity) : circ_scope. *)
Notation "w1 * w2" := (pair _ _ _ _ _ _ w1 w2) (at level 40, left associativity) : circ_scope.
Notation "(())" := unit : circ_scope.

Parameter Δ1 Δ2 Δ3 Δ4 Δ5 Δ6 Δ7: Ctx.

(* Getting contexts for input patterns *)

Open Scope circ_scope.

(*** Tactics ***)

(* Prevent compute from unfolding important fixpoints *)
Opaque wproj.
Opaque Ctx.

Arguments merge_assoc {Γ1 Γ2 Γ3 Γ Γ' Γ0} M1 M2 M3.
Arguments merge_disjoint {Γ1 Γ2 Γ3 Γ Γ'} M1 M2.
Notation msym := merge_symm.

Ltac type_check_once := 
  intros;
  compute in *;
  repeat match goal with 
  | [ |- ?Γ = ?Γ ]                  => reflexivity
  | [ p : Pat _ One |- _ ]          => inversion p; subst; clear p
  | [ |- Pat _ One ]                => apply unit
  | [ p: Pat ?Γ ?W |- Pat ?Γ ?W ]   => exact p (* danger? *)
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ3 |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => exact H
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ3 |- MergeCtx ?Γ2 ?Γ1 ?Γ3 ] => apply (merge_symm H)
  | [ H : MergeCtx [] ?Γ1 ?Γ2 |- _] => apply merge_nil_l in H; subst 
  | [ H : MergeCtx ?Γ1 [] ?Γ2 |- _] => apply merge_nil_r in H; subst
  | [ |- MergeCtx _ ?Γ ?Γ ]         => apply MergeNilL 
  | [ |- MergeCtx ?Γ _ ?Γ ]         => apply MergeNilR 
  | [ |- MergeCtx [] _ _]           => apply MergeNilL
  | [ |- MergeCtx _ [] _]           => apply MergeNilR
  | [ |- MergeCtx _ _ []]           => apply MergeNilL (* Both work *)
(* the following may fail *)
  | [ H : MergeCtx _ ?Γ2 ?Γ3 |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => apply H 
  | [ H : MergeCtx ?Γ1 _ ?Γ3 |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => apply H
  | [ H : MergeCtx ?Γ1 ?Γ2 _ |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => apply H 
  | [ H : MergeCtx _ ?Γ2 ?Γ3 |- MergeCtx ?Γ2 _ ?Γ3 ] => apply (merge_symm H)
  | [ H : MergeCtx ?Γ1 _ ?Γ3 |- MergeCtx _ ?Γ1 ?Γ3 ] => apply (merge_symm H)
  | [ H : MergeCtx ?Γ1 ?Γ2 _ |- MergeCtx ?Γ2 ?Γ1 _ ] => apply (merge_symm H)
(* /may fail *)
  | [ |- context[merge_disjoint ?H ?H'] ] =>
        destruct (merge_disjoint H H') as [[? ?] [? ?]]
(* For transitive merges *)
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ' , H': MergeCtx ?Γ' ?Γ3 ?Γ4 |- MergeCtx ?Γ1 ?Γ3 ?Γ'' ] =>
      apply (projT2 (fst (merge_disjoint H H')))
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ' , H': MergeCtx ?Γ' ?Γ3 ?Γ4 |- MergeCtx ?Γ2 ?Γ3 ?Γ'' ] =>
      apply (projT2 (snd (merge_disjoint H H'))) 
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ' , H': MergeCtx ?Γ' ?Γ3 ?Γ4 |- MergeCtx ?Γ3 ?Γ1 ?Γ'' ] =>
      apply (merge_symm (projT2 (fst (merge_disjoint H H')))) 
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ' , H': MergeCtx ?Γ' ?Γ3 ?Γ4 |- MergeCtx ?Γ3 ?Γ2 ?Γ'' ] =>
      apply (merge_symm (projT2 (snd (merge_disjoint H H')))) 
(* Associative *)
  | [H: MergeCtx ?Γ1 ?Γ3 ?Δ |- MergeCtx ?Γ2 ?Δ ?Γ' ] => 
    eapply merge_assoc; [| | apply H]; type_check_once; fail
  | [H: MergeCtx ?Γ1 ?Γ3 ?Δ |- MergeCtx ?Γ2 ?Δ ?Γ' ] => 
    eapply merge_assoc; [| | apply (msym H)]; type_check_once; fail
  | [H: MergeCtx ?Γ1 ?Γ3 ?Δ |- MergeCtx ?Δ ?Γ2 ?Γ' ] => 
    eapply msym; eapply merge_assoc; [| | apply H]; type_check_once; fail
  | [H: MergeCtx ?Γ1 ?Γ3 ?Δ |- MergeCtx ?Δ ?Γ2 ?Γ' ] => 
    eapply msym; eapply merge_assoc; [| | apply (msym H)]; type_check_once; fail
  end.

Ltac check_assoc := match goal with
(* Associative Merges *)
  | [H1 : MergeCtx ?Γ1 ?Γ2 ?Γ, H2: MergeCtx ?Γ ?Γ3 ?Γ', H3: MergeCtx ?Γ1 ?Γ3 ?Δ 
     |- MergeCtx ?Γ2 ?Δ ?Γ' ] => apply (merge_assoc H1 H2 H3)
  | [H1 : MergeCtx ?Γ1 ?Γ2 ?Γ, H2: MergeCtx ?Γ ?Γ3 ?Γ', H3: MergeCtx ?Γ1 ?Γ3 ?Δ 
     |- MergeCtx ?Δ ?Γ2 ?Γ' ] => apply (msym (merge_assoc H1 H2 H3))
  | [H1 : MergeCtx ?Γ2 ?Γ1 ?Γ, H2: MergeCtx ?Γ ?Γ3 ?Γ', H3: MergeCtx ?Γ1 ?Γ3 ?Δ 
     |- MergeCtx ?Γ2 ?Δ ?Γ' ] => apply (merge_assoc (msym H1) H2 H3)
  | [H1 : MergeCtx ?Γ2 ?Γ1 ?Γ, H2: MergeCtx ?Γ ?Γ3 ?Γ', H3: MergeCtx ?Γ1 ?Γ3 ?Δ 
     |- MergeCtx ?Δ ?Γ2 ?Γ' ] => apply (msym (merge_assoc (msym H1) H2 H3))
  | [H1 : MergeCtx ?Γ1 ?Γ2 ?Γ, H2: MergeCtx ?Γ3 ?Γ ?Γ', H3: MergeCtx ?Γ1 ?Γ3 ?Δ 
     |- MergeCtx ?Γ2 ?Δ ?Γ' ] => apply (merge_assoc H1 (msym H2) H3)
  | [H1 : MergeCtx ?Γ1 ?Γ2 ?Γ, H2: MergeCtx ?Γ3 ?Γ ?Γ', H3: MergeCtx ?Γ1 ?Γ3 ?Δ 
     |- MergeCtx ?Δ ?Γ2 ?Γ' ] => apply (msym (merge_assoc H1 (msym H2) H3))
  | [H1 : MergeCtx ?Γ2 ?Γ1 ?Γ, H2: MergeCtx ?Γ3 ?Γ ?Γ', H3: MergeCtx ?Γ1 ?Γ3 ?Δ 
     |- MergeCtx ?Γ2 ?Δ ?Γ' ] => apply (merge_assoc (msym H1) (msym H2) H3)
  | [H1 : MergeCtx ?Γ2 ?Γ1 ?Γ, H2: MergeCtx ?Γ3 ?Γ ?Γ', H3: MergeCtx ?Γ1 ?Γ3 ?Δ 
     |- MergeCtx ?Δ ?Γ2 ?Γ' ] => apply (msym (merge_assoc (msym H1) (msym H2) H3))
  | [H1 : MergeCtx ?Γ1 ?Γ2 ?Γ, H2: MergeCtx ?Γ ?Γ3 ?Γ', H3: MergeCtx ?Γ3 ?Γ1 ?Δ 
     |- MergeCtx ?Γ2 ?Δ ?Γ' ] => apply (merge_assoc H1 H2 (msym H3))
  | [H1 : MergeCtx ?Γ1 ?Γ2 ?Γ, H2: MergeCtx ?Γ ?Γ3 ?Γ', H3: MergeCtx ?Γ3 ?Γ1 ?Δ 
     |- MergeCtx ?Δ ?Γ2 ?Γ' ] => apply (msym (merge_assoc H1 H2 (msym H3)))
  | [H1 : MergeCtx ?Γ2 ?Γ1 ?Γ, H2: MergeCtx ?Γ ?Γ3 ?Γ', H3: MergeCtx ?Γ3 ?Γ1 ?Δ 
     |- MergeCtx ?Γ2 ?Δ ?Γ' ] => apply (merge_assoc (msym H1) H2 (msym H3))
  | [H1 : MergeCtx ?Γ2 ?Γ1 ?Γ, H2: MergeCtx ?Γ ?Γ3 ?Γ', H3: MergeCtx ?Γ3 ?Γ1 ?Δ 
     |- MergeCtx ?Δ ?Γ2 ?Γ' ] => apply (msym (merge_assoc (msym H1) H2 (msym H3)))
  | [H1 : MergeCtx ?Γ1 ?Γ2 ?Γ, H2: MergeCtx ?Γ3 ?Γ ?Γ', H3: MergeCtx ?Γ3 ?Γ1 ?Δ 
     |- MergeCtx ?Γ2 ?Δ ?Γ' ] => apply (merge_assoc H1 (msym H2) (msym H3))
  | [H1 : MergeCtx ?Γ1 ?Γ2 ?Γ, H2: MergeCtx ?Γ3 ?Γ ?Γ', H3: MergeCtx ?Γ3 ?Γ1 ?Δ 
     |- MergeCtx ?Δ ?Γ2 ?Γ' ] => apply (msym (merge_assoc H1 (msym H2) (msym H3)))
  | [H1 : MergeCtx ?Γ2 ?Γ1 ?Γ, H2: MergeCtx ?Γ3 ?Γ ?Γ', H3: MergeCtx ?Γ3 ?Γ1 ?Δ 
     |- MergeCtx ?Γ2 ?Δ ?Γ' ] => apply (merge_assoc (msym H1) (msym H2) (msym H3))
  | [H1 : MergeCtx ?Γ2 ?Γ1 ?Γ, H2: MergeCtx ?Γ3 ?Γ ?Γ', H3: MergeCtx ?Γ3 ?Γ1 ?Δ 
    |- MergeCtx ?Δ ?Γ2 ?Γ' ] => apply (msym (merge_assoc (msym H1) (msym H2) (msym H3)))
end.

Ltac check_assoc' := match goal with
  | [H: MergeCtx ?Γ1 ?Γ3 ?Δ |- MergeCtx ?Γ2 ?Δ ?Γ' ] => 
    eapply merge_assoc; [| | apply H]; type_check_once; fail
  | [H: MergeCtx ?Γ1 ?Γ3 ?Δ |- MergeCtx ?Γ2 ?Δ ?Γ' ] => 
    eapply merge_assoc; [| | apply (msym H)]; type_check_once; fail
  | [H: MergeCtx ?Γ1 ?Γ3 ?Δ |- MergeCtx ?Δ ?Γ2 ?Γ' ] => 
    apply msym; eapply merge_assoc; [| | apply H]; type_check_once; fail
  | [H: MergeCtx ?Γ1 ?Γ3 ?Δ |- MergeCtx ?Δ ?Γ2 ?Γ' ] => 
    apply msym; eapply merge_assoc; [| | apply (msym H)]; type_check_once; fail
end.  


(*  | [ H : MergeCtx _ ?Γ2 ?Γ3 |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => has_evar Γ1; exact H
  | [ H : MergeCtx ?Γ1 _ ?Γ3 |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => has_evar Γ2; exact H
  | [ H : MergeCtx ?Γ1 ?Γ2 _ |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => has_evar Γ3; exact H 
  | [ H : MergeCtx _ ?Γ2 ?Γ3 |- MergeCtx ?Γ2 ?Γ1 ?Γ3 ] => has_evar Γ1; 
                                                        apply (merge_symm H)
  | [ H : MergeCtx ?Γ1 _ ?Γ3 |- MergeCtx ?Γ2 ?Γ1 ?Γ3 ] => has_evar Γ2; 
                                                        apply (merge_symm H)
  | [ H : MergeCtx ?Γ1 ?Γ2 _ |- MergeCtx ?Γ2 ?Γ1 ?Γ3 ] => has_evar Γ3; 
                                                        apply (merge_symm H) *)

(* Useful for debugging *)
Ltac type_check_num := 
  let pre := numgoals in idtac "Goals before: " pre "";
  [> type_check_once..];
  let post := numgoals in idtac "Goals after: " post "";
  tryif (guard post < pre) then type_check_num else idtac.

(* Easiest solution *)
Ltac type_check := let n := numgoals in do n [> type_check_once..].  

(*** Paper Examples ***)

Definition id_circ {W} :  Box W W. 
  refine (box (fun Γ p1 => output _ p1)); type_check.
Defined.

Definition hadamard_measure : Box Qubit Bit.
  refine (box (fun Γ p1 => 
   gate _ _ H p1 
  (fun Γ2 Γ2' M2 p2 => gate _ _ meas p2
  (fun Γ3 Γ3' M3 p3 => output _ p3)))); type_check.
Defined.

Definition inSeq {W1 W2 W3} (c1 : Box W1 W2) (c2 : Box W2 W3) : Box W1 W3. 
  refine (box (fun Γ1 p1 => compose (unbox c1 _ p1) _  
                                (fun Γ2 Γ2' M2 p2 => unbox c2 _ p2))); type_check.
Defined.

Definition inPar {W1 W2 W1' W2'} (c1 : Box W1 W1') (c2 : Box W2 W2') : 
  Box (W1⊗W2) (W1'⊗W2').
  refine (
  box (fun Γ12 p12 => 
   let 'existT23 Γ1 Γ2 p1 p2 M := wproj p12 in 
   compose (unbox c1 _ p1) _
           (fun Γ3 Γ3' M3 p1' => compose (unbox c2 _ p2) _
                                      (fun Γ4 Γ4' M4 p2' => (output _ (p1' * p2') ))))); 
   type_check.
Defined.
   
Definition init (b : bool) : Box One Qubit.
  refine (
  if b then (box (fun Γ p1 => gate _ _ init1 p1 (fun Γ2 Γ2' M2 p2 => output _ p2)))
       else (box (fun Γ p1 => gate _ _ init0 p1 (fun Γ2 Γ2' M2 p2 => output _ p2))));
  type_check. 
Defined.

Definition bell00 : Box One (Qubit ⊗ Qubit).
  refine (
  box (fun Γ p1 => 
  (gate _ _ init0 p1
  (fun Γ2 Γ2' M2 p2 => gate _ _ init0 (())
  (fun Γ3 Γ3' M3 p3 => gate _ _ (* Γ2'? *) H p2
  (fun Γ4 Γ4' M4 p4 => gate _ _ CNOT (p3 * p4) 
  (fun Γ5 Γ5' M5 p5 => output _ p5))))))); type_check.
Defined.

Definition alice : Box (Qubit⊗Qubit) (Bit⊗Bit).
refine (
  box (fun Γ qa => 
  (gate _ _ CNOT qa
  (fun Γ2 Γ2' M2 p2 => let 'existT23 Γq Γa q a M := wproj p2 in gate Γa _ H q
  (fun Γ3 Γ3' M3 p3 => gate _ _ meas p3
  (fun Γ4 Γ4' M4 p4 => gate _ _ meas a 
  (fun Γ5 Γ5' M5 p5 => output _ (p4 * p5)))))))); type_check. Defined.

(*
Lemma wrong : forall Γ1 Γ2, {Γ3 : Ctx & MergeCtx Γ1 Γ2 Γ3}.
Proof.
  intros.
  esplit. 
  apply merge_refl.
  Stupid shelf!
*)

Definition bob' : Box (Bit⊗(Bit⊗Qubit)) Qubit. 
refine(
  box (fun Γxyb xyb =>
    let 'existT23 Γx Γyb x yb Mxyb := wproj xyb in
    gate _ _ (bit_control σx) yb
     (fun Γyb Γyb' Myb yb' =>
     let 'existT23 Γy' Γb' y' b' Myb' := wproj yb' in
      gate _ _ (bit_control σz) (x * b') (* <? *)
       (fun Γxb Γxb' Mxb xb =>
        gate _ _ discard y' 
         (fun Γz1 Γz1 Mz1 z1 =>
          let 'existT23 Γx' Γb'' x' b'' Mxb := wproj xb in
          gate _ _ discard x'
           (fun Γz2 Γz2' Mz2 z2 => output _ b'')))))); type_check.
Defined.

Definition bob : Box (Bit⊗Bit⊗Qubit) Qubit. 
refine(
  box (fun Γxyb xyb =>
    let 'existT23 Γxy Γb xy b Mxyb := wproj xyb in
    let 'existT23 Γx Γy x y Mxy := wproj xy in
    gate _ _ (bit_control σx) (y * b) 
     (fun Γyb Γyb' Myb yb =>
     let 'existT23 Γy' Γb' y' b' Myb := wproj yb in
      gate _ _ (bit_control σz) (x * b') (* <? *)
       (fun Γxb Γxb' Mxb xb =>
        gate _ _ discard y' 
         (fun Γz1 Γz1 Mz1 z1 =>
          let 'existT23 Γx' Γb'' x' b'' Mxb := wproj xb in
          gate _ _ discard x'
           (fun Γz2 Γz2' Mz2 z2 => output _ b'')))))); type_check.

rename x1 into Γyb.
apply merge_symm in Mxy.
specialize (merge3_assoc Γy Γx Γb Γxyb (existT _ Γxy (Datatypes.pair Mxy Mxyb))); intros.
destruct H0.
destruct p.
apply (merge_functional m0) in m1; subst.
apply m2.

eapply merge_symm.
eapply merge_assoc.
2: apply Myb0.
apply (merge_symm Myb).
type_check.

type_check.
Defined.

(*
Definition teleport' : Box Qubit Qubit.
  refine(
  box (fun Γq q =>
    compose (unbox bell00 _ unit) _
      (fun Γab Γab' Mab ab => 
       let 'existT23 Γa Γb a b Mab' := wproj ab in 
       compose (unbox alice _ (q * a)) _
               (fun Γxy Γxy' Mxy xy => 
                  let 'existT23 Γx Γy x y Mxy := wproj xy in 
                  unbox bob' _ (x * (y * b))))
      )); type_check.
Defined.
*)

Definition teleport : Box Qubit Qubit.
  refine(
  box (fun _ q =>
    compose (unbox bell00 _ unit) _
      (fun _ _ _ ab => 
       let 'existT23 _ _ a b _ := wproj ab in 
       compose (unbox alice _ (q * a)) _
               (fun _ _ _ qa => unbox bob _ (qa * b)))
      )); type_check.
Defined.


(* Right associative Tensor *)
Fixpoint Tensor (n : nat) (W : WType) := 
  match n with 
  | 0 => One
  | 1 => W
  | S n' =>  W ⊗ (Tensor n' W)
  end.

Infix "⨂" := Tensor (at level 30). 
(* Transparent Tensor. *)
Opaque Tensor.

Fixpoint inSeqMany {W} (n :nat) (c : Box W W) : Box W W := 
  match n with
  | 0 => id_circ
  | 1 => c
  | S n' => inSeq c (inSeqMany n' c)
  end.

Print inSeqMany.

(* Zero-indexed variant. I don't know why this is necessary *)
(* This will be fairly common *)
Fixpoint inParManyZ {W1 W2} (n : nat) (c : Box W1 W2) {struct n} : 
  Box (S n ⨂ W1) (S n ⨂ W2) :=
  match n with 
  | 0 => c
  | S n' => inPar c (inParManyZ n' c)
  end. 

Definition inParMany {W1 W2} (n : nat) (c : Box W1 W2) : Box (n ⨂ W1) (n ⨂ W2) := 
  match n with 
  | 0 => id_circ
  | S n' => inParManyZ n' c 
  end.

Eval compute in inParMany 4 hadamard_measure.

Parameter RGate : nat -> Unitary Qubit.

Local Obligation Tactic := type_check.

Fixpoint rotationsZ (m : nat) (n : nat) : Box (S (S n) ⨂ Qubit) (S (S n) ⨂ Qubit).
refine (
  match n as n0 return n = n0 -> Box (S (S n0) ⨂ Qubit) (S (S n0) ⨂ Qubit) with
  | 0 => fun eq => id_circ 
  | S n' => fun eq => box (fun Γ w =>
    let 'existT23 Γc Γqqs c qqs Mcqqs := wproj w in 
    let 'existT23 Γq Γqs q qs Mqqs := wproj qqs in 
    compose (unbox (rotationsZ m n') _ (c * qs)) _
            (fun Γcqs Γcqs' Mcqs cqs =>  
               let 'existT23 Γc' Γqs' c' qs' Mcqs' := wproj cqs in 
               gate _ _ (control (RGate (1 + m - n'))) (c' * q)
               (fun Γcq Γcq' Mcq cq => 
               let 'existT23 Γc'' Γq'' c'' q'' Mcq' := wproj cq in 
               output _ (c'' * (q'' * qs')))))
   end (eq_refl n)); type_check.

apply (merge_symm (projT2 (snd (merge_disjoint Mqqs (msym Mcqqs))))).

type_check.

Admitted.

Definition rotations (m : nat) (n : nat) : Box (S n ⨂ Qubit) (S n ⨂ Qubit) :=
  match n with 
  | 0 => id_circ
  | S n' => rotationsZ m n' 
  end.

Fixpoint qftZ (n : nat) : Box (S n ⨂ Qubit) (S n ⨂ Qubit).
refine(
  match n as n0 return n = n0 -> Box (S n0 ⨂ Qubit) (S n0 ⨂ Qubit) with 
  | 0 => fun eq => (box (fun Γ p1 =>  gate _ _ H p1 (fun Γ2 Γ2' M2 p2 => output _ p2)))
  | S n' => fun eq => box (fun Γqw qw =>
             let 'existT23 Γq Γw q w Mqw := wproj qw in
             compose (unbox (qftZ n') _ w) _
                     (fun Γw' Γw'' Mw' w' => (unbox (rotationsZ (S n') n') _ (q * w'))))
  end (eq_refl n)); type_check.
Defined.

Definition qft (n : nat) : Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  match n with 
  | 0 => id_circ
  | S n' => qftZ n'
  end.



fourier : Π(n:Nat). CIRC(  n qubit,   n qubit)= fun n => case n of
| 0 => id
| 1 => hadamard
    | S n’ => box (q,w) =>
                w <- unbox fourier n’ w;
                unbox rotations (S n’) n’ (q,w)

(* RGate (2+m-n') *)


(** Approaches to a general list-based solver **)
(*

1) For known head:

H : MergeCtx [...] Γ 

|­ MergeCtx [Γx ; Γy ; Γz] Γ

Saturate the tails of H and the goal (i.e. replace all compound contexts with their atoms). Then apply permute_equal H.

2a) 

H : [x ; y ; z ; a ; b ] Γ

MergeCtx [ x ; y ; z] ?Goal <-> MergeCtx [x ; y ; z ; a] ?Goal' <-> MergeCtx [x ; y ; z ; a ; b] ?Goal''


2b) 

H : [x ; y ; z ; a ; b ] Γ
-> H : [x ; y ; z ; a] Γ'
-> H : [x ; y ; z] Γ''

MergeCtx [ x ; y ; z] ?Goal

*)





(* *)