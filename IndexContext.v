Require Import Prelim.
Require Import Monad.
Require Import Monoid.
Require Import TypingContext.

Section IndexContext.
Set Implicit Arguments.

Variable A : Type.


(* An index map is a map from nats to A's encoded as a list of option A's;
   index i maps to a if ls[i]=Some a *)
Definition IdxMap := list (option A).
Definition IdxCtx := option IdxMap.

Definition mergeOption (o1 o2 : option A) : option (option A) :=
  match o1, o2 with
  | _, None => Some o1
  | None, _ => Some o2
  | Some _, Some _ => None
  end.
Fixpoint mergeIdxMap (i1 i2 : IdxMap) : option IdxMap :=
  match i1, i2 with
  | nil, _ => Some i2
  | _, nil => Some i1
  | o1 :: i1, o2 :: i2 => do o ← mergeOption o1 o2;
                         do i ← mergeIdxMap i1 i2;
                         Some (o :: i)
  end.

Lemma mergeIdxMap_nil_r : forall i, mergeIdxMap i nil = Some i.
Proof.
  destruct i; auto.
Defined.


Lemma mergeIdxMap_step : forall o1 o2 i1 i2,
    mergeIdxMap (o1 :: i1) (o2 :: i2) = do o ← mergeOption o1 o2;
                                        do i ← mergeIdxMap i1 i2;
                                        Some (o :: i).
Proof.
  intros; auto.
Defined.

Fixpoint is_empty_map (i : IdxMap) :=
  match i with
  | nil => true
  | None :: i => is_empty_map i
  | Some _ :: _ => false
  end.


(* This will hold for all monads if you depend on functional extensionality *)
Lemma bind_option_eq : forall X Y (e : option X) (f f' : X -> option Y), 
      (forall x, f x = f' x) -> bind e f = bind e f'.
Proof.
  intros. destruct e; auto.
  simpl. auto.
Defined.
Arguments bind_option_eq {X Y} e.

(* This should really hold for all monads *)
Lemma bind_permut : forall {X Y Z} (ma : option X) (mb : option Y) (g : X -> Y -> option Z),
  bind ma (fun x => bind mb (g x)) = bind mb (fun y => bind ma (fun x => g x y)).
Proof.
  intros. destruct ma; destruct mb; auto.
Defined.


Lemma mergeOption_assoc : forall x y z,
                          do a ← mergeOption x y; mergeOption a z
                        = do b ← mergeOption y z; mergeOption x b.
Proof.
  destruct x; destruct y; destruct z; auto.
Defined.

Lemma mergeOption_comm : forall x y, mergeOption x y = mergeOption y x.
Proof.
  destruct x; destruct y; auto.
Defined.

Hint Resolve mergeIdxMap_nil_r.
Lemma IdxMap_assoc : forall a b c, 
      (do x ← mergeIdxMap b c; mergeIdxMap a x) = (do x ← mergeIdxMap a b; mergeIdxMap x c).
    assert (H : forall X (x : X), Some x = return_ x) by reflexivity.
    induction a as [ | x a]; intros;
    [  simpl; destruct (mergeIdxMap b c); auto | ].
    destruct b as [ | y b]; destruct c as [ | z c]; auto.
    * repeat rewrite mergeIdxMap_nil_r. 
      rewrite H, <- bind_left_unit.
      rewrite (bind_right_unit _ (mergeIdxMap (x :: a) (y :: b))) at 1.
      apply bind_option_eq; auto. 
    * repeat rewrite mergeIdxMap_step.
      repeat rewrite <- bind_associativity.
      rewrite (bind_option_eq (mergeOption y z) _
                (fun x0 => do i ← mergeIdxMap b c; mergeIdxMap (x :: a) (x0 :: i))); 
        [ | intros; rewrite <- bind_associativity; apply bind_option_eq; auto ].
      rewrite (bind_option_eq (mergeOption x y)  _
                (fun x0 => do i ← mergeIdxMap a b; mergeIdxMap (x0 :: i) (z :: c))); 
        [ | intros; rewrite <- bind_associativity; apply bind_option_eq; auto ].
      erewrite (bind_option_eq (mergeOption y z));
        [ | intros; apply bind_option_eq; intros; apply mergeIdxMap_step ].
      erewrite (bind_option_eq (mergeOption x y));
        [ | intros; apply bind_option_eq; intros; apply mergeIdxMap_step ].
      erewrite (bind_option_eq (mergeOption y z));
        [ | intros; apply bind_permut].
      erewrite (bind_option_eq (mergeOption x y));
        [ | intros; apply bind_permut].
      repeat rewrite bind_associativity.
      rewrite mergeOption_assoc.
      apply bind_option_eq; intros.
      repeat rewrite bind_associativity.
      rewrite IHa. reflexivity.
Defined.

Lemma IdxMap_comm : forall a b, mergeIdxMap a b = mergeIdxMap b a.
Proof.
  induction a as [ | x a]; destruct b as [ | y b]; auto.
    repeat rewrite mergeIdxMap_step.
    rewrite mergeOption_comm.
    apply bind_option_eq; intros o.
    rewrite IHa. reflexivity.
Defined.

Fixpoint singleton' (x : nat) (a : A) :=
  match x with
  | O => Some a :: nil
  | S x' => None :: singleton' x' a 
  end.


Lemma m'_cons_step : forall (o1 o2 : option A) Γ1 Γ2,
      mergeIdxMap (o1 :: Γ1) (o2 :: Γ2) = match mergeIdxMap Γ1 Γ2, o1, o2 with
                                          | Some Γ, _, None => Some (o1 :: Γ)
                                          | Some Γ, None, _ => Some (o2 :: Γ)
                                          | _, _, _         => None
                                          end.
Proof.
  simpl. intros. destruct o1; destruct o2; auto. simpl. destruct (mergeIdxMap Γ1 Γ2); auto.
Qed.

Lemma is_Some_m'_None_None : forall Γ1 Γ2,
      is_Some (mergeIdxMap (None :: Γ1) (None :: Γ2)) = is_Some (mergeIdxMap Γ1 Γ2).
Admitted.

Lemma is_Some_m'_Some_None : forall a Γ1 Γ2,
      is_Some (mergeIdxMap (Some a :: Γ1) (None :: Γ2)) = is_Some (mergeIdxMap Γ1 Γ2).
Admitted.

Lemma is_Some_m'_None_Some : forall a Γ1 Γ2,
      is_Some (mergeIdxMap (None :: Γ1) (Some a :: Γ2)) = is_Some (mergeIdxMap Γ1 Γ2).
Admitted.

Lemma is_Some_m'_Some_Some : forall a1 a2 Γ1 Γ2,
      is_Some (mergeIdxMap (Some a1 :: Γ1) (Some a2 :: Γ2)) = false.
Admitted.




End IndexContext.
Hint Resolve mergeIdxMap_nil_r.
About singleton.

Instance PMonoid_IdxMap A : PPCM (IdxMap A) :=
    { one' := nil; m' := @mergeIdxMap A}.
Instance PMonoid_IdxMap_Laws A : PPCM_Laws (IdxMap A).
Proof.
  split.
  - simpl; auto.
  - apply IdxMap_assoc.
  - apply IdxMap_comm.
Defined.
Instance Monoid_IdxMap_Laws A : PCM_Laws (IdxCtx A) :=
  PPCM_to_PCM_Laws (IdxMap A).
(* WHY IS THIS NECESSARY? (see examples at end of file *)
Hint Resolve Monoid_IdxMap_Laws.

Instance PTypingContext_IdxMap A : PTypingContext nat A (IdxMap A) :=
  { singleton' := @singleton' A
  }.

Instance DecidablePaths_nat : DecidablePaths nat :=
  { decPaths := Nat.eq_dec }.

Ltac unfold_m' :=
  repeat match goal with
  | [ |- context[m' ?Γ1 ?Γ2] ] => replace (m' Γ1 Γ2) with (mergeIdxMap Γ1 Γ2) by auto
  end.

Instance PTypingContext_IdxMap_Laws A : PTypingContext_Laws nat A (IdxMap A).
Proof.
  split.
  - unfold IdxMap.
    induction Γ1 as [ | o1 Γ1]; destruct Γ2 as [ | o2 Γ2], Γ3 as [ | o3 Γ3]; auto.
    * rewrite Bool.andb_true_r. auto.
    * repeat rewrite Bool.andb_true_r. simpl.
      destruct (mergeOption o1 o2); auto.
      destruct (mergeIdxMap Γ1 Γ2); auto.
    * unfold_m'. 
      remember (mergeIdxMap (o1 :: Γ1) (o2 :: Γ2)) as Γ eqn:HeqΓ.
      destruct Γ as [ Γ | ]; [ | auto].
      replace (is_Some (Some Γ)) with true by auto.
      rewrite Bool.andb_true_l.
      replace (Some Γ) with (return_ Γ : IdxCtx A) by auto.
      rewrite <- bind_left_unit.
      destruct (mergeIdxMap Γ1 Γ2) as [Γ' | ] eqn:HeqΓ'; 
      [ | rewrite m'_cons_step in HeqΓ; rewrite HeqΓ' in HeqΓ; inversion HeqΓ ].
      assert (IH' : is_Some (m' Γ' Γ3) = is_Some (m' Γ1 Γ3) && is_Some (m' Γ2 Γ3)).
      { specialize (IHΓ1 Γ2 Γ3).
        simpl in IHΓ1. 
        rewrite HeqΓ' in IHΓ1.
        apply IHΓ1.
      }
      destruct o1 as [a1 | ]; destruct o2 as [a2 | ]; try (inversion HeqΓ; fail);
        simpl in HeqΓ, HeqΓ'; rewrite HeqΓ' in HeqΓ; inversion HeqΓ;
        unfold_m'.
      + destruct o3; auto. 
(*        rewrite is_Some_m'_Some_None.*)
        (* WHAT IS GOING ON? CAN'T APPLY MY LEMMAS *)
        simpl in *.
        destruct (mergeIdxMap Γ' Γ3), (mergeIdxMap Γ1 Γ3), (mergeIdxMap Γ2 Γ3); 
        auto.
      + destruct o3.
        ++ simpl. rewrite Bool.andb_false_r. auto.
        ++ simpl in *.
           destruct (mergeIdxMap Γ' Γ3), (mergeIdxMap Γ1 Γ3), (mergeIdxMap Γ2 Γ3); 
           auto.
      + simpl in *.
        destruct o3; 
        destruct (mergeIdxMap Γ' Γ3), (mergeIdxMap Γ1 Γ3), (mergeIdxMap Γ2 Γ3); 
          auto.
  - intros.
    generalize dependent y. induction x, y; intros; split; intros H; simpl in *; auto; try (inversion H; fail).
    * rewrite mergeIdxMap_nil_r in H. inversion H.
    * destruct (mergeIdxMap (singleton' x a) (singleton' y b)) eqn:Hxy.
      + inversion H.
      + apply IHx in Hxy. auto.
    * inversion H. 
      destruct (IHx y) as [_ IHx'].
      subst.
      rewrite IHx'; auto.
Qed.

Instance TypingContext_IdxMap A : TypingContext_Laws nat A (IdxCtx A)  :=
  PTypingContext_to_TypingContext_Laws nat A (IdxMap A).
Hint Resolve TypingContext_IdxMap.

(* Now option IdxCtx should be a typing context *)

Section Tests.
Variable A : Type.


Lemma singleton_not_empty : forall x a, is_valid (singleton x a : IdxCtx A).
Proof.
  intros. eapply singleton_is_valid; auto.
Defined.


Example test : forall x y a b, 
    singleton x a ∙ singleton y b = singleton y b ∙ singleton x a ∙ (⊤ : IdxCtx A).
Proof.
  intros. monoid.
Defined.

Example test' : forall x y a b, x <> y ->
    singleton x a ⊎ singleton y b == singleton y b ∙ singleton x a ∙ (⊤ : IdxCtx A).
Proof.
  intros.
  solve_ctx.
Defined.

End Tests.
    
Require Import Contexts.

Definition OCtx := IdxCtx VType.

Instance Monoid_OCtx_Laws : PCM_Laws OCtx :=
  PPCM_to_PCM_Laws (IdxMap VType).
Hint Resolve Monoid_OCtx_Laws.

Lemma OCtx_Ctx : OCtx = option Ctx.
Proof. reflexivity. Qed.

(* We shouldn't need these, but we do. *)
Lemma M_unit_r : forall (A : Type) (PCM_A : PCM A), PCM_Laws A -> forall a : A,  a ∙ ⊤  = a.
Proof. intros. apply M_unit. Qed.

Lemma M_absorb_r : forall (A : Type) (PCM_A : PCM A), PCM_Laws A -> forall a : A,  a ∙ ⊥  = ⊥.
Proof. intros. apply M_absorb. Qed.

Lemma merge_wire_ind_fun : forall o1 o2 o,
    Merge_Wire o1 o2 o -> mergeOption o1 o2 = Some o.
Proof. induction 1; auto. Qed.

Lemma merge_ind_fun : forall Γ Γ1 Γ2,
    Γ == Γ1 ⋓ Γ2 ->
    Some Γ = Some Γ1 ∙ Some Γ2.
Proof.
  intros.
  induction H; subst.
  - rewrite M_unit_l. easy. auto.
  - rewrite M_unit_r. easy. auto. (* very weird that M_unit won't work... *)
  - inversion m; subst.
    + simpl in *. rewrite <- IHMerge. easy.
    + simpl in *. rewrite <- IHMerge. easy.
    + simpl in *. rewrite <- IHMerge. easy.
Qed.
 
Lemma merge_wire_fun_ind : forall o1 o2 o,
    mergeOption o1 o2 = Some o -> Merge_Wire o1 o2 o.
Proof.
  intros [w1 | ] [w2 | ] [w | ]; simpl; inversion 1; constructor.
Qed.

(* Is this true? *)
Lemma M_unit_inversion : forall {A : Type} (Γ1 Γ2 : IdxCtx A), 
  Γ1 ∙ Γ2 = ⊤  -> (Γ1 = ⊤) * (Γ2 = ⊤).
Proof.
  intros.
  destruct Γ1, Γ2.
  - destruct i, i0; auto. inversion H. 
    destruct (mergeOption o o0), (mergeIdxMap i i0); auto; inversion H1.
  - rewrite M_absorb_r in H; auto. inversion H.
  - rewrite M_absorb_l in H; auto. inversion H.
  - auto.
Qed.

Lemma merge_fun_ind : forall Γ1 Γ2 Γ,
    Some Γ = Some Γ1 ∙ Some Γ2 ->
    Γ == Γ1 ⋓ Γ2.
Proof.
  intros Γ1 Γ2 Γ.
  gen Γ1 Γ2.
  induction Γ; intros.
  - symmetry in H. apply M_unit_inversion in H as [E1 E2].
    inversion E1. inversion E2. constructor. 
  - destruct Γ1, Γ2.
    + inversion H.
    + simpl in H. inversion H; subst. constructor.
    + rewrite M_unit_r in H; auto. inversion H; subst. constructor. 
    + simpl in H.
      destruct o, o0. 
      * simpl in H; symmetry in H; inversion H.
      * simpl in H.
        destruct (mergeIdxMap Γ1 Γ2) as [Γ'|] eqn:E. 
        inversion H; subst. 
        repeat constructor.
        apply IHΓ; auto.
        inversion H.
      * simpl in H.
        destruct (mergeIdxMap Γ1 Γ2) as [Γ'|] eqn:E. 
        inversion H; subst. 
        repeat constructor.
        apply IHΓ; auto.
        inversion H.
      * simpl in H.
        destruct (mergeIdxMap Γ1 Γ2) as [Γ'|] eqn:E.
        inversion H; subst. 
        repeat constructor.
        apply IHΓ; auto.
        inversion H.
Qed.

Lemma test_octx1 : forall (Γ1 Γ2 Γ3 : OCtx), Γ1 ∙ Γ2 ∙ Γ3 = Γ3 ∙ Γ1 ∙ Γ2.
Proof. intros. monoid. Qed.

Lemma test_octx2 : forall (Γ1 Γ2 Γ3 : Ctx), 
  (Some Γ1) ∙ (Some Γ2) ∙ (Some Γ3) = (Some Γ3) ∙ (Some Γ1) ∙ (Some Γ2).
Proof. intros. monoid. Qed.