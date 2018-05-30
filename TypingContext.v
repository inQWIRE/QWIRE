Require Import Monad.
Require Import Monoid.
Require Import Coq.Classes.EquivDec.

Class TypingContext (X A Ctx : Type) :=
  { singleton : X -> A -> Ctx
  ; validity : Ctx -> bool
  }.

(* partial typing context *)
Class PTypingContext (X A PCtx : Type) :=
  { singleton' : X -> A -> PCtx }.

Definition is_Some {Z} (x : option Z) := match x with
                        | Some _ => true
                        | None => false
                        end.

Instance PTypingCtx_to_TypingCtx X A PCtx `{PTypingContext X A PCtx} 
    : TypingContext X A (option PCtx) :=
  { singleton := fun x a => Some (singleton' x a)
  ; validity := is_Some
  }.

Open Scope bool_scope.

(*
(* I think this is reinventing the wheel (aka Coq.Classes.EquivDec) but don't
   want to redo now. *)
Class DecidablePaths X := {decPaths : forall (x y : X), {x = y} + {x <> y}}.

  Definition bdec {X} `{DecidablePaths X} (x y : X) : bool :=
    if decPaths x y then true else false.
  Infix "=?" := bdec (at level 70).
  Notation "x <>? y" := (negb (x =? y)) (at level 25).

Section DecidablePaths.
  Context X `{DecidablePaths X}.

  Lemma bdec_eq : forall x y, x =? y = true <-> x = y.
  Proof.
    intros.
    unfold bdec. 
    destruct (decPaths x y) eqn:decX.
    - split; auto.
    - split; auto. intros. absurd (false = true); auto.
  Qed.

  Lemma bdec_neq : forall x y, x <>? y = true <-> x <> y.
  Proof.
    intros.
    unfold bdec.
    destruct (decPaths x y) eqn:decX.
    - split; intros; auto. inversion H0. 
    - split; auto.
  Qed.

  Lemma bdec_eq' : forall x, x =? x = true.
  Proof.
    intros x. apply bdec_eq. auto.
  Qed.

  Lemma eq_bdec_true : forall x y, x = y -> x =? y = true.
  Proof. intros. apply bdec_eq. auto. Qed.
  Lemma neq_bdec_false : forall x y, x <> y -> x =? y = false.
  Proof. intros. apply Bool.negb_true_iff.
                 apply bdec_neq. auto.
  Qed.
  Lemma eq_bdec_false : forall x y, x = y -> x <>? y = false.
  Proof.
    intros.
    apply Bool.negb_true_iff.
    rewrite Bool.negb_involutive.
    apply bdec_eq. auto.
  Qed.
  Lemma neq_bdec_true : forall x y, x <> y -> x =? y = false.
  Proof.
    intros.
    apply Bool.negb_true_iff.
    apply bdec_neq. auto.
  Qed.



End DecidablePaths.
*)

(* These must exist but rolling our own for now. *)
Section bdec.

  Context X `{EqDec X eq}.

Lemma eq_bdec_true : forall x y, x = y -> x ==b y = true.
Proof. intros; cbv. destruct (H x y); congruence. Qed.

Lemma neq_bdec_false : forall x y, x <> y -> x ==b y = false.
Proof. intros; cbv. destruct (H x y); congruence. Qed.

Lemma eq_bdec_false : forall x y, x = y -> x <>b y = false.
Proof. intros; cbv. destruct (H x y); congruence. Qed.

Lemma neq_bdec_true : forall x y, x <> y -> x <>b y = true.
Proof. intros; cbv. destruct (H x y); congruence. Qed.

End bdec.

Class TypingContext_Laws X A Ctx `{EqDec X eq} 
                                 `{PCM_Ctx : PCM_Laws Ctx} 
                                 `{TypingContext X A Ctx} :=
  { validity3 : forall Γ1 Γ2 Γ3, 
    validity (Γ1 ∙ Γ2 ∙ Γ3) =  validity (Γ1 ∙ Γ2) 
                            && validity (Γ1 ∙ Γ3) 
                            && validity (Γ2 ∙ Γ3)
  ; validity_reflection : forall Γ, validity Γ = false <-> Γ = ⊥
  ; validity_singleton : forall x a, validity (singleton x a) = true
  ; validity_top : validity ⊤ = true
  ; validity_singleton_merge : forall x y a b, 
    validity (singleton x a ∙ singleton y b) = (x <>b y)
  }. 

Class PTypingContext_Laws X A Ctx `{EqDec X eq}
                                  `{PPCM_Ctx : PPCM_Laws Ctx}
                                  `{PTypingContext X A Ctx} :=
  { pvalidity3 : forall Γ1 Γ2 Γ3,
        is_Some (do Γ ← m' Γ1 Γ2; m' Γ Γ3)
      = is_Some (m' Γ1 Γ2) && is_Some (m' Γ1 Γ3) && is_Some (m' Γ2 Γ3)
  ; validity_singleton_merge' : forall x y a b,
    m' (singleton' x a) (singleton' y b) = None <-> x = y
  }.

Instance PTypingContext_to_TypingContext_Laws X A Ctx `{PTypingContext_Laws X A Ctx}
                                            : TypingContext_Laws X A (option Ctx).
Proof.
  split.
  - destruct Γ1 as [Γ1 | ], Γ2 as [Γ2 | ], Γ3 as [Γ3 | ]; auto.
    * apply pvalidity3.
    * assert (merge_None : forall z, validity (Some z ∙ None) = false) by auto.
      rewrite merge_None.
      rewrite Bool.andb_false_r.
      simpl. destruct (m' Γ1 Γ2); auto.
  - destruct Γ; auto.
    * simpl. split; inversion 1.
    * simpl. split; auto.
  - intros; simpl; auto.
  - simpl; auto.
  - intros. simpl. unfold nequiv_decb.
    destruct (equiv_dec x y) as [e | ne]; auto.
    * cbv in e. subst.
      unfold is_Some.
      destruct (validity_singleton_merge' y y a b) as [_ N].
      rewrite N by easy.
      rewrite eq_bdec_true; easy.
    * destruct (m' (singleton' x a) (singleton' y b)) as [ | z] eqn:eq'; auto.
      rewrite neq_bdec_false; easy.
      apply (validity_singleton_merge') in eq'. contradiction.
Qed.

Section TypingContexts.

Context X A Ctx `{TypingContext_Laws X A Ctx}.

Definition is_valid Γ := (validity Γ = true). 

Lemma is_valid3 : forall Γ1 Γ2 Γ3, 
    is_valid (Γ1 ∙ Γ2 ∙ Γ3) <->  is_valid (Γ1 ∙ Γ2) 
                                 /\ is_valid (Γ1 ∙ Γ3) 
                                 /\ is_valid (Γ2 ∙ Γ3).
Proof.
  unfold is_valid. intros.
  rewrite validity3. split; [intros eq | intros [eq1 [eq2 eq3] ] ].
  - destruct (validity (Γ1 ∙ Γ2)), (validity (Γ1 ∙ Γ3)), (validity (Γ2 ∙ Γ3)); auto.
  - rewrite eq1, eq2, eq3. auto.
Defined.

Lemma is_valid3_forward : forall Γ1 Γ2 Γ3,
      is_valid (Γ1 ∙ Γ2) ->
      is_valid (Γ1 ∙ Γ3) ->
      is_valid (Γ2 ∙ Γ3) ->
      is_valid (Γ1 ∙ Γ2 ∙ Γ3).
Proof. intros. apply is_valid3. auto. Qed.

Definition validity_reflection_true : forall Γ, validity Γ = true <-> Γ <> ⊥.
Proof.
  intros Γ. split; intros.
  - intros eq0. apply validity_reflection in eq0. rewrite eq0 in *. 
    absurd (false = true); auto.
  - destruct (validity Γ) eqn:v_Γ; auto.
    apply validity_reflection in v_Γ. contradiction.
Qed.
Lemma singleton_is_valid : forall x a, is_valid (singleton x a). 
Proof.
  apply validity_singleton.
Defined.

Lemma top_is_valid : is_valid ⊤.
Proof.
  apply validity_top.
Defined.
Lemma top_not_bottom : ⊤ <> ⊥.
Proof. apply validity_reflection_true. apply validity_top. Qed.

Lemma singleton_merge_is_valid : forall x y a b, 
    is_valid (singleton x a ∙ singleton y b) <-> (x <> y).
Proof.
  intros. unfold is_valid.
  rewrite validity_singleton_merge.
  split; cbv; destruct (H x y); congruence. 
Qed.

Lemma singleton_merge_invalid : forall x a b,
    ~ is_valid (singleton x a ∙ singleton x b).
Proof.
  intros. unfold is_valid.
  rewrite validity_singleton_merge. 
  cbv; destruct (H x x); congruence.
Qed.

End TypingContexts.
About is_valid.
Arguments is_valid {X A Ctx TypingContext} : rename.


(***************************************************)
(* Tactics to solve goals of the form "is_valid Γ" *)
(***************************************************)

(* This is the naive tactic, but instead of working top down, we want to be a little smarter by working bottom up *)
Ltac validate_dumb :=
  repeat rewrite M_unit; repeat rewrite M_unit_l;
  repeat match goal with
  | [ H : is_valid ?Γ |- is_valid ?Γ ]              => exact H
  | [ |- is_valid ⊤ ]                               => apply top_is_valid
  | [ |- is_valid (singleton _ _) ]                 => eapply singleton_is_valid; auto
  | [ |- is_valid (singleton _ _ ∙ singleton _ _) ] => eapply singleton_merge_is_valid; auto
  | [ |- is_valid (_ ∙ _ ∙ _) ]                     => eapply is_valid3; auto
  | [ |- _ /\ _]                                    => split
  end.

Ltac introduce_valid_singletons :=
  repeat match goal with
  | [ |- context[singleton ?x ?a] ] => 
    assert (is_valid (singleton x a)) 
    by apply (@singleton_is_valid _ _ _ _ _ _ _ _);
    let Γ := fresh "Γ" in
    remember (singleton x a) as Γ (* so that we don't match this x again *)
  end; subst.

Ltac introduce_valid_term Γ :=
  match Γ with
  | _               => match goal with
                       [ H : is_valid Γ |- _ ] => idtac
                       end
  | ?Γ1 ∙ ?Γ2 ∙ ?Γ3 => let Γ12 := constr:(Γ1 ∙ Γ2) in
                       let Γ13 := constr:(Γ1 ∙ Γ3) in
                       let Γ23 := constr:(Γ2 ∙ Γ3) in
                       introduce_valid_term Γ12;
                       introduce_valid_term Γ13;
                       introduce_valid_term Γ23;
                       assert (is_valid Γ) by validate_dumb;
                       let Γ' := fresh "Γ" in
                       remember Γ as Γ'
  | _               => assert (is_valid Γ) by validate_dumb;
                       let Γ' := fresh "Γ" in
                       remember Γ as Γ'
  end; subst.

(*
Ltac validate :=
  repeat rewrite M_assoc;
  match goal with
  | [ |- is_valid ?Γ ] => introduce_valid_term Γ
  end; auto.
*)

(* This new tactic uses rewriting *)

Ltac eq_to_beq :=
  repeat match goal with
  | [H : ?x = ?y |- context[?x ==b ?y] ] => 
    rewrite (eq_bdec_true _ x y H)
  | [H : ?x = ?y |- context[?y ==b ?x] ] => 
    rewrite (eq_bdec_true _ y x (eq_sym H))
  | [H : ?x = ?y |- context[?x <>b ?y] ] => 
    rewrite (eq_bdec_false _ x y H)
  | [H : ?x = ?y |- context[?y <>b ?x] ] =>
    rewrite (eq_bdec_false _ y x (eq_sym H))
  | [H : ?x <> ?y |- context[?x <>b ?y] ] =>
    rewrite (neq_bdec_true _ x y H)
  | [H : ?x <> ?y |- context[?y <>b ?x] ] =>
    rewrite (neq_bdec_true _ y x (not_eq_sym H))
  | [ H : ?x <> ?y |- context[?x ==b ?y] ] =>
    rewrite (neq_bdec_false _ x y H)
  | [ H : ?x <> ?y |- context[?y ==b ?x] ] =>
    rewrite (neq_bdec_false _ y x (not_eq_sym H))
  end.


Ltac validate :=
  intros;
  unfold is_valid in *;
  repeat rewrite M_assoc;
  repeat rewrite M_unit;
  repeat rewrite validity3;
  repeat rewrite validity_top;
  repeat rewrite validity_singleton;
  repeat rewrite validity_singleton_merge;
  eq_to_beq; auto.

Section Tests.

Context X A Ctx `{TypingContext_Laws X A Ctx}.

Lemma test3 : forall x y z a b c, x <> y -> y <> z -> x <> z ->
             is_valid (singleton x a ∙ singleton y b ∙ singleton z c).
Proof.
  validate.
Qed.


Lemma test4 : forall x y z w a b c d, x <> y -> y <> z -> x <> z -> x <> w -> y <> w -> z <> w ->
             is_valid (singleton x a ∙ singleton y b ∙ singleton z c ∙ singleton w d).
Proof.
  validate. 
Qed.

End Tests.


(* In the end, solve goals of this form *)
(* The unicode symbol is \uplus *)
Notation "Γ1 ⊎ Γ2 == Γ" := (Γ = Γ1 ∙ Γ2 /\ is_valid Γ) (at level 75).

Ltac solve_ctx := 
  repeat match goal with
  | [ |- _ /\ _ ] => split
  | [ |- is_valid ?Γ ] => validate
  | [ |- _ = _ ] => monoid
  end.

