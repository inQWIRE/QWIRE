Require Export Bool.
Require Export Arith.
Require Export Reals.
Require Export Psatz.
Require Export Omega.
Require Export Program.
Require Export List.
Require Export Psatz.
Require Import Monad. 

Export ListNotations.

(* Boolean notations, lemmas *)

Notation "¬ b" := (negb b) (at level 10).
Infix  "⊕" := xorb (at level 20).

Lemma xorb_nb_b : forall b, ¬ b ⊕ b = true. Proof. destruct b; easy. Qed.
Lemma xorb_b_nb : forall b, b ⊕ ¬ b = true. Proof. destruct b; easy. Qed.


(* A bit of useful reflection from Software Foundations Vol 3 *)

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.  apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].


(* Currying *)

Definition curry {A B C : Type} (f : A * B -> C) : (A -> B -> C) :=
  fun x y => f (x,y).
Definition uncurry {A B C : Type} (f : A -> B -> C) : (A * B -> C) :=
  fun p => f (fst p) (snd p).

(* Lists *)


(* Precondition: x must appear in li *)
Fixpoint lookup (x : nat) (li : list nat) : nat :=
  match li with
  | nil => 0
  | y :: ys => if x =? y then 0 else S (lookup x ys)
  end.

(*
Fixpoint index {A} (i : nat) (li : list A) : option A :=
  match i, li with
  | _, nil => None
  | 0, x :: _ => Some x
  | S i', _ :: li' => index i' li'
  end.
*)
Notation "l !! i" := (nth_error l i) (at level 20).

Fixpoint remove_at {A} (i : nat) (ls : list A) :=
  match i, ls with
  | _   ,[]        => []
  | 0   , _ :: ls' => ls'
  | S i', a :: ls' => a :: remove_at i' ls'
  end.

Fixpoint update_at {A} (ls : list A) (i : nat) (a : A) : list A :=
  match ls, i with
  | []      , _    => []
  | _ :: ls', 0    => a :: ls'
  | b :: ls', S i' => b :: update_at ls' i' a
  end.



Fixpoint Injective {A} (ls : list A) :=
  match ls with
  | [] => True
  | x :: ls' => ~ In x ls' /\ Injective ls'
  end.
  
Lemma nth_nil : forall {A} x, ([] : list A) !! x = None.
Proof.
  destruct x; auto.
Qed.

(* option type *)


Definition maybe {A} (o : option A) (default : A) : A :=
  match o with
  | Some a => a
  | None => default
  end.


(* Why are we defining this from scratch??? *)
Fixpoint inb (a : nat) (ls : list nat) : bool :=
  match ls with
  | [] => false
  | b :: ls' => (b =? a) || inb a ls'
  end%bool.

Fixpoint subset (ls1 ls2 : list nat) : bool :=
  match ls1 with
  | [] => true
  | a :: ls1' => inb a ls2 && subset ls1' ls2
  end.
Notation "ls1 ⊆ ls2" := (subset ls1 ls2 = true) (at level 30).

Fixpoint disjoint (ls1 ls2 : list nat) : bool :=
  match ls1 with
  | [] => true
  | a :: ls1' => (negb (inb a ls2)) && disjoint ls1' ls2
  end.
Notation "ls1 ⊥ ls2" := (disjoint ls1 ls2 = true) (at level 30).

Lemma disjoint_nil_l : forall ls, nil ⊥ ls. Proof. reflexivity. Qed.
Lemma disjoint_nil_r : forall ls, ls ⊥ nil. Proof. induction ls; trivial. Qed.

(*
Lemma disjoint_cons : forall a ls1 ls2, (negb (inb a ls1)) = true ->
                                   ls1 ⊥ ls2 ->
                                   ls1 ⊥ (a :: ls2).
Proof.
  intros a ls1 ls2 H H0.
  induction ls1.
  apply disjoint_nil_l.
  simpl in *.
  Search ((_ =? _) = (_ =? _)).
  rewrite Nat.eqb_sym.
  destruct (a0 =? a). simpl in *. inversion H.
  destruct (inb a0 ls2). simpl in *. inversion H0.
  simpl in *.
  apply IHls1; assumption.
Qed.  
*)

Lemma disjoint_cons : forall a ls1 ls2, 
    ((negb (inb a ls1)) && disjoint ls1 ls2 = disjoint ls1 (a :: ls2))%bool.
Proof.
  intros a ls1 ls2.
  induction ls1. reflexivity.
  simpl.
  rewrite <- IHls1.
  rewrite Nat.eqb_sym.
  destruct (a =? a0), (inb a ls1), (inb a0 ls2); auto.
Qed.  

Lemma disjoint_symm : forall ls1 ls2, disjoint ls1 ls2 = disjoint ls2 ls1.
Proof. intros. 
       induction ls1.
       - simpl.
         symmetry.
         apply disjoint_nil_r.
       - simpl.
         rewrite <- disjoint_cons.
         rewrite IHls1.
         reflexivity.
Qed.         
         

Lemma eqb_neq : forall x y, x <> y -> x =? y = false.
Proof.
  induction x as [ | x]; destruct y as [ | y]; intros H; auto.
  - contradiction.
  - simpl.
    apply IHx.
    intros H'.
    subst.
    contradiction.
Qed.

Lemma lookup_app : forall x ls1 ls2,
      lookup x (ls1 ++ ls2) = if inb x ls1 then lookup x ls1 
                                           else (lookup x ls2 + length ls1)%nat.
Proof.
  induction ls1; intros; simpl; auto. 
  destruct (Nat.eq_dec x a) as [H_x_a | H_x_a].
  * subst.
    rewrite Nat.eqb_refl.
    reflexivity.
  * repeat rewrite eqb_neq; auto. simpl.
    rewrite IHls1.
    destruct (inb x ls1); auto.
Qed.

Lemma subset_app : forall ls1 ls2 ls, (ls1 ++ ls2) ⊆ ls -> ls1 ⊆ ls /\ ls2 ⊆ ls.
Proof.
  induction ls1; intros ls2 ls H; simpl in *; split; auto.
  - apply Bool.andb_true_iff in H.
    destruct H as [H_a_ls H].
    rewrite H_a_ls; simpl.
    apply IHls1 in H.
    destruct H; auto.
  - apply Bool.andb_true_iff in H.
    destruct H as [H_a_ls H].
    apply IHls1 in H.
    destruct H; auto.
Qed.

Lemma seq_app : forall offset1 offset2 start,
      seq start offset1 ++ seq (start + offset1) offset2 
    = seq start (offset1 + offset2).
Proof.
  induction offset1; intros; simpl; auto.
  rewrite Nat.add_succ_r.
  rewrite <- Nat.add_succ_l.
  rewrite IHoffset1.
  reflexivity.
Qed.


Lemma inb_fmap_S : forall ls x,
      inb (S x) (fmap S ls) = inb x ls.
Proof.
  induction ls; intros; simpl in *; auto.
  simpl.
  rewrite IHls.
  reflexivity.
Qed.

(************************************)
(* Helpful, general purpose tactics *)
(************************************)

Ltac simpl_rewrite lem :=
  let H := fresh "H" in 
  specialize lem as H; simpl in H; rewrite H; clear H.

(* From SF *)
Tactic Notation "gen" ident(X1) :=
  generalize dependent X1.
Tactic Notation "gen" ident(X1) ident(X2) :=
  gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) :=
  gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) :=
  gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) :=
  gen X5; gen X4; gen X3; gen X2; gen X1.


(***************)
(* Powers of 2 *)
(***************)

Lemma double_mult : forall (n : nat), (n + n = 2 * n)%nat. Proof. intros. omega. Qed.
Lemma pow_two_succ_l : forall x, (2^x * 2 = 2 ^ (x + 1))%nat.
Proof. intros. rewrite mult_comm. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma pow_two_succ_r : forall x, (2 * 2^x = 2 ^ (x + 1))%nat.
Proof. intros. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma double_pow : forall (n : nat), (2^n + 2^n = 2^(n+1))%nat. 
Proof. intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity. Qed.
Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> (a^m = b^n)%nat.
Proof. intuition. Qed.

Ltac unify_pows_two :=
  repeat match goal with
  (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
  | [ |- context[ 4%nat ]]                  => replace 4%nat with (2^2)%nat by reflexivity
  | [ |- context[ (0 + ?a)%nat]]            => rewrite plus_0_l 
  | [ |- context[ (?a + 0)%nat]]            => rewrite plus_0_r 
  | [ |- context[ (2 * 2^?x)%nat]]          => rewrite <- Nat.pow_succ_r'
  | [ |- context[ (2^?x * 2)%nat]]          => rewrite pow_two_succ_l
  | [ |- context[ (2^?x + 2^?x)%nat]]       => rewrite double_pow 
  | [ |- context[ (2^?x * 2^?y)%nat]]       => rewrite <- Nat.pow_add_r 
  | [ |- context[ (?a + (?b + ?c))%nat ]]   => rewrite plus_assoc 
  | [ |- (2^?x = 2^?y)%nat ]                => apply pow_components; try omega 
  end.
