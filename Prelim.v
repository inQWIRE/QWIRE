Require Export Bool.
Require Export Arith.
Require Export Psatz.
Require Export Program.
Require Export List.

Export ListNotations.

(* Boolean notations, lemmas *)

Notation "¬ b" := (negb b) (at level 10).
Infix  "⊕" := xorb (at level 20).

Search xorb andb.

Lemma xorb_nb_b : forall b, ¬ b ⊕ b = true. Proof. destruct b; easy. Qed.
Lemma xorb_b_nb : forall b, b ⊕ ¬ b = true. Proof. destruct b; easy. Qed.

Lemma xorb_involutive_l : forall b b', b ⊕ (b ⊕ b') = b'. Proof. destruct b, b'; easy. Qed.
Lemma xorb_involutive_r : forall b b', b ⊕ b' ⊕ b' = b. Proof. destruct b, b'; easy. Qed.

Lemma andb_xorb_dist : forall b b1 b2, b && (b1 ⊕ b2) = (b && b1) ⊕ (b && b2).
Proof. destruct b, b1, b2; easy. Qed.

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

Ltac bdestructΩ X := bdestruct X; simpl; try lia.


(* Distribute functions over lists *)

Lemma if_dist : forall (A B : Type) (b : bool) (f : A -> B) (x y : A), f (if b then x else y) = if b then f x else f y.
Proof. destruct b; reflexivity. Qed.

Lemma if_dist2 : forall (A B C : Type) (b : bool) (f : A -> B -> C) (x y : A) (z : B), f (if b then x else y) z = if b then f x z else f y z.
Proof. destruct b; reflexivity. Qed.

(* f_equals in the other direction *)

Lemma f_equal_inv : forall {A B} (x : A) (f g : A -> B), f = g -> f x = g x.
Proof. intros. rewrite H. easy. Qed.

Lemma f_equal2_inv : forall {A B C} x y (f g : A -> B -> C), f = g -> f x y = g x y.
Proof. intros. rewrite H. easy. Qed.

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

Lemma update_length : forall A (l: list A) (a : A) (n : nat), 
    length (update_at l n a) = length l.
Proof.
  induction l; auto. 
  simpl.
  destruct n.
  easy.
  simpl.
  rewrite IHl; easy.
Qed.

Fixpoint Injective {A} (ls : list A) :=
  match ls with
  | [] => True
  | x :: ls' => ~ In x ls' /\ Injective ls'
  end.
  
Lemma nth_nil : forall {A} x, ([] : list A) !! x = None.
Proof.
  destruct x; auto.
Qed.

Lemma repeat_combine : forall A n1 n2 (a : A), 
  List.repeat a n1 ++ List.repeat a n2 = List.repeat a (n1 + n2).
Proof.
  induction n1; trivial. 
  intros. simpl. 
  rewrite IHn1.
  reflexivity.
Qed.

Lemma rev_repeat : forall A (a : A) n, rev (repeat a n) = repeat a n.
Proof.
  induction n; simpl; trivial.
  rewrite IHn.
  rewrite (repeat_combine A n 1).
  rewrite Nat.add_1_r.
  reflexivity.
Qed.

Lemma firstn_repeat_le : forall A (a : A) m n, (m <= n)%nat -> firstn m (repeat a n) = repeat a m.  
Proof.
  induction m; trivial.
  intros n L.
  destruct n; [inversion L|].  
  simpl.
  rewrite IHm by lia. 
  reflexivity.
Qed.

Lemma firstn_repeat_ge : forall A (a : A) m n, (m >= n)%nat -> firstn m (repeat a n) = repeat a n.  
Proof.
  intros A a m n H.
  generalize dependent m.
  induction n; intros m L; simpl.
  - apply firstn_nil.
  - destruct m; [inversion L|].
    simpl.
    rewrite IHn by lia.
    reflexivity.
Qed.

Lemma firstn_repeat : forall A (a : A) m n, firstn m (repeat a n) = repeat a (min m n).  
Proof.
  intros.
  bdestruct (m <=? n).
  - rewrite firstn_repeat_le, Min.min_l; easy.
  - rewrite firstn_repeat_ge, Min.min_r; trivial; lia.
Qed.

Lemma skipn_repeat : forall A (a : A) m n, skipn m (repeat a n) = repeat a (n-m).
Proof.  
  induction m; intros n; simpl.
  - rewrite Nat.sub_0_r. reflexivity.
  - destruct n; trivial.
    simpl.
    apply IHm.
Qed.

Lemma skipn_length : forall {A} (l : list A) n, length (skipn n l) = (length l - n)%nat. 
Proof.
  Transparent skipn.
  intros A l.
  induction l.
  intros [|n]; easy.
  intros [|n].
  easy.
  simpl.
  rewrite IHl.
  easy.
  Opaque skipn.
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

(************************************)
(* Helpful, general purpose tactics *)
(************************************)

Ltac simpl_rewrite lem :=
  let H := fresh "H" in 
  specialize lem as H; simpl in H; rewrite H; clear H.

Ltac simpl_rewrite' lem := 
  let H := fresh "H" in
  specialize lem as H; simpl in H; rewrite <- H; clear H.

Ltac simpl_rewrite_h lem hyp := 
  let H := fresh "H" in
  specialize lem as H; simpl in H; rewrite <- H in hyp; clear H.

Ltac apply_with_obligations H :=
  match goal with
  | [|- ?P ?a]    => match type of H with ?P ?a' => 
    replace a with a'; [apply H|]; trivial end
  | [|- ?P ?a ?b] => match type of H with ?P ?a' ?b' => 
    replace a with a'; [replace b with b'; [apply H|]|]; trivial end
  | [|- ?P ?a ?b ?c ] => match type of H with ?P ?a' ?b' ?c' => 
    replace a with a'; [replace b with b'; [replace c with c'; [apply H|]|]|]; trivial end
  | [|- ?P ?a ?b ?c ?d] => match type of H with ?P ?a' ?b' ?c' ?d' => 
    replace a with a'; [replace b with b'; [replace c with c'; [replace d with d'; [apply H|]|]|]|]; trivial end
  | [|- ?P ?a ?b ?c ?d ?e] => match type of H with ?P ?a' ?b' ?c' ?d' ?e' => 
    replace a with a'; [replace b with b'; [replace c with c'; [replace d with d'; [replace e with e'; [apply H|]|]|]|]|]; 
    trivial end 
  | [|- ?P ?a ?b ?c ?d ?e ?f] => match type of H with ?P ?a' ?b' ?c' ?d' ?e' ?f' => 
    replace a with a'; [replace b with b'; [replace c with c'; [replace d with d'; [replace e with e'; [replace f with f'; 
    [apply H|]|]|]|]|]|]; trivial end 
  | [|- ?P ?a ?b ?c ?d ?e ?f ?g] => match type of H with ?P ?a' ?b' ?c' ?d' ?e' ?f' ?g' => 
    replace a with a'; [replace b with b'; [replace c with c'; [replace d with d'; [replace e with e'; [replace f with f'; 
    [replace g with g'; [apply H|]|]|]|]|]|]|]; trivial end 
  end.


(* From SF - up to five arguments *)
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

Lemma double_mult : forall (n : nat), (n + n = 2 * n)%nat. Proof. intros. lia. Qed.
Lemma pow_two_succ_l : forall x, (2^x * 2 = 2 ^ (x + 1))%nat.
Proof. intros. rewrite mult_comm. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma pow_two_succ_r : forall x, (2 * 2^x = 2 ^ (x + 1))%nat.
Proof. intros. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma double_pow : forall (n : nat), (2^n + 2^n = 2^(n+1))%nat. 
Proof. intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity. Qed.
Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> (a^m = b^n)%nat.
Proof. intuition. Qed.
Lemma pow_positive : forall a b, a <> 0 -> 0 < a ^ b.
Proof. intros. induction b; simpl; try lia. apply Nat.lt_0_mul'. split; lia. Qed.  

Ltac unify_pows_two :=
  repeat match goal with
  (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
  | [ |- context[ 4%nat ]]                  => replace 4%nat with (2^2)%nat by reflexivity
  | [ |- context[ (0 + ?a)%nat]]            => rewrite plus_0_l 
  | [ |- context[ (?a + 0)%nat]]            => rewrite plus_0_r 
  | [ |- context[ (1 * ?a)%nat]]            => rewrite Nat.mul_1_l 
  | [ |- context[ (?a * 1)%nat]]            => rewrite Nat.mul_1_r 
  | [ |- context[ (2 * 2^?x)%nat]]          => rewrite <- Nat.pow_succ_r'
  | [ |- context[ (2^?x * 2)%nat]]          => rewrite pow_two_succ_l
  | [ |- context[ (2^?x + 2^?x)%nat]]       => rewrite double_pow 
  | [ |- context[ (2^?x * 2^?y)%nat]]       => rewrite <- Nat.pow_add_r 
  | [ |- context[ (?a + (?b + ?c))%nat ]]   => rewrite plus_assoc 
  | [ |- (2^?x = 2^?y)%nat ]                => apply pow_components; try lia 
  end.
