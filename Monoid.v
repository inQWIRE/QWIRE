Require Import Monad.
Require Import PermutSetoid.
Require Import Sorting.Permutation.
Require Import Sorting.PermutEq. (* Standard library *)  

(* A partial commutative monoid is a monoid (1,m) with an undefined element 0. *)
Class PCM A :=
    { one  : A
    ; zero : A
    ; m    : A -> A -> A }.

Notation "⊥" := zero : monoid_scope.
Notation "⊤" := one : monoid_scope.
Notation "a ∙ b" := (m a b) (left associativity, at level 50) : monoid_scope.

Open Scope monoid_scope.

Class PCM_Laws A `{PCM A} :=
  { M_unit  : forall a, a ∙ ⊤ = a
  ; M_assoc : forall a b c, a ∙ (b ∙ c) = (a ∙ b) ∙ c
  ; M_comm  : forall a b, a ∙ b = b ∙ a
  ; M_absorb : forall a, a ∙ ⊥ = ⊥ 
  }.

Hint Resolve M_unit M_assoc M_comm M_absorb.

(****************************)
(* Interpretable type class *)
(****************************)

Class Translate (A B : Type) := { translate : A -> B }.
Notation "⟨ b ⟩" := (translate b) : monoid_scope.

(**********************************)
(* Lift a partial monoid to a PCM *)
(**********************************)

Class PPCM A :=
  { one' : A 
  ; m' : A -> A -> option A }.
Class PPCM_Laws A `{PPCM A} :=
  { PMonoid_unit : forall a, m' a one' = Some a ;
    PMonoid_assoc : forall a b c, (do x ← m' b c; m' a x) = (do x ← m' a b; m' x c) ;
    PMonoid_comm : forall a b, m' a b = m' b a 
  }.

Instance PPCM_to_PCM A `{PPCM A} : PCM (option A) :=
  { one := Some one'
  ; zero := None
  ; m := fun a b => do x ← a;
                    do y ← b;
                    m' x y
  }.
Instance PPCM_to_PCM_Laws A `{PPCM_Laws A} : PCM_Laws (option A).
Proof.
  split.
  - destruct a; simpl; auto. apply PMonoid_unit.
  - destruct a as [a | ], b as [b | ], c as [c | ]; simpl; auto. 
    * apply PMonoid_assoc. 
    * destruct (m' a b); auto.
  - destruct a as [a | ], b as [b | ]; simpl; auto.
    apply PMonoid_comm.
  - destruct a; simpl; auto.
Qed.

(*******************)
(* CMonoid Section *)
(*******************)

Section CMonoid.
  Variable A : Type.
  Variable PCM_A : `{PCM A}.
  Variable PCM_Laws_A : `{PCM_Laws A}.

  (**************************************)
  (* Basic consequences of CMonoid Laws *)
  (**************************************)

  Lemma M_unit_l : forall a, ⊤ ∙ a = a.
  Proof. intros. rewrite M_comm. auto. Defined.
  Hint Resolve M_unit_l.


  Lemma M_comm_assoc : forall a b c, a ∙ b ∙ c = b ∙ a ∙ c.
  Proof.
    intros. rewrite (M_comm a b). reflexivity.
  Defined.

  Lemma M_comm_assoc_r : forall a b c, a ∙ (b ∙ c) = b ∙ (a ∙ c).
  Proof.
    intros. rewrite M_assoc. rewrite (M_comm a b). rewrite <- M_assoc.
    reflexivity.
  Defined.

  Lemma M_absorb_l : forall a, ⊥ ∙ a = ⊥.
  Proof. intros. rewrite M_comm. auto. Defined.
  Hint Resolve M_absorb_l.

  (****************************)
  (* ToA type class *)
  (****************************)

  Open Scope list_scope.


  Global Instance TranslateA : Translate A A := {translate := fun x => x}.

  Definition translate_option {X} `{Translate X A} (x : option X) : A :=
    match x with
    | Some x' => ⟨x'⟩
    | None    => ⊥
    end.
  Global Instance Translate_option (X : Type) `{Translate X A} : Translate (option X) A :=
    { translate := translate_option }.

  Lemma translate_Some : forall {X} `{Translate X A} (x : A), 
        ⟨Some x⟩ = ⟨x⟩.
  Proof.
    auto.
  Defined.

  Fixpoint translate_list {X} `{Translate X A} (ls : list X) : A :=
    match ls with
    | nil => ⊤
    | b :: ls' => ⟨b⟩ ∙ translate_list ls'
    end.
  Global Instance Translate_list (X : Type) `{Translate X A} : Translate (list X) A :=
    { translate := translate_list }.


  (******************************************************)
  (* Structural representation of an commutative monoid *)
  (******************************************************)

  Inductive M_exp :=
  | M_zero : M_exp
  | M_one  : M_exp
  | M_var  : A -> M_exp
  | M_m    : M_exp -> M_exp -> M_exp.

  Fixpoint translate_M_exp (e : M_exp) : A :=
    match e with
    | M_zero => ⊥
    | M_one => ⊤
    | M_var a => a
    | M_m e1 e2 => translate_M_exp e1 ∙ translate_M_exp e2
    end.
  Global Instance Translate_M_exp : Translate M_exp A := {translate := translate_M_exp}.


  (****************)
  (* lists of A's *)
  (****************)

  Fixpoint flatten (e : M_exp) : option (list A) :=
    match e with
    | M_zero => None
    | M_one  => Some nil
    | M_var a => Some (a :: nil)
    | M_m e1 e2 => do ls1 ← flatten e1;
                   do ls2 ← flatten e2;
                   return_ (ls1 ++ ls2)
    end.

  Lemma flatten_correct' : forall (ls1 ls2 : list A),
      ⟨ls1⟩ ∙ ⟨ls2⟩ = ⟨ls1 ++ ls2⟩.
  Proof.
    induction ls1; intros; auto.
    simpl.
    rewrite <- M_assoc. unfold translate_list in *; simpl in *.
    rewrite IHls1. reflexivity.
  Defined.

  Lemma option_list_correct : forall (o1 o2 : option (list A)),
    ⟨o1⟩ ∙ ⟨o2⟩ = ⟨ do ls1 ← o1;
                         do ls2 ← o2;
                         return_ (ls1 ++ ls2) ⟩.
  Proof.
    destruct o1; destruct o2; simpl; auto.
    apply flatten_correct'.
  Defined.

  Lemma flatten_correct : forall e, ⟨e⟩ = ⟨flatten e⟩.
  Proof.
    intros. unfold translate; simpl.
    induction e; simpl; try rewrite M_unit; auto. 
    rewrite IHe1, IHe2.
    apply option_list_correct.
  Defined.


  (*****************)
  (* lists of nats *)
  (*****************)


  (* Instead of working with list A directly, we instead want to work with
   a pair of a list A and a list nat-- the elements in the second list
   index into the first list, and let us compare elements.
   *)

  Fixpoint index (xs : list A) (i : nat) : A :=
    match xs, i with
    | nil, _ => ⊥
    | (x :: _), 0 => x
    | (_ :: xs), S x => index xs x
    end.

  Fixpoint index_wrt (values : list A) (indices : list nat) : list A :=
(*    fmap (index values) indices.*) (* for some reason, fmap is not simplifying appropriately? *)
    match indices with
    | nil => nil
    | i :: indices' => index values i :: index_wrt values indices'
    end.

  Instance Translate_nat_list : Translate (list A * list nat) A :=
    { translate := fun x => match x with
                            | (values, idx) => ⟨index_wrt values idx⟩
                            end }.

  (* Default list_nat representation of a value *)

  (* nats_lt n produces a list of nats [0..n-1] *)
  Fixpoint nats_lt n : list nat :=
    match n with
    | O => nil
    | S n' => O :: fmap S (nats_lt n')
    end.
  Require Import List.

  Lemma index_wrt_cons : forall idx a values,
      index_wrt (a :: values) (fmap S idx) = index_wrt values idx.
  Proof. 
    induction idx as [ | n]; intros a values; simpl; auto.
    rewrite IHidx; auto.
  Defined.

  Lemma index_wrt_default : forall (ls : list A),
      index_wrt ls (nats_lt (length ls)) = ls.
  Proof.
    induction ls; simpl; auto. 
    rewrite index_wrt_cons.
    rewrite IHls. 
    reflexivity.
  Defined.

  
(*
  Fixpoint translate_list_option {X} `{Translate X A} (ls : list (option A)) : A :=
    match ls with
    | nil => Some ⊤
    | Some a :: ls' => fmap (m a) (translate_list_option ls')
    | None :: _ => None
    end.
  Instance Translate_list_option : Translate (option A) (list (option A)) :=
    { translate := translate_list_option }.
*)

  Lemma split_list : forall values ls1 ls2,
      ⟨index_wrt values (ls1 ++ ls2)⟩ = ⟨index_wrt values ls1⟩ ∙ ⟨index_wrt values ls2⟩.
  Proof.
    induction ls1; simpl; intros; auto. simpl in *.
    rewrite IHls1. auto. 
  Qed.  


(*
  Lemma in_interp_nat : forall i a values idx,
      In i idx ->
      index values i = Some a ->
      In a (index_wrt values idx).
  Proof.
    induction idx as [ | j idx]; intros pf_in pf_a; simpl in *.
    - contradiction.
    - destruct pf_in as [eq | pf_in].
      * subst. rewrite pf_a. left; auto.
      * right. apply IHidx; auto.
  Defined.
*)


  Lemma in_index : forall i a values,
      ⟨index values i⟩ = a -> a = ⊥ \/ In a values.
  Proof.
    induction i; destruct values; intros; auto.
    - simpl in H. right. left. auto.
    - simpl in H. 
      destruct (IHi _ _ H); auto.
      right. right. auto.
  Defined.

  Lemma in_index_wrt : forall a idx values,
      In a (index_wrt values idx) ->
      a = ⊥ \/ In a values. 
  Proof.
    induction idx as [ | i]; intros values pf_in; simpl in *.
    - contradiction.
    - destruct pf_in as [pf_in | pf_in].
      * (* index values i = a implies In a values? not if a = 0... *)
        apply (in_index i); auto.
      * apply IHidx; auto.
  Defined.

  (****************)
  (* Permutations *)
  (****************)

  Lemma interp_permutation : forall (values : list A) (idx1 idx2 : list nat),
      Permutation idx1 idx2 -> 
      ⟨index_wrt values idx1⟩ = ⟨index_wrt values idx2⟩.
  Proof.
    intros values idx1 idx2 pf.
    induction pf; simpl in *; auto.
    - rewrite IHpf; auto.
    - rewrite M_comm_assoc_r. reflexivity.
    - rewrite IHpf1, IHpf2. reflexivity.
  Defined.

  Lemma permutation_reflection : forall ls1 ls2,
      @permutation nat _ PeanoNat.Nat.eq_dec ls1 ls2 -> Permutation ls1 ls2.
  Proof.
    intros. apply (permutation_Permutation PeanoNat.Nat.eq_dec); auto.
  Defined.

  Require Import Multiset. About list_contents.
  Require Import Arith.

  Notation contents := (list_contents eq Nat.eq_dec).

  Lemma meq_multiplicity : forall (ls1 ls2 : list nat),
      (forall x, In x ls1 \/ In x ls2 ->
                 multiplicity (contents ls1) x = multiplicity (contents ls2) x) ->
      meq (contents ls1) (contents ls2).
  Proof.
    intros ls1 ls2 H x.
    destruct (in_dec Nat.eq_dec x ls1); [apply H; auto | ].
    destruct (in_dec Nat.eq_dec x ls2); [apply H; auto | ].
    repeat rewrite multiplicity_In_O; auto. 
  Defined.


  (* find the value of the first duplicated value in the list *)
  Fixpoint find_duplicate (ls : list nat) : option nat :=
    match ls with
    | nil => None
    | n :: ls' => if in_dec Nat.eq_dec n ls' then Some n 
                  else find_duplicate ls'
    end.


  (**************)
  (* Partiality *)
  (**************)

  
  Lemma interp_0 : forall (ls : list A),
      In ⊥ ls ->
      ⟨ls⟩ = ⊥.
  Proof.
    induction ls; intros pf_in; simpl in *.
    - contradiction.
    - destruct pf_in as [eq | pf_in].
      * rewrite eq. auto.  
      * rewrite IHls; auto.
  Defined.

End CMonoid.
Arguments index_wrt {A} {PCM_A}.
Arguments interp_permutation {A} {PCM_A} {PCM_Laws_A}.

(**************)
(* Automation *)
(**************)


(* Structural tactics *)
Ltac print_goal :=
  match goal with
  | [|- ?G ] => idtac G
  end.


Ltac type_of_goal :=
  match goal with
  | [ |- ?a = _] => type of a
  end.


Ltac has_evars term := 
  match term with
    | ?L = ?R        => has_evar L; has_evar R
    | ?L = ?R        => has_evars L
    | ?L = ?R        => has_evars R
    | ?Γ1 ∙ ?Γ2      => has_evar Γ1; has_evar Γ2
    | ?Γ1 ∙ ?Γ2      => has_evars Γ1
    | ?Γ1 ∙ ?Γ2      => has_evars Γ2
  end.


(* Simplify parts of an expression, but not the whole thing *)
Ltac simpl_arg e := let e' := fresh "e" in
                    set (e' := e);
                    simpl in e';
                    unfold e';
                    clear e'.

Ltac destruct_finite_In :=
  repeat match goal with
  | [ H : In _ _ \/ In _ _ |- _ ] => destruct H
  | [ H : In _ nil |- _ ] => apply (False_rect _ H)
  | [ H : In ?a (_ :: _) |- _ ] => destruct H; try (subst; reflexivity)
  end.


(* Ltac versions of term-level functions *)

Ltac append ls1 ls2 := 
  match ls1 with
  | ?x :: ?l => let l' := append l ls2 in constr:(x :: l')
  | nil      => ls2
  end.



Ltac lookup x xs :=
  match xs with
    | x :: _ => constr:(O)
    | ?y :: ?xs' => let n := lookup x xs' in constr:(S n)
  end.

Ltac difference ls1 ls2 :=
  match ls1 with
  | nil => ls1
  | ?x :: ?ls1' => (* if x ∈ ls2, then ls1' \ ls2*)
                   let i := lookup x ls2 in
                   difference ls1' ls2
  | ?x :: ?ls1' => (* if x ∉ ls2, then x ∪ (ls1' \ ls2) *)
                   let l := difference ls1' ls2 in
                   constr:(x :: l)
  end.


Ltac find_duplicate ls :=
  match ls with
  | ?n :: ?ls' => let z := lookup n ls' in n
  | _ :: ?ls' => find_duplicate ls'
  end.

(* Manipulating parts of the monoid *)

(* reposition an evar so that it occurs as the right-most associated application
of m on the LHS of a hypothesis *)
(* e.g. : a1 ∙ a2 ∙ ⋯ ∙ e = b1 ∙ ⋯ ∙ bn *)
Ltac repos_evar :=
  repeat match goal with 
  | [ |- ?G ] => (* if the goal has more than one evar, then fail *)
                 has_evars G; fail 1
  | [ |- ?a = ?b ] => (* the evar should occur on the LHS *)
                      has_evar b; symmetry 
  | [ |- context[?a ∙ ?b] ] => (* the evar should only occur on the RHS of an m *)
                              has_evar a; rewrite (M_comm a b)
  end;
  repeat match goal with 
  | [ |- ?a ∙ (?b ∙ ?c) = _ ] => rewrite (M_assoc a b c)
  end.

(*********************)
(* Doing reification *)
(*********************)


Ltac simpl_args :=
  match goal with
  | [ |- ⟨ ?e1 ⟩ ∙ ?ev = ⟨ ?e2 ⟩ ] => simpl_arg e1; simpl_arg e2
  | [ |- ⟨ ?e1 ⟩ = ⟨ ?e2 ⟩ ] => simpl_arg e1; simpl_arg e2
  end.

Ltac reify A a :=
  match a with
  | ⊥ => constr:(@M_zero A)
  | ⊤ => constr:(@M_one A)
  | ?a1 ∙ ?a2 => let e1 := reify A a1 in
                 let e2 := reify A a2 in
                 constr:(@M_m A e1 e2)
  | _ => constr:(@M_var A a)
  end.

Ltac prep_reification := 
  let A := type_of_goal in
  match goal with
  | [ |- ?a1 ∙ ?ev = ?a2 ] => (* evar case *)
    is_evar ev;
    let e1 := reify A a1 in
    let e2 := reify A a2 in
    change ((⟨e1⟩ : A) ∙ ev = (⟨e2⟩ : A));
    repeat rewrite flatten_correct; auto;
    simpl_args
  | [ |- ?a1 = ?a2 ] => (* non-evar case *)
    let e1 := reify A a1 in
    let e2 := reify A a2 in
    change ((⟨e1⟩ : A) = (⟨e2⟩ : A));
    repeat rewrite flatten_correct; auto;
    simpl_args  
  end.


(* reify_wrt (values ls : list A) : list nat 
     returns a list of indices `idx` so that (informally)
     ⟨index_wrt values idx⟩ = ⟨ls ∩ values⟩
 *)
Ltac reify_wrt values ls :=
  match ls with
  | nil => constr:(@nil nat)
  | ?a :: ?ls' => let i := lookup a values in
                  let idx := reify_wrt values ls' in
                  constr:(i :: idx)
  | _ :: ?ls' => (* if a does not occur in the reference list `values`, just skip it *)
                 reify_wrt values ls'
  end.

(* This tactic takes in three input lists: 
    values1, values2 : list A
    ls : list A
   
  It returns two lists of indices, idx1 and idx2, such that
    ⟨index_wrt values1 idx1⟩ ∙ ⟨index_wrt values2 idx2⟩ = ⟨ls⟩
  
 *)
Ltac split_reify_wrt values1 values2 ls := 
    let idx1 := reify_wrt values1 ls in
    let idx2 := reify_wrt values2 ls in
    constr:((idx1,idx2)).


Ltac solve_permutation :=
  apply interp_permutation;
  apply permutation_reflection;
  apply meq_multiplicity;
  intros; destruct_finite_In;
  fail.


(* This tactic finds fragments ⟨Some a⟩ and replaces them with ⟨a⟩ *)
Ltac strip_Some :=
  let A := type_of_goal in
  repeat match goal with
  | [ |- context[ ⟨Some ?a⟩ ] ] => 
    replace (⟨Some a⟩) with (⟨a⟩ : A) by auto
  end.

Ltac knot_reification tac := 
  strip_Some;
  tac;
  solve_permutation.




Ltac reification_wrt :=
  let A := type_of_goal in
  match goal with
  | [ |- ?a = ?a ] => reflexivity
  | [ |- ⟨?ls1⟩ = ⟨?ls2⟩ ] =>
    let src := append ls1 ls2 in 
    let idx1 := reify_wrt src ls1 in
    let idx2 := reify_wrt src ls2 in
    let ls1' := constr:(index_wrt src idx1) in
    let ls2' := constr:(index_wrt src idx2) in
    change ((⟨ls1'⟩ : A) = (⟨ls2'⟩ : A))
  | [ |- ⟨?ls1⟩ ∙ ?ev = ⟨?ls2⟩ ] =>
    let src := append ls1 ls2 in
    let ls2_1 := difference ls2 ls1 in
    let idx1  := reify_wrt src ls1 in (* indices of ls1 *)
    let idx2_1 := reify_wrt src ls2_1 in (* indices of ls2 that are not in ls1 *)
    let idx2' := constr:(index_wrt src (idx1 ++ idx2_1)) in
    replace (⟨ls2⟩) with (⟨idx2'⟩ : A) 
      by (simpl_args; strip_Some; reification_wrt; solve_permutation);
    rewrite split_list; auto
  end.

Ltac monoid := repos_evar; prep_reification; strip_Some; reification_wrt; solve_permutation.



Section Examples.
Variable A : Type.
Variable PCM_A : `{PCM A}.
Variable PCM_A_Laws : `{PCM_Laws A}.


Example PCM_comm' : forall (a b : A), a ∙ b = b ∙ a.
Proof.
  intros. monoid. 
Defined.

Example PCM_unit' : forall a, ⊤ ∙ a  = a.
Proof. 
  intros. monoid.
Defined.


Example PCM_absorb' : forall a, ⊥ ∙ a = ⊥.
Proof.
  intros. monoid. 
Defined.


Example PCM_aba : forall a b, a ∙ b ∙ a = a ∙ a ∙ b.
Proof.
  intros. monoid. 
Qed.


Example PCM_abc : forall a b c, a ∙ b ∙ c = c ∙ a ∙ ⊤ ∙ b.   
Proof.
  intros. monoid.
Defined.


Example PCM_evar : forall a b c, exists d, b = d -> a ∙ b ∙ c = c ∙ d ∙ a ∙ ⊤.   
Proof.
  intros. 
  evar (y : A).
  exists y. unfold y.
  intros. 
  monoid.
Qed.  

Example PCM_evar2 : forall a b c d e, exists x, x = d ∙ e ∙ b -> 
                                      a ∙ x ∙ c = b ∙ c ∙ d ∙ ⊤ ∙ e ∙ a. 
Proof.
  intros. 
  evar (y : A).
  exists y. unfold y.
  intros.
  monoid.
Qed.  

End Examples.