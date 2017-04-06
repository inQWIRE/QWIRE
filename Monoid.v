Require Import List.
Open Scope list_scope.

(* Monoid type class *)

Class Monoid {A} (m : A -> A -> A) (u : A) :=
{
    assoc  : forall a b c, m a (m b c) = m (m a b) c;
    unit_l : forall a, m u a = a;
    unit_r : forall a, m a u = a
}.

Section Monoid.
  Variable A : Set.
  Variable m : A -> A -> A.
  Variable u : A.
  Infix "+" := m.
  Hypothesis M : Monoid m u.


  Inductive mexp :=
  | Ident : mexp
  | Var : A -> mexp
  | Op : mexp -> mexp -> mexp.

  Fixpoint mdenote (me : mexp) : A :=
    match me with
      | Ident => u
      | Var a => a
      | Op me1 me2 => m (mdenote me1) (mdenote me2)
    end.
  Fixpoint mldenote (ls : list A) : A :=
    match ls with
      | nil => u
      | x :: ls' => x + mldenote ls'
    end.

  Fixpoint flatten (me : mexp) : list A :=
    match me with 
      | Ident => nil
      | Var x => x :: nil
      | Op me1 me2 => flatten me1 ++ flatten me2
    end.

  Lemma mldenote_correct : forall ml1 ml2,
                             mldenote ml1 + mldenote ml2 = mldenote (ml1 ++ ml2 ).
  Proof.
    induction ml1; intros ml2; simpl.
    - rewrite unit_l. reflexivity.
    - rewrite <- IHml1. rewrite <- assoc. reflexivity.
  Qed.

  Lemma flatten_correct : forall me, mdenote me = mldenote (flatten me).
  Proof.
    induction me; simpl; auto.
    - rewrite unit_r. reflexivity.
    - rewrite IHme1. rewrite IHme2. rewrite mldenote_correct. reflexivity.
  Qed.
  
  Theorem monoid_reflect : forall me1 me2,
                             mldenote (flatten me1 ) = mldenote (flatten me2 )
                             -> mdenote me1 = mdenote me2.
    intros; repeat rewrite flatten_correct; assumption.
  Qed.

  Ltac reify me :=
    match me with
      | u           => Ident
      | m ?me1 ?me2 => let r1 := reify me1 in
                       let r2 := reify me2 in
                       constr:(Op r1 r2)
      | _           => constr:(Var me)
    end.

  Ltac equate x y :=
    let dummy := constr:(eq_refl x : x = y) in idtac.



  (* We assume m1 and m2 are lists of primitives, none of which are unit *)
  Ltac equate_monoids m12 :=
    match m12 with
      | (nil      , nil      ) => idtac 
      | (nil      , ?x :: ?m2) => equate x u; equate_monoids (nil,m2)
      | (?x :: ?m1, nil      ) => equate x u; equate_monoids (m1,nil)
      | (?x :: ?m1, ?x :: ?m2) => equate_monoids (m1,m2)
    end.


  Ltac monoid :=     match goal with
    | [ |- ?me1 = ?me2 ] => let r1 := reify me1 in
                            let r2 := reify me2 in
                            change (mdenote r1 = mdenote r2);
                            apply monoid_reflect; simpl flatten
    end;
    try ( match goal with
          [ |- mldenote ?ls1 = mldenote ?ls2 ] => equate_monoids (ls1,ls2)
          end;
          reflexivity
    ).


Theorem t1 : forall a b c d, a + b + c + d = a + (b + c) + d.
  intros; monoid.
Qed.
(*
Ltac monoid :=
  (* the evar should occur on the right hand side of the equation *)
  match goal with
  | [ |- ?a = _ ] => has_evar a; symmetry
  end;
  repeat (
    repeat (rewrite <- assoc);
    match goal with 
    | [ |- ?a = ?a ] => reflexivity
    | [ |- ?a = ?b ] => is_evar a; reflexivity
    | [ |- ?a = ?b ] => is_evar b; reflexivity
    (* remove identities *)
    | [ _ : Monoid ?m ?u |- context[?m ?a ?u] ] => rewrite (unit_r a)
    | [ _ : Monoid ?m ?u |- context[?m ?u ?a] ] => rewrite (unit_l a)
    (* solve nil evars *)
    | [ _ : Monoid ?m ?u |- ?a = ?m ?a _ ] => rewrite (unit_r a); reflexivity
    | [ _ : Monoid ?m ?u |- ?a = ?m _ ?a ] => rewrite (unit_l a); reflexivity
    (* apply f_eq *)
    | [ _ : Monoid ?m ?u |- ?m ?a _ = ?m ?a _ ] => f_equal
    end
  ).
*)


(* Commutative Monoid *)
Class CMonoid {A} (m : A -> A -> A) (u : A) `{Monoid A m u} :=
{
    comm : forall (a b : A), m a b = m b a
}.


  Hypothesis CM : CMonoid m u.

Print mexp.

Ltac get_evars ls :=
  match ls with
  | nil       => constr:(nil)
  | ?a :: ?ls => let ls' := get_evars ls in
                 tryif is_evar a then constr:(a :: ls') else ls'
  end.
Ltac get_concrete ls :=
  match ls with
  | nil       => nil
  | ?a :: ?ls => let ls' := get_concrete ls in
                 tryif is_evar a then ls' else constr:(a :: ls')
  end.
Require Import Coq.Sorting.Permutation.

Check Permutation.
(* tactic: finish_basic_perms *)

Lemma permutation_correct : forall ls1 ls2,
      Permutation ls1 ls2 -> mldenote ls1 = mldenote ls2.
Proof.
  induction 1; simpl; auto.
  - rewrite IHPermutation; auto.
  - repeat rewrite assoc. rewrite (comm y x). reflexivity.
  - rewrite IHPermutation1. auto.
Qed.


Import ListNotations.
Ltac find_before x ls :=
  match ls with
  | x  :: _ => constr:(@nil A)
  | ?y :: ?tail => let ls' := find_before x tail in constr:(y :: ls')
  end.
Ltac find_after x ls :=
  match ls with
  | x :: ?tail => tail
  | _ :: ?tail => find_after x tail
  end.

Ltac split_with a ls :=
  let before := find_before a ls in
  let after  := find_after  a ls in
  change ls with (before ++ a :: after).

Ltac permutation := 
  simpl; match goal with
  | [ |- Permutation ?ls ?ls ]           => apply perm_nil
  | [ |- Permutation (?a :: ?ls1) ?ls2 ] => 
         split_with a ls2;
         apply Permutation_cons_app; permutation
  end.

Lemma test : forall (a1 a2 a3 : A), Permutation [a1;a2;a3] [a3;a1;a2].
Proof. (*permutation.*)
  intros. permutation.
Qed.


Ltac print_goal :=
  match goal with
  | [ |- ?G ] => idtac G
  end.
Ltac try_for_each ls tac :=
  simpl;
  match ls with
  | nil        => idtac
  | ?a :: ?ls' => idtac "Trying " a; try (tac a); try_for_each ls' tac
  end.

Check Permutation_cons_app.
Lemma mldenote_cons_app : forall ls ls1 ls2 a,
      mldenote ls = mldenote (ls1 ++ ls2) 
   -> mldenote (a :: ls) = mldenote (ls1 ++ a :: ls2).
Proof.
  intros ls ls1; revert ls.
  induction ls1 as [ | a1 ls1]; intros ls ls2 a tail; simpl in *.
  - rewrite tail. reflexivity.
  - rewrite <- (IHls1 (ls1 ++ ls2)); [ | reflexivity].
    rewrite tail. 
    assert (a + a1 = a1 + a). apply comm.
    repeat rewrite assoc. rewrite H.
    reflexivity.
Qed.

Lemma mldenote_cons : forall a ls1 ls2,
      mldenote ls1 = mldenote ls2
   -> mldenote (a :: ls1) = mldenote (a :: ls2).
Proof.
  intros. simpl. rewrite H. reflexivity.
Qed.

Check eq_sym.

Ltac elim_dup a :=
  match goal with
  | [ |- mldenote ?ls1 = mldenote ?ls2 ] => 
         let before1 := find_before a ls1 in
         let after1  := find_after  a ls1 in
         let before2 := find_before a ls2 in
         let after2  := find_after  a ls2 in
         apply (@eq_trans _ _ (mldenote (before1 ++ a :: after1))); [reflexivity |];
         apply (@eq_trans _ _ (mldenote (before2 ++ a :: after2))); [| reflexivity];
         apply (@eq_trans _ _ (mldenote (a :: before1 ++ after1))); 
            [apply eq_sym; apply mldenote_cons_app; reflexivity | ];
            (*rewrite <- (mldenote_cons_app (before1 ++ after1)) ; reflexivity | ];*)
         apply (@eq_trans _ _ (mldenote (a :: before2 ++ after2))); 
             [ | apply mldenote_cons_app; reflexivity];
(*            [ | rewrite <- (mldenote_cons_app (before2 ++ after2)); reflexivity];*)
         apply mldenote_cons
(*
         change ls1 with (before1 ++ a :: after1);
         change ls2 with (before2 ++ a :: after2);
         rewrite <- (mldenote_cons_app (before1 ++ after1)); 
         [ rewrite <- (mldenote_cons_app (before2 ++ after2)); [ | auto ] | auto ]
*)
  end.

Opaque mldenote.
Ltac elim_dups :=
  simpl;
  match goal with
  | [ |- mldenote ?ls1 = mldenote ?ls2 ] => try_for_each ls1 elim_dup
  end.

  Ltac cmonoid := 
    match goal with
    | [ |- ?me1 = ?me2 ] => let r1 := reify me1 in
                            let r2 := reify me2 in
                            change (mdenote r1 = mdenote r2);
                            apply monoid_reflect; simpl flatten
    end;
    match goal with
    [ |- mldenote ?ls1 = mldenote ?ls2 ] => elim_dups
    end;
    try reflexivity.




Theorem t2 : forall a b c d, b + a + d + c = a + (b + c) + d.
  intros. cmonoid.
Qed.


End Monoid.