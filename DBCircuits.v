Require Import Contexts.
Require Import HOASCircuits.
Require Import Program.
Require Import List.
Require Import Monad.
Import Arith.
Open Scope circ_scope.

(* A minimal circuit *)
(* A well-formed DeBruijn_Circuit n w has exactly n input wires. 
*)
Inductive DeBruijn_Circuit (*n : nat*) (w : WType) : Set :=
| db_output : (*forall {pf : n = size_WType w},*)
              Pat w -> DeBruijn_Circuit w
| db_gate   : forall {w1 w2} (*{pf : n + size_WType w2 = n' + size_WType w1}*),
               Gate w1 w2 -> Pat w1 -> DeBruijn_Circuit w -> DeBruijn_Circuit w
| db_lift   :  (*{pf : n = S n'}*)
               Pat Bit -> (bool -> DeBruijn_Circuit w) -> DeBruijn_Circuit w
.

Inductive DeBruijn_Box (w1 w2 : WType) : Set :=
| db_box : DeBruijn_Circuit w2 -> DeBruijn_Box w1 w2.

Arguments db_output {w}.
Arguments db_gate {w w1 w2 }.
Arguments db_lift {w}.
Arguments db_box w1 {w2}.



(* Throughout this development, we will want to update some state based on the
presence of a gate. This is handled by a type class Gate_State, which models how
a gate might affect some underlying state:

    - We might need to create a fresh variable;

    - We might need to remove a variable from the state;

    - We might need to change the type of a variable in the state. Not all
      states will keep track of the type, but some will.
*)
Class Gate_State A :=
  { get_fresh  : WType -> State A Var 
  ; remove_var : Var -> A -> A
  ; change_type : Var -> WType -> A -> A
  }.

Fixpoint pat_to_list {w} (p : Pat w) : list Var :=
  match p with
  | unit => []
  | qubit x => [x]
  | bit x => [x]
  | pair p1 p2 => pat_to_list p1 ++ pat_to_list p2
  end.


Definition remove_pat {A} `{Gate_State A} {w} (p : Pat w) (a : A) : A :=
  fold_left (fun a x => remove_var x a)  (pat_to_list p) a.



(* process_gate_pat g p a returns the pattern that is obtained from running the
   gate g with input pattern p and state a 
*)
Definition process_gate_pat {A w1 w2} `{Gate_State A} (g : Gate w1 w2) : Pat w1 -> A -> Pat w2 :=
  match g with 
  | U _           => fun p _ => p
  | init0 | init1 => fun _ a => qubit (fst (get_fresh Qubit a))
  | new0 | new1   => fun _ a => bit (fst (get_fresh Bit a))
  | meas          => fun p _ => match p with
                                | qubit x => bit x
                                end
  | discard       => fun _ _ => unit
  end.

(* process_gate_state g p a returns the state that is obtained from running the
   gate g with input pattern p and state a. The two functions process_gate_pat
   and process_gate_state could be combined into one operation in a state monad,
   but the result requires a lot of bulky infrastructure for dealing with
   monads, unfortunately. It may be easier just to take two passes over the gate.
*)
Definition process_gate_state {A w1 w2} `{Gate_State A} (g : Gate w1 w2) : Pat w1 -> A -> A :=
  match g with 
  | U _           => fun _ a => a
  | init0 | init1 => fun _ a => snd (get_fresh Qubit a)
  | new0 | new1   => fun _ a => snd (get_fresh Bit a)
  | meas          => fun p a => match p with
                                | qubit x => change_type x Bit a
                                end
  | discard       => fun p a => remove_pat p a
  end.

    


(**********************)  
(* De Bruijn Contexts *)
(**********************)

Fixpoint remove_at  {A} (i : nat) (ls : list A) :=
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


Instance Ctx_State : Gate_State Ctx :=
  { get_fresh w  := do Γ ← get;
                    do _ ← put (Some w :: Γ);
                    return_ 0
  ; remove_var := remove_at
  ; change_type x w Γ := update_at Γ x (Some w)
  }.

Print Gate_State.
Instance OCtx_State : Gate_State OCtx :=
  { get_fresh w := fun Γ => match Γ with
                            | Invalid => (0, Invalid)
                            | Valid Γ' => let (x,Γ'') := get_fresh w Γ' in
                                          (x,Valid Γ'')
                            end
  ; remove_var x Γ := match Γ with
                      | Invalid => Invalid
                      | Valid Γ' => remove_var x Γ'
                      end
  ; change_type x w Γ := match Γ with
                         | Invalid => Invalid
                         | Valid Γ' => change_type x w Γ'
                         end
  }.
    
                   
                                         
                                         
                                         

(**********)
(* Typing *)
(**********)


(* Although we use ordinary (nominal) contexts for typing, it should be the case
that they are always "minimal", meaning that the list is equivalent to a list of
WTypes (as opposed to list (option WType)). However, because of context
splitting, this will only be enforcable at the top level. *)


Definition is_Some {A} (a : option A) :=
  match a with
  | Some _ => True
  | None => False
  end.

Fixpoint all_Some (Γ : Ctx) :=
  fold_left (fun prop x => is_Some x /\ prop) Γ True.
Definition Min (Γ : OCtx) :=
  match Γ with
  | Valid Γ' => all_Some Γ'
  | Invalid  => False
  end.

Definition OCtx_app (Γ1 Γ2 : OCtx) : OCtx :=
  match Γ1, Γ2 with
  | Valid Γ1', Valid Γ2' => Valid (Γ1' ++ Γ2')
  | _, _ => Invalid
  end.
Notation "Γ1 +++ Γ2" := (OCtx_app Γ1 Γ2) (right associativity, at level 30).

                         
Inductive Types_DB {w} (Γ : OCtx) : DeBruijn_Circuit w -> Prop :=
| types_db_output : forall p, Types_Pat Γ p -> Types_DB Γ (db_output p)
| types_db_gate   : forall Γ1 Γ2 w1 w2 (g : Gate w1 w2) p c,
                    Types_Pat Γ1 p ->
                    Types_DB (process_gate_state g p Γ) c ->
                    Γ = Γ1 ⋓ Γ2 -> is_valid Γ ->
                    Types_DB Γ (db_gate g p c)
                             
| types_db_lift   : forall Γ1 Γ2 Γ' p f,
                    Types_Pat Γ1 p ->
                    (forall b, Types_DB Γ' (f b)) ->
                    Γ = Γ1 ⋓ Γ2 -> is_valid Γ ->
                    Γ' = remove_pat p Γ -> (* Γ' is NOT Γ2 *)
                    Types_DB Γ (db_lift p f)
.

(*****************)
(* Substitutions *)
(*****************)

(* A substitution σ is a finite map from a variable x to a natural number i,
   where σ[i]=x. 
   This formulation of finite maps is unique because when a variable is removed from the list, 
   all variables above that one are shifted downward. 
*)
Definition substitution := list Var.

Print Gate_State.
Record subst_state := Mk_subst_state
  { get_σ : substitution
  ; fresh : nat }. 

Instance substitution_Gate_State : Gate_State subst_state :=
  { get_fresh w st := let x := fresh st in 
                      (x, Mk_subst_state (x :: get_σ st) (S x))
  ; remove_var x st := let σ' := List.remove Nat.eq_dec x (get_σ st) in
                        Mk_subst_state σ' (fresh st)
  ; change_type x w st := st
  }.
                      


Lemma in_S_fmap : forall x ls,
    In (S x) (fmap S ls) <->
    In x ls.
Admitted.

(* Precondition: x must appear in li *)
Fixpoint lookup (x : Var) (li : list Var) : nat :=
  match li with
  | nil => 0
  | y :: ys => if x =? y then 0 else S (lookup x ys)
  end.
Fixpoint index {A} (i : nat) (li : list A) : option A :=
  match i, li with
  | _, nil => None
  | 0, x :: _ => Some x
  | S i', _ :: li' => index i' li'
  end.

Definition subst_var (σ : substitution) (x : Var) := lookup x σ.
Fixpoint subst_pat (σ : subst_state) {w} (p : Pat w) : Pat w :=
  match p with
  | unit    => unit
  | qubit x => qubit (subst_var (get_σ σ) x)
  | bit   x => bit (subst_var (get_σ σ) x)
  | pair p1 p2 => pair (subst_pat σ p1) (subst_pat σ p2)
  end.

Fixpoint subst_db (σ : subst_state) {w} (c : DeBruijn_Circuit w) 
                : DeBruijn_Circuit w :=
  match c with
  | db_output p    => db_output (subst_pat σ p)
  | db_gate g p c' => let p' := subst_pat σ p in
                      let σ' := process_gate_state g p σ in
                      db_gate g p' (subst_db σ' c')
  | db_lift p f    => let p' := subst_pat σ p in
                      let σ' := remove_pat p σ in
                      db_lift p' (fun b => subst_db σ' (f b))
  end.


(* starting at i=|Γ|-1, finds the x such that x ↦ i ∈ σ, then looks up the type W of
   x in Γ. Adds the binding W to the head of the resulting DB_Ctx; by the end
   the process, this binding will be at index i in the list. *)

(*
Fixpoint subst_ctx' (Γ : Ctx) (σ : substitution) (i : nat) : option Ctx :=
  match i with
  | 0   => return_ []
  | S j => do x  ← index j σ;
           do Γ' ← subst_ctx' Γ σ j;
           return_ (Contexts.index Γ x :: Γ')
  end.

Definition subst_ctx (Γ : OCtx) σ : OCtx :=
  match Γ with
  | Valid Γ' => subst_ctx' Γ' σ (length Γ')
  | Invalid => Invalid
  end.

*)

(*
Fixpoint subst_ctx' Γ σ (x : nat) : OCtx :=
  match Γ with
  | []           => ∅
  | None   :: Γ' => subst_ctx' Γ' σ (S x)
  | Some w :: Γ' => (* if x does not occur in σ, then lookup x σ = length σ,
                       which is probably not the right answer. So we must assume that
                       σ is an isomorphism on its domain, and x < length σ. 
                       Assuming x <= length Γ, it suffices to assume length Γ <= length σ *)
    let y := lookup x σ in
    subst_ctx' Γ' σ (S x) ⋓ singleton y w
  end.

(* Example:
    let σ be the mapping x0 ↦ 2,
                         x3 ↦ 0,
                         x2 ↦ 1
    this is encoded as σ = [x3,x2,x0]

    Let Γ = [Some w0,None,Some w2,Some w3]

    The result should be [Some w3, Some w2, Some w0]
 *)

(* Running through the function:
   Step 1: Γ = [Some w0, None, Some w2, Some w3]
           σ = [x3,x2,x0]
           i = 0
   match to obtain...
      y = lookup 0 σ = 2
      subst_ctx' [None,Some w2, Some w3] σ 1 ⋓ singleton 2 w0
    =  ....................................  ⋓ [None,None,Some w0]

  Step 2: Γ = [None, Some w2, Some w3]
          i = 1
  match to obtain...
      subst_ctx' [Some w2, Some w3] σ 2

  Step 3: Γ = [Some w2, Some w3]
          i = 2
  match to obtain...
      y = lookup 2 σ = 1
      subst_ctx' [Some w3] σ 3 ⋓ singleton 1 w2
    = .......................  ⋓ [None,Some w2]

  Step 4: Γ = [Some w3]
          i = 3
  match to obtain....
      y = lookup 3 σ = 0
      subst_ctx' [] σ 4 ⋓ singleton 0 w3
    = ∅ ⋓ [Some w3]

  Thus... 
  Step 1 result is
    ∅ ⋓ [Some w3] ⋓ [None,Some w2] ⋓ [None,None,Some w0]
  = [Some w3, Some w2, Some w0] 
  ... as expected
*)

Definition subst_ctx (Γ : OCtx) σ : OCtx :=
  match Γ with
  | Valid Γ' => subst_ctx' Γ' σ 0
  | Invalid => Invalid
  end.
 *)

Definition subst_ctx' (Γ : Ctx) (σ : substitution) : Ctx :=
  fmap (Contexts.index Γ) σ.
Definition subst_ctx (Γ : OCtx) σ : OCtx :=
  match Γ with
  | Valid Γ' => Valid (subst_ctx' Γ' σ)
  | Invalid => Invalid
  end.

Lemma index_invalid : forall i, Contexts.index Invalid i = None.
Proof.
  destruct i; auto.
Qed.
Lemma index_empty : forall i, Contexts.index ∅ i = None.
Proof.
  destruct i; auto.
Qed.




Require Import Permutation. Print In.
Fixpoint Injective {A} (ls : list A) :=
  match ls with
  | [] => True
  | x :: ls' => ~ In x ls' /\ Injective ls'
  end.
  
Lemma index_nil : forall {A} x, index x ([] : list A) = None.
Proof.
  destruct x; auto.
Qed.



Record WF_σ (Γ : OCtx) σ :=
  { pf_inj : Injective σ
  ; pf_valid : is_valid Γ
  ; pf_subset : forall x w,
                Contexts.index Γ x = Some w ->
                In x σ
  }.

  


Lemma inj_S : forall σ, Injective σ <-> Injective (fmap S σ).
Admitted.





(* WF_σ Γ σ means that x ∈ dom(Γ) implies x ∈ dom(σ) 
   So if x ∈ dom(Γ) then S x ∈ dom(o :: Γ).
   So by hypothesis, S x ∈ (fmap S σ), which means 
   x ∈ σ.
 *)
(*
Lemma wf_σ_tail : forall σ o Γ,
    WF_σ (Valid (o :: Γ)) (fmap S σ) ->
    WF_σ (Valid Γ) σ.
Proof.
  intros σ o Γ [pf_inj pf_valid pf_subset].
  split.
  * apply inj_S; auto.
  * apply valid_valid.
  * intros x w pf_in.
    apply in_S_fmap.
    apply pf_subset with (w := w); auto.
Qed.  
 *)


(* PROPERTY:
    (subst_ctx σ Γ)[i] = Γ[σ[i]]
*)
Lemma valid_subst : forall Γ σ i,
    is_valid Γ ->
    Contexts.index (subst_ctx Γ σ) i = do x ← index i σ;
                                       Contexts.index Γ x.
Proof.
  destruct Γ as [ | Γ]; intros.
  * dependent destruction H.
  * unfold subst_ctx.
    generalize dependent Γ. generalize dependent i.
    induction σ; intros i Γ pf_wf.
  + unfold subst_ctx'. simpl.
    rewrite index_empty.
    rewrite index_nil.
    reflexivity.
    + replace (subst_ctx' Γ (a :: σ)) with (Contexts.index Γ a :: subst_ctx' Γ σ)
        by (unfold subst_ctx'; simpl; auto).
      simpl.
      destruct i as [ | i].
      - simpl. auto.
      - simpl. rewrite IHσ; auto.
Qed.

Lemma subst_ctx_nil : forall σ,
      subst_ctx ∅ σ = ∅.
Proof. 
  intros.
  unfold subst_ctx.
  reflexivity.
Qed.

Inductive SingletonOCtx x w : OCtx -> Prop :=
| SingletonValid : forall Γ, SingletonCtx x w Γ -> SingletonOCtx x w (Valid Γ).

Print subst_ctx'.


Definition maybe {A} (o : option A) (default : A) : A :=
  match o with
  | Some a => a
  | None => default
  end.

(*Lemma subst_ctx_cons : forall Γ σ n,
    subst_ctx (Valid Γ) σ (S n) =  maybe (do x ← index n σ;
                                            do w ← Contexts.index Γ x;
                                            do Γ' ← subst_ctx' Γ σ n;
                                            return_ (Some w :: Γ')) Invalid.
 *)

(* OR: lookup x σ = y ???*)


Notation "x ↦ y ∈ σ" := (index y σ = Some x) (at level 20).
Definition in_dom x σ := x ↦ subst_var σ x ∈ σ.
Notation "x '∈_dom' σ" := (in_dom x σ) (at level 20).


Lemma map_nil_inv : forall (x y : nat), ~ (x ↦ y ∈ []).
Proof.
  intros x y H.
  rewrite index_nil in H.
  inversion H.
Qed.

Lemma maps_to_in : forall y x (σ : substitution),
    x ↦ y ∈ σ -> In x σ.
Proof.
  induction y; intros.
  - simpl in H. destruct σ; inversion H; subst.
    simpl. auto.
  - simpl in *. destruct σ; inversion H; subst.
    simpl.
    right. apply IHy; auto.
Qed.

Lemma wf_subst_iso : forall (x y z : nat) (σ : substitution),
    Injective (z :: σ) -> x ↦ y ∈ σ -> x <> z.
Proof.
  intros; simpl in *.
  destruct H.
  intros eq; subst.
  absurd (In z σ); auto.
  eapply maps_to_in; eauto.
Qed.

Lemma index_lookup : forall σ x y, Injective σ ->
                                   x ↦ y ∈ σ -> lookup x σ = y.
Proof.
  induction σ; destruct y; intros wf_σ H; simpl in *.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    rewrite Nat.eqb_refl.
    reflexivity.
  - replace (x =? a) with false.
    destruct wf_σ as [not_in wf_σ].
    erewrite IHσ; [reflexivity | auto | auto]. 
    apply eq_sym. apply Nat.eqb_neq.
    eapply wf_subst_iso; eauto.
Qed.    

    
    
  
Lemma subst_ctx_singleton_eq' : forall x y i σ w,
    Injective σ ->
    (x + i)%nat ↦ y ∈ σ ->
    subst_ctx' (singleton x w) σ i = Valid (singleton y w).
Proof.
  induction x; intros y i σ w inj_σ pf_map.
  - simpl in *.
    erewrite index_lookup; eauto.
  - simpl in *.
    apply IHx; auto.
    rewrite Nat.add_succ_r.
    auto.
Qed.

Lemma subst_ctx_singleton_eq : forall x y σ w,
    Injective σ ->
    x ↦ y ∈ σ ->
    subst_ctx (singleton x w) σ = Valid (singleton y w).
Proof.
  intros.
  unfold subst_ctx.
  apply subst_ctx_singleton_eq'; auto. 
  rewrite Nat.add_0_r; auto.
Qed.
 
    

Lemma otypes_qubit : forall Γ x,
      SingletonOCtx x Qubit Γ ->
      Types_Pat Γ (qubit x).
Proof.
  destruct Γ. intros.
  - absurd (SingletonOCtx x Qubit Invalid); auto. inversion 1.
  - intros. constructor. inversion H; auto.
Qed.

Lemma otypes_bit : forall Γ x,
      SingletonOCtx x Bit Γ ->
      Types_Pat Γ (bit x).
Proof.
  destruct Γ. intros.
  - absurd (SingletonOCtx x Bit Invalid); auto. inversion 1.
  - intros. constructor. inversion H; auto.
Qed.



(*
Fixpoint Ctx_dom (Γ : Ctx) :=
  match Γ with
  | [] => []
  | Some w :: Γ' => 0 :: fmap S (Ctx_dom Γ')
  | None :: Γ' => fmap S (Ctx_dom Γ')
  end.
Definition OCtx_dom (Γ : OCtx) : list nat :=
  match Γ with
  | Valid Γ' => Ctx_dom Γ'
  | Invalid => []
  end.
*)


(*
Lemma in_dom_merge : forall Γ1 Γ2 x w,
      Contexts.index (Γ1 ⋓ Γ2) x = Some w ->
      Contexts.index Γ1 x = Some w \/ Contexts.index Γ2 x = Some w.
Admitted.
*)

(*
Lemma index_singleton : forall x y w w',
    Contexts.index (singleton x w) y = Some w' ->
    x = y  /\ w = w'.
Proof.
  induction x as [ | x]; destruct y as [ | y]; intros w w' H; simpl in *.
  - inversion H; auto.
  - destruct y; inversion H.
  - inversion H.
  -destruct (IHx _ _ _ H); subst; auto.
Qed.
*)

(*
Lemma subst_ctx'_bound : forall Γ x j σ w,
      Contexts.index (subst_ctx' Γ σ j) x = Some w ->
      j <= x.
Proof.
  induction Γ as [ | [w' | ] Γ]; intros x j σ w pf_in; simpl in *.
  - destruct x; inversion pf_in.
  - apply in_dom_merge in pf_in.
    destruct pf_in as [pf_in | pf_in].
    * apply IHΓ in pf_in.
      apply le_trans with (m := S j); auto.
    * Print subst_ctx'.
      apply index_singleton in pf_in.
      destruct pf_in; subst.
      assert (x = j) by auto.
      subst. auto.
  - apply IHΓ in pf_in.
    apply le_trans with (m := S j); auto.
Admitted.
 *)

Notation "x ∉ 'dom' Γ" := (Contexts.index Γ x = None) (at level 30).

(*
Lemma subst_ctx'_bound : forall Γ i j σ,
      Injective σ ->
      i <= j ->
      lookup i σ ∉ dom (subst_ctx' Γ σ j).
Proof.
  induction Γ as [ | o Γ]; intros i j σ pf_inj pf_le.
  * simpl. destruct (lookup i σ); auto.
  * simpl.
    assert (IH : lookup i σ ∉ dom (subst_ctx' Γ σ (S j))).
Admitted.
*)


Lemma valid_merge_singleton_r : forall Γ x w,
    x ∉ dom Γ -> is_valid Γ ->
    is_valid (Γ ⋓ singleton x w).
Proof.
  destruct Γ as [ | Γ].
  * inversion 2. inversion H1.
  * induction Γ as [ | [w' | ] Γ]; intros x w H pf_valid.
    - simpl. apply valid_valid.
    - simpl.
      destruct x as [ | x']; inversion H; simpl.
      assert (pf_valid' : is_valid (Valid Γ ⋓ singleton x' w)).
      { apply IHΓ; auto. apply valid_valid. }
      simpl in *.
      destruct (merge' Γ (singleton x' w)); [dependent destruction pf_valid' | ].
      apply valid_valid.
    - simpl in *.
      destruct x as [ | x']; simpl in *.
      + replace (merge' Γ []) with (Valid Γ ⋓ ∅) by auto.
        rewrite (merge_nil_r (Valid Γ)).
        apply valid_valid.
      + assert (pf_valid' : is_valid (merge' Γ (singleton x' w))).
        { apply IHΓ; auto. apply valid_valid. }
        destruct (merge' Γ (singleton x' w)); auto.
        apply valid_valid.
Qed.



(*
Lemma subst_ctx_merge_valid' : forall Γ1 Γ2 Γ i σ,
    Injective σ ->
    is_valid (subst_ctx' Γ1 σ i) ->
    is_valid (subst_ctx' Γ2 σ i) ->
    merge' Γ1 Γ2 = Valid Γ ->
    is_valid (subst_ctx' Γ σ i).
Proof.
  induction Γ1 as [ | o1 Γ1]; destruct Γ2 as [ | o2 Γ2]; intros Γ i σ wf_σ H1 H2 pf_merge.
  - simpl in *.
    inversion pf_merge.
    simpl. validate.
  - simpl in *.
    inversion pf_merge.
    simpl. destruct o2; auto.
  - simpl in *.
    inversion pf_merge.
    simpl. destruct o1; auto.
  - simpl in *.
    destruct o1 as [w1 | ], o2 as [w2 | ]; simpl in *.
    * inversion pf_merge.
    * destruct (merge' Γ1 Γ2) as [ | Γ'] eqn:H_Γ'; inversion pf_merge.
      simpl.
      apply valid_merge_singleton_r.
      + apply subst_ctx'_bound; auto.
      + eapply IHΓ1; auto; eauto.
        apply valid_split_basic in H1.
        destruct H1; auto.
          
    * destruct (merge' Γ1 Γ2) as [ | Γ'] eqn:H_Γ'; inversion pf_merge.
      simpl.
      apply valid_merge_singleton_r.
      + apply subst_ctx'_bound; auto.
      + eapply IHΓ1; auto; [ | eauto]. 
        apply valid_split_basic in H2.
        destruct H2; auto.
          
    * destruct (merge' Γ1 Γ2) as [ | Γ'] eqn:H_Γ'; inversion pf_merge.
      simpl.
      eapply IHΓ1; auto; [ | eauto]; auto.
Qed.
*)


(*
Lemma map_subst_var : forall σ x Γ w,
  wf_σ Γ σ ->
  Contexts.index Γ x = Some w ->
  x ↦ subst_var σ x ∈ σ.
Proof.
  intros σ x Γ w [pf_σ H] H'.
  eapply H.
  apply H'.
Qed.
 *)


(*** TODO: need to use injectivity here *)
Lemma index_eq_le : forall Γ σ i j,
      i <= j ->
      Contexts.index (subst_ctx' Γ σ j) (lookup i σ) = None.
Proof. Print subst_ctx'.
(* 
    Claim 1: size (subst_ctx' Γ σ j) = size Γ
    Claim 2: the maximum index value in (subst_ctx' Γ σ j) is
           <= max_{i >= j} (lookup i σ)
    So x >= max_{i >= j} (lookup i σ) implies (subst_ctx' Γ σ j)[x]=None
    But σ is not necessarily monotonic, so we don't know that
    i < j implies  (lookup i σ) < lookup j σ <= max_value
*)
Admitted.


Print subst_ctx'.


(* When can we be sure that 
  (lookup x σ) ∉ subst_ctx' Γ σ j? 

  Well, we know 
    (subst_ctx' Γ σ j)[x] = Some w
  provided 
    there exists some y such that y ↦ x ∈ σ
    and Γ[y] = Some w

 *)




Inductive WF_σ' : Ctx -> substitution -> nat -> Prop :=
| wf_nil  : forall σ x, WF_σ' [] σ x
| wf_Some : forall w Γ σ x,
    WF_σ' Γ σ (S x) ->
    Contexts.index Γ (lookup x σ) = None ->
    WF_σ' (Some w :: Γ) σ x
| wf_None : forall Γ σ x,
    WF_σ' Γ σ (S x) ->
    WF_σ' (None :: Γ) σ x.
Lemma wf_σ'_index : forall Γ σ x,
    WF_σ' Γ σ x ->
    forall i w, Contexts.index Γ i = Some w ->
                In (i + x) σ.
Proof.
  induction 1; intros i w' pf_index.
  - destruct i; inversion pf_index.
  - destruct i as [ | i].
    admit. simpl.
    
  -
    
    


Lemma subst_ctx'_in : forall Γ σ x j w,
    Contexts.index (subst_ctx' Γ σ j) x = Some w ->
    x ↦ (lookup x σ) ∈ σ.
Proof.
  intros.
   Print subst_ctx'.
  
  induction Γ as [ | [w' | ] Γ]; intros σ x j w pf_index.
  * simpl in pf_index.
    destruct x; inversion pf_index.
  * simpl in *.
    remember (subst_ctx' Γ σ (S j) ⋓ singleton (lookup j σ) w')
      as Γ' eqn:H_Γ'.
    destruct Γ' as [ | Γ']; [destruct x; inversion pf_index | ].
    destruct (Nat.eq_dec (x) (lookup j σ)).
    + subst.
      assert (w = w') by admit.
    + 
    
    

(*???????*)
Lemma subst_ctx_valid' : forall Γ σ i,
  WF_σ (Valid Γ) σ ->
  is_valid (subst_ctx' Γ σ i) .
Proof.
  induction Γ as [ | o Γ]; intros σ i pf_valid (*[ pf_inj pf_valid pf_subset];*);
    simpl in *.
  * apply valid_valid.
  * assert (is_valid (subst_ctx' Γ σ (S i))).
    { apply IHΓ.
      apply wf_σ_tail with (o := o).
      destruct pf_valid. split; auto.
      + apply (inj_S σ); auto.
      + intros x w pf_index.
        admit.
    }
    destruct o; auto.
    apply valid_merge_singleton_r; auto.
    (* need to prove:
       index (lookup i σ) (subst_ctx' Γ σ (S i)) = None
     *)
    apply index_eq_le; auto.
  Admitted.

Lemma subst_ctx_valid : forall Γ σ,
    WF_σ Γ σ ->
    is_valid (subst_ctx Γ σ).
Proof.
  intros Γ σ pf_σ. destruct Γ as [ | Γ].
  * simpl. destruct pf_σ. dependent destruction pf_valid0.
  * simpl. apply subst_ctx_valid'. auto.
Qed.



Lemma subst_ctx_merge' : forall Γ1 Γ2 Γ σ i,
      Valid Γ = merge' Γ1 Γ2 ->
      subst_ctx' Γ σ i = subst_ctx' Γ1 σ i ⋓ subst_ctx' Γ2 σ i.
Proof.
  induction Γ1 as [ | o1 Γ1], Γ2 as [ | o2 Γ2]; intros Γ σ i pf_merge.
  * simpl in *.
    dependent destruction pf_merge. auto.
  * simpl in pf_merge. dependent destruction pf_merge.
    rewrite merge_nil_l.
    reflexivity.
  * simpl in pf_merge.
    dependent destruction pf_merge.
    rewrite merge_nil_r.
    reflexivity.
  * destruct o1 as [ w1 | ], o2 as [ w2 | ].
    + dependent destruction pf_merge.
    + simpl in pf_merge.
      destruct (merge' Γ1 Γ2) as [ | Γ'] eqn:H_Γ'; 
        dependent destruction pf_merge.
      simpl.
      rewrite (IHΓ1 Γ2 Γ' σ (S i)); auto.
      monoid.
    + simpl in pf_merge.
      destruct (merge' Γ1 Γ2) as [ | Γ'] eqn:H_Γ'; 
        dependent destruction pf_merge.
      simpl.
      rewrite (IHΓ1 Γ2 Γ' σ (S i)); auto.
      monoid.
    + simpl in pf_merge.
      destruct (merge' Γ1 Γ2) as [ | Γ'] eqn:H_Γ'; 
        dependent destruction pf_merge.
      simpl.
      rewrite (IHΓ1 Γ2 Γ' σ (S i)); auto.
Qed.

    
Lemma subst_ctx_merge : forall Γ1 Γ2 σ,
    WF_σ (Γ1 ⋓ Γ2) σ ->
    subst_ctx (Γ1 ⋓ Γ2) σ = subst_ctx Γ1 σ ⋓ subst_ctx Γ2 σ.
Proof.
  intros Γ1 Γ2 σ pf_σ.
  (*  set (pf_valid := subst_ctx_valid _ _ pf_σ H).*)
  assert (H : is_valid (Γ1 ⋓ Γ2)) by (destruct pf_σ; auto).
  unfold subst_ctx.
  destruct Γ1 as [ | Γ1], Γ2 as [ | Γ2]; dependent destruction H.
  rename x into Γ.
  rewrite H.
  apply subst_ctx_merge'; auto.
Qed.


Lemma SingletonOCtx_eq : forall x w Γ,
      Γ = Valid (singleton x w) ->
      SingletonOCtx x w Γ.
Proof.
  intros. subst.
  constructor.
  apply singleton_singleton.
Qed.



Lemma SingletonCtx_index : forall Γ x w,
        SingletonCtx x w Γ ->
        Contexts.index Γ x = Some w.
Proof.
  induction 1; auto.
Qed.



Lemma index_merge_l : forall x Γ1 Γ2 w,
    Contexts.index Γ1 x = Some w ->
    is_valid (Γ1 ⋓ Γ2) ->
    Contexts.index (Γ1 ⋓ Γ2) x = Some w.
Proof.
  induction x as [ | x]; intros Γ1 Γ2 w pf_index pf_valid;
    destruct Γ1 as [ | [ | [w1 | ] Γ1]];
    destruct Γ2 as [ | [ | [w2 | ] Γ2]];
    try (simpl in *;
         dependent destruction pf_index;
         auto; fail);
    try ( simpl in *;
          absurd (is_valid Invalid); [ apply not_valid | auto]; fail);
    try (
        dependent destruction pf_index;
        dependent destruction pf_valid; simpl; auto; fail).
  * simpl in *.
    dependent destruction pf_index.
    destruct (merge' Γ1 Γ2) as [ | Γ];
      [absurd (is_valid Invalid); [apply not_valid | auto] | ].
    auto.
  * simpl in *.
    destruct (merge' Γ1 Γ2) as [ | Γ] eqn:H_Γ;
      [absurd (is_valid Invalid); [apply not_valid | auto] | ].
    apply IHx with (Γ2 := Valid Γ2) in pf_index; auto.
    simpl in *.
    rewrite H_Γ in pf_index.
    auto.
    simpl. rewrite H_Γ. apply valid_valid.
  * simpl in *.
    destruct (merge' Γ1 Γ2) as [ | Γ] eqn:H_Γ;
      [absurd (is_valid Invalid); [apply not_valid | auto] | ].
    apply IHx with (Γ2 := Valid Γ2) in pf_index; auto.
    simpl in *.
    rewrite H_Γ in pf_index.
    auto.
    simpl. rewrite H_Γ. apply valid_valid.
  * simpl in *.
    destruct (merge' Γ1 Γ2) as [ | Γ] eqn:H_Γ;
      [absurd (is_valid Invalid); [apply not_valid | auto] | ].
    apply IHx with (Γ2 := Valid Γ2) in pf_index; auto.
    simpl in *.
    rewrite H_Γ in pf_index.
    auto.
    simpl. rewrite H_Γ. apply valid_valid.
Qed.


Lemma index_merge_r : forall x Γ1 Γ2 w,
    Contexts.index Γ2 x = Some w ->
    is_valid (Γ1 ⋓ Γ2) ->
    Contexts.index (Γ1 ⋓ Γ2) x = Some w.
Proof.
  intros.
  rewrite merge_comm.
  apply index_merge_l; auto.
  rewrite merge_comm.
  auto.
Qed.



Lemma wf_σ_merge : forall Γ1 Γ2 σ,
    WF_σ (Γ1 ⋓ Γ2) σ ->
    WF_σ Γ1 σ /\ WF_σ Γ2 σ.
Proof.
  intros Γ1 Γ2 σ [H H'].
  split.
  * split; auto.
    + destruct Γ1; [ dependent destruction H' | apply valid_valid].
    + intros x w index_x.
      apply pf_subset0 with (w := w).
      apply index_merge_l; auto.
  * split; auto.
    + destruct Γ2; [ dependent destruction H' | apply valid_valid].
      destruct Γ1; inversion H0.
    + intros x w index_x.
      apply pf_subset0 with (w := w).
      apply index_merge_r; auto.
Qed.

Lemma in_maps_to : forall σ x,
      In x σ ->
      x ↦ (subst_var σ x) ∈ σ.
Proof.
  induction σ; simpl; intros x pf_in.
  * contradiction.
  * destruct (Nat.eq_dec x a).
    + subst. 
      rewrite Nat.eqb_refl.
      auto.
    + destruct pf_in as [eq | pf_in]; [absurd (a = x); auto | ].
      Search (_ =? _ = false).
      replace (x =? a) with false
        by (apply eq_sym; apply Nat.eqb_neq; auto).
      simpl.
      apply IHσ; auto.
Qed.

Lemma types_subst_pat_db : forall Γ w (p : Pat w),
    Types_Pat Γ p ->
    forall Γ' σ, WF_σ Γ (get_σ σ) ->
    Γ' = subst_ctx Γ (get_σ σ) ->
    Types_Pat Γ' (subst_pat σ p).
Proof.
  induction 1; intros Γ' σ pf_σ pf_Γ'; subst.
  - simpl. constructor.
  - unfold subst_pat.
    apply otypes_qubit.
    replace Γ with (singleton x Qubit)
      by (apply eq_sym; apply singleton_equiv; auto).
    apply SingletonOCtx_eq.
    destruct pf_σ.
    apply subst_ctx_singleton_eq; auto.
    apply in_maps_to.
    eapply pf_subset0.
    apply SingletonCtx_index; eauto.
  - unfold subst_pat.
    apply otypes_bit.
    replace Γ with (singleton x Bit)
      by (apply eq_sym; apply singleton_equiv; auto).
    apply SingletonOCtx_eq.
    destruct pf_σ as [inj_σ pf_σ].
    apply subst_ctx_singleton_eq; auto.
    apply in_maps_to.
    eapply pf_subset0.
    apply SingletonCtx_index; eauto.
  - simpl.
    destruct (wf_σ_merge _ _ _ pf_σ) as [pf_σ1 pf_σ2].
    econstructor; [  | 
                     | apply IHTypes_Pat1; auto
                     | apply IHTypes_Pat2; auto].
    apply subst_ctx_valid; auto.
    apply subst_ctx_merge; auto.
Qed.

Lemma wf_remove_pat : forall w (p : Pat w) σ Γ,
  WF_σ Γ (get_σ σ) ->
  WF_σ (remove_pat p Γ) (get_σ (remove_pat p σ)).
Admitted.

Lemma wf_gate_state : forall w1 w2 (g : Gate w1 w2) p Γ σ,
        WF_σ Γ (get_σ σ) ->
        WF_σ (process_gate_state g p Γ) (get_σ (process_gate_state g p σ)).
Admitted.

Lemma subst_remove_pat : forall w (p : Pat w) σ Γ,
    WF_σ Γ (get_σ σ) ->
    remove_pat (subst_pat σ p) (subst_ctx Γ (get_σ σ))
  = subst_ctx (remove_pat p Γ) (get_σ (remove_pat p σ)).
Admitted.

    

Lemma subst_process_gate : forall w1 w2 (g : Gate w1 w2) p σ Γ,
    WF_σ Γ (get_σ σ) ->
    process_gate_state g (subst_pat σ p) (subst_ctx Γ (get_σ σ))
  = subst_ctx (process_gate_state g p Γ) (get_σ (process_gate_state g p σ)).
Admitted.

Lemma types_subst_db : forall w (c : DeBruijn_Circuit w) Γ ,
      Types_DB Γ c ->
      forall {σ Γ'}, WF_σ Γ (get_σ σ) ->
      Γ' = subst_ctx Γ (get_σ σ) ->
      Types_DB Γ' (subst_db σ c).
Proof.
  induction 1; intros σ Γ0 pf_wf pf_Γ0; simpl.
  - constructor.
    eapply types_subst_pat_db; eauto.
  - subst. econstructor.
    * eapply types_subst_pat_db;
        [eauto | apply (wf_σ_merge _ _ _ pf_wf) | reflexivity ].
    * apply IHTypes_DB; auto.
      + apply wf_gate_state; auto.
      + apply subst_process_gate; auto.
    * apply subst_ctx_merge; auto.
    * apply subst_ctx_valid; auto.
  - subst.
    econstructor.
    * eapply types_subst_pat_db;
        [eauto | apply (wf_σ_merge _ _ _ pf_wf) | reflexivity ].
    * intros b. apply H1.
      + apply wf_remove_pat; auto.
      + reflexivity.
    * apply subst_ctx_merge; auto.
    * apply subst_ctx_valid; auto.
    * rewrite subst_remove_pat; auto.
Qed.
    
      
             
    


(***************)
(* composition *)
(***************)


(* produces the substitution context *)
  
    
(*
Definition OCtx_to_subst_state (Γ : OCtx) : subst_state :=
  match Γ with
  | Valid Γ' => 
 *)


(*
Fixpoint mk_subst {w} (p : Pat w) : substitution :=
  match p with
  | unit       => []
  | bit x      => [x]
  | qubit x    => [x]
  | pair p1 p2 => (mk_subst p1) ++ (mk_subst p2)
  end.
 *)
Fixpoint mk_subst {w} (p : Pat w) (pad : nat) : substitution :=
  pat_to_list p ++ seq (size_WType w) pad.
About max.
Definition max_list (σ : substitution) :=
  fold_left max σ 0.

Definition mk_subst_state {w} (p : Pat w) (pad : nat) : subst_state :=
  let σ := mk_subst p pad in
  Mk_subst_state σ (max_list σ).


Fixpoint db_compose {w w'} (in_c' : nat) (*|w| + in_c' is the number of inputs to c'
                                         *)
                           (c : DeBruijn_Circuit w) (c' : DeBruijn_Circuit w')
                  : DeBruijn_Circuit w' :=
  match c with
  | db_output p   => subst_db (mk_subst_state p in_c') c'
  | db_gate g p c => db_gate g p (db_compose in_c' c c')
  | db_lift p f   => db_lift p (fun b => db_compose in_c' (f b) c')
  end.

Fixpoint WType_to_Ctx w :=
  match w with
  | One => []
  | Qubit => [Some Qubit] 
  | Bit => [Some Bit] 
  | W1 ⊗ W2 => WType_to_Ctx W1 ++ WType_to_Ctx W2
  end.



Lemma wf_app : forall Γ1 Γ2 σ,
        WF_σ (Valid Γ1) σ ->
        WF_σ (Valid Γ2) (fmap (Nat.add (length Γ1)) σ) ->
        WF_σ (Valid (Γ1 ++ Γ2)) σ.
Proof.
  intros Γ1 Γ2; generalize dependent Γ1.
  induction Γ2 as [ | o2 Γ2]; intros Γ1 σ pf1 pf2.
  * rewrite app_nil_r; auto.
  * replace (Γ1 ++ o2 :: Γ2) with ((Γ1 ++ [o2]) ++ Γ2)
      by (rewrite <- app_assoc; auto).
    replace (fmap (Nat.add (length Γ1)) σ)
      with (fmap S (fmap (Nat.add (length Γ1 - 1)%nat) (σ : list nat))).
        
    apply IHΓ2.

    
  
  induction Γ1; intros Γ2 σ pf1 pf2.
  * simpl in *. replace (list_fmap (fun m : nat => m) σ) with σ in pf2; auto.
    { clear Γ2 pf1 pf2. induction σ; simpl; auto. rewrite <- IHσ; auto. }
  * simpl in *.
    apply wf_σ_tail in pf1.
    assert (IH : WF_σ (Valid (Γ1 ++ Γ2)) 
    apply 
    

Search (OCtx -> nat). Print size_Ctx.

Lemma db_compose_correct : forall {w} {Γ1 : Ctx} (c : DeBruijn_Circuit w),
                           Types_DB Γ1 c ->
                           forall {w'} {Γ2 Γ : Ctx} {Γ2'} (c' : DeBruijn_Circuit w'),
    Γ2 = WType_to_Ctx w ->
    Types_DB (Valid (Γ2 ++ Γ)) c' ->
    Γ2' = Valid (Γ1 ++ Γ) ->
    Types_DB Γ2' (db_compose (length_OCtx Γ) c c').
Proof.
  induction 1; intros w' Γ02 Γ0' Γ02' c' H_Γ02 types_c' H_Γ02'.
  - simpl. subst.
    eapply types_subst_db.
    * apply types_c'.
    *
        
      admit.
    * unfold mk_subst_state. simpl.
      admit.
  - simpl. subst.
    econstructor.
    * eauto.
    * eapply IHTypes_DB; [reflexivity | apply types_c' | ]. admit (*?*).
    * admit.
    * apply valid_valid.
  - simpl. subst.
    econstructor.
    * eauto.
    * intros b. eapply H1; [ reflexivity | apply types_c' | reflexivity].
    * admit.
    * apply valid_valid.
    * admit.
Admitted.




(******************************************)
(* Turning HOAS circuits into DB circuits *)
(******************************************)

Fixpoint hoas_to_db {w} (c : Circuit w) (σ : subst_state) : DeBruijn_Circuit w :=
  match c with
  | output p   => db_output p
  | gate g p f => (* p' will be the input to f, so a hoas-level pat *)
                  let p' := process_gate_pat g p σ in
                  (* p0 is the db-pat corresponding to p *)
                  let p0 := subst_pat σ p in
                  (* σ' is the updated substitution,to go with p' *)
                  let σ' := process_gate_state g p σ in
                  db_gate g p0 (hoas_to_db (f p') σ')
  | lift p f   => let p0 := subst_pat σ p in
                  let σ' := remove_pat p σ in
                  db_lift (subst_pat σ p) (fun b => hoas_to_db (f b) σ')
  end.

About get_fresh.
Fixpoint get_fresh_pat {A} `{Gate_State A} (w : WType) : State A (Pat w) :=
  match w with
  | One   => return_ unit
  | Qubit => do x ← get_fresh Qubit;
             return_ (qubit x)
  | Bit   => do x ← get_fresh Bit;
             return_ (bit x)
  | w1 ⊗ w2 => do p1 ← get_fresh_pat w1;
               do p2 ← get_fresh_pat w2;
               return_ (pair p1 p2)
  end.

  

Definition empty_subst_state := Mk_subst_state [] 0.

Definition hoas_to_db_box {w1 w2} (B : Box w1 w2) : DeBruijn_Box w1 w2 :=
  match B with
  | box f => let (p,σ) := get_fresh_pat w1 empty_subst_state in
             db_box w1 (hoas_to_db (f p) σ)
  end.
