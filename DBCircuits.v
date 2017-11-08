Require Import Prelim.
Require Import Monad.
Require Import Contexts.
Require Import HOASCircuits.

Open Scope circ_scope.

Inductive DeBruijn_Circuit (w : WType) : Set :=
| db_output : Pat w -> DeBruijn_Circuit w
| db_gate   : forall {w1 w2},
               Gate w1 w2 -> Pat w1 -> DeBruijn_Circuit w -> DeBruijn_Circuit w
| db_lift   : Pat Bit -> (bool -> DeBruijn_Circuit w) -> DeBruijn_Circuit w
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

Definition remove_pat {A} `{Gate_State A} {w} (p : Pat w) (a : A) : A :=
  fold_left (fun a x => remove_var x a)  (pat_to_list p) a.

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

Definition remove_Ctx {A} `{Gate_State A} (Γ : Ctx) (a : A) : A :=
  fold_left (fun a x => remove_var x a) (Ctx_dom Γ) a.
Definition remove_OCtx {A} `{Gate_State A} (Γ : OCtx) (a : A) : A :=
  fold_left (fun a x => remove_var x a) (OCtx_dom Γ) a.


(* process_gate_pat g p a returns the pattern that is obtained from running the
   gate g with input pattern p and state a 
*)
Definition process_gate_pat {A w1 w2} `{Gate_State A} (g : Gate w1 w2) 
         : Pat w1 -> A -> Pat w2 :=
  match g with 
  | U _ | NOT     => fun p _ => p
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
  | U _  | NOT    => fun _ a => a
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


(* Ctx's and OCtx's can be used as state *)
Instance Ctx_State : Gate_State Ctx :=
  { get_fresh w  := do Γ ← get;
                    do _ ← put (Γ ++ [Some w]);
                    return_ (length Γ)
  ; remove_var := remove_at
  ; change_type x w Γ := update_at Γ x (Some w)
  }.

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


                         
Inductive Types_DB {w} (Γ : OCtx) : DeBruijn_Circuit w -> Prop :=
| types_db_output : forall p, Types_Pat Γ p -> Types_DB Γ (db_output p)
| types_db_gate   : forall Γ1 Γ2 w1 w2 (g : Gate w1 w2) p c,
                    Types_Pat Γ1 p ->
                    Types_DB (process_gate_state g p Γ) c ->
                    Γ == Γ1 ∙ Γ2 ->
                    Types_DB Γ (db_gate g p c)
                             
| types_db_lift   : forall Γ1 Γ2 Γ' p f,
                    Types_Pat Γ1 p ->
                    (forall b, Types_DB Γ' (f b)) ->
                    Γ == Γ1 ∙ Γ2 ->
                    Γ' = remove_pat p Γ -> (* Γ' is NOT Γ2 *)
                    Types_DB Γ (db_lift p f)
.

(*****************)
(* Substitutions *)
(*****************)

(* A substitution σ is a finite map from a variable x to a natural number i,
   where σ[i]=x. This formulation of finite maps is unique because when a
   variable is removed from the list, all variables above that one are shifted
   downward. *)
Definition substitution := list Var.



Record subst_state := Mk_subst_state
  { get_σ : substitution
  ; fresh : nat }. 

(* This should be used for HOAS *)
Instance subst_state_Gate_State : Gate_State subst_state :=
  { get_fresh w st := let x := fresh st in
                      let σ := get_σ st in
                      (x, Mk_subst_state (σ ++ [x]) (S x))
  ; remove_var x st := let σ' := List.remove Nat.eq_dec x (get_σ st) in
                        Mk_subst_state σ' (fresh st)
  ; change_type x w st := st
  }.

(* This should be used for internal substitution *)
(* the fresh variable generated for substitutions alone is the length of the
   list, as opposed to for subst_state, where the fresh variable is only
   assummed to be fresh in the state *)
(* I'm not sure this is right... *)
Instance substitution_Gate_State : Gate_State substitution :=
  { get_fresh w σ := let x := length σ in
                     (x, σ ++ [x]) 
  ; remove_var x σ := List.remove Nat.eq_dec x σ
  ; change_type x w σ := σ
  }.


Definition subst_var (σ : substitution) (x : Var) := lookup x σ.

(* Mapping relation *)

Notation "x ↦ y ∈ σ" := (σ !! y = Some x) (at level 20).
Definition in_dom x σ := x ↦ subst_var σ x ∈ σ.
Notation "x '∈_dom' σ" := (in_dom x σ) (at level 20).


Fixpoint subst_pat (σ : substitution) {w} (p : Pat w) : Pat w :=
  match p with
  | unit    => unit
  | qubit x => qubit (subst_var σ x)
  | bit   x => bit (subst_var σ x)
  | pair p1 p2 => pair (subst_pat σ p1) (subst_pat σ p2)
  end.

Fixpoint subst_db (σ : substitution) {w} (c : DeBruijn_Circuit w) 
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


(* Below are three possible definitions of subst_ctx *)

(* 1: *)
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

(* 2: *)
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

(* 3: *)


Definition subst_ctx' (Γ : Ctx) (σ : substitution) : Ctx :=
  fmap (index Γ) σ.
Definition subst_ctx (Γ : OCtx) σ : OCtx :=
  match Γ with
  | Valid Γ' => Valid (trim (subst_ctx' Γ' σ))
  | Invalid => Invalid
  end.


(*************************)
(* Scoping substitutions *)
(*************************)




Record WF_σ (Γ : OCtx) σ :=
  { pf_inj : Injective σ
  ; pf_valid : is_valid Γ
  ; pf_subset : forall x w,
                index Γ x = Some w ->
                In x σ
  }.

  

(*
Lemma inj_S : forall σ, Injective σ <-> Injective (fmap S σ).
Admitted.

*)




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

Lemma subst_nil' : forall Γ,
      subst_ctx' Γ [] = [].
Proof.
  intros. auto.
Qed.

(* PROPERTY:
    (subst_ctx σ Γ)[i] = Γ[σ[i]]
*)
Lemma valid_subst' : forall σ Γ i,
      index (subst_ctx' Γ σ) i = do x ← σ !! i;
                                 index Γ x.
Proof.
  induction σ; intros Γ i.
  * rewrite subst_nil'.
    rewrite index_empty.
    rewrite nth_nil.
    auto.
  * replace (subst_ctx' Γ (a :: σ)) with (index Γ a :: subst_ctx' Γ σ)
      by (unfold subst_ctx'; simpl; auto).
    destruct i as [ | i]; [simpl; auto | ].
    simpl.
    apply IHσ.
Qed.

Lemma valid_subst : forall Γ σ i,
    is_valid Γ ->
    index (subst_ctx Γ σ) i = do x ← σ !! i;
                              index Γ x.
Proof.  
  destruct Γ as [ | Γ]; intros.
  * invalid_contradiction.
  * unfold subst_ctx.
    rewrite index_trim.
    apply valid_subst'.
Qed.

  
Lemma subst_ctx'_nil : forall σ,
    empty_Ctx (subst_ctx' [] σ).
Proof.
  induction σ; unfold subst_ctx'.
  * constructor.
  * simpl. 
    rewrite nth_nil.
    simpl.
    constructor.
    apply IHσ.
Qed.

Lemma subst_ctx_nil : forall σ,
      subst_ctx ∅ σ = ∅.
Proof. 
  intros.
  unfold subst_ctx.
  f_equal.
  apply trim_empty.
  apply subst_ctx'_nil.
Qed.

Lemma subst_ctx_cons : forall Γ x σ,
    subst_ctx' Γ (x :: σ) = (index Γ x) :: (subst_ctx' Γ σ).
Proof.
  intros. unfold subst_ctx'. simpl. auto.
Qed.



(* Properties about the mapping x ↦ y ∈ σ *)

Lemma map_nil_inv : forall (x y : nat), ~ (x ↦ y ∈ []).
Proof.
  intros x y H.
  rewrite nth_nil in H.
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

(* properties about subst_ctx Γ σ where Γ is a singleton context *)

Lemma singleton_tail : forall σ w,
  ~ In 0 σ ->
  empty_Ctx (subst_ctx' [Some w] σ).
Proof.
  induction σ as [ | x σ]; intros w pf_in.
  * constructor.
  * simpl in pf_in.
    replace (subst_ctx' [Some w] (x :: σ))
      with (Contexts.index (Valid [Some w]) x :: subst_ctx' [Some w] σ)
      by (unfold subst_ctx'; simpl; auto).
    destruct x as [ | x].
    + absurd (0 = 0); auto.
    + replace (Contexts.index (Valid [Some w]) (S x)) with (None : option WType)
        by (simpl; rewrite nth_nil; auto).
      constructor.
      apply IHσ.
      auto.
Qed.


Lemma singleton_index_None : forall x w Γ,
        SingletonCtx x w Γ ->
        forall y, y <> x ->
        Contexts.index Γ y = None.
Proof.
  induction 1; intros; simpl.
  * destruct y; [contradiction | ].
    simpl. rewrite nth_nil; auto.
  * destruct y; [auto | ].
    simpl.
    apply IHSingletonCtx.
    auto.
Qed.
  


Lemma singleton_subst_empty : forall σ x w Γ,
      SingletonCtx x w Γ -> 
      ~ In x σ ->
      empty_Ctx (subst_ctx' Γ σ).
Proof.
  induction σ; intros x w Γ pf_singleton not_in.
  * rewrite subst_nil'.
    constructor.
  * rewrite subst_ctx_cons.
    simpl in not_in.
    apply Classical_Prop.not_or_and in not_in.
    destruct not_in.
    rewrite (singleton_index_None _ _ _ pf_singleton); auto.
    constructor.
    apply (IHσ _ _ _ pf_singleton); auto.
Qed.

  
Lemma subst_ctx_singleton : forall σ x w Γ,
    SingletonCtx x w Γ ->
    In x σ -> Injective σ ->
    SingletonOCtx (subst_var σ x) w (subst_ctx (Valid Γ) σ).
Proof.
  induction σ as [ | y σ]; intros x w Γ pf_signleton pf_in pf_inj.

  * contradiction.
  * Opaque subst_ctx.
    simpl.
    simpl in pf_in.
    destruct (Nat.eq_dec y x).
    + Transparent subst_ctx. 
      subst. rewrite Nat.eqb_refl.
      unfold subst_ctx.
      rewrite subst_ctx_cons.
      erewrite singleton_index; [ | eauto].
      simpl in *.
      destruct pf_inj.
      constructor.
      rewrite trim_empty; [constructor | ].
      eapply singleton_subst_empty; eauto.

    + replace (x =? y) with false
        by (apply eq_sym; apply (Nat.eqb_neq x y); auto).
      destruct pf_in; [contradiction | ].
      assert (IH : SingletonOCtx (subst_var σ x) w (subst_ctx Γ σ)).
      { apply IHσ; auto.
        inversion pf_inj; auto.
      }
      inversion IH; subst.
      unfold subst_ctx.
      rewrite subst_ctx_cons.

      rewrite (singleton_index_None x w Γ); auto.
      simpl.
      remember (trim (subst_ctx' Γ σ)) as Γ'.


      destruct Γ'; [inversion H1 | ].
      constructor.
      constructor.
      auto.
Qed.

Lemma subst_ctx_singleton' : forall σ x w Γ,
    SingletonCtx x w Γ ->
    In x σ -> Injective σ ->
    SingletonCtx (subst_var σ x) w (trim (subst_ctx' Γ σ)).
Proof.
  intros.
  assert (lem : SingletonOCtx (subst_var σ x) w (subst_ctx Γ σ)).
  { apply subst_ctx_singleton; auto.
  }
  inversion lem; auto.
Qed.

(* properties about the well-founded substitution relation *)

Lemma wf_merge_proj : forall σ Γ1 Γ2,
    WF_σ (Γ1 ⋓ Γ2) σ ->
    WF_σ Γ1 σ /\ WF_σ Γ2 σ.
Admitted.


(* Property about the substitution of a merged context *)

Lemma subst_ctx_merge : forall Γ1 Γ2 σ,
    subst_ctx (Γ1 ⋓ Γ2) σ = subst_ctx Γ1 σ ⋓ subst_ctx Γ2 σ.
Admitted.


(* Typing *)

Lemma types_subst_pat_db : forall Γ w (p : Pat w),
    Types_Pat Γ p ->
    forall Γ' σ, WF_σ Γ σ ->
    Γ' = subst_ctx Γ σ ->
    Types_Pat Γ' (subst_pat σ p).
Proof.
  intros Γ w p pf_p.
  induction pf_p; intros Γ' σ pf_wf pf_Γ'; subst.
  * rewrite subst_ctx_nil.
    constructor.
  * unfold subst_pat.
    constructor.
    destruct pf_wf.
    apply subst_ctx_singleton'; auto.
    eapply pf_subset0.
    apply singleton_index; eauto.
  * unfold subst_pat.
    constructor.
    destruct pf_wf.
    apply subst_ctx_singleton'; auto.
    eapply pf_subset0.
    apply singleton_index; eauto.
  * simpl.
    apply wf_merge_proj in pf_wf.
    destruct pf_wf as [pf_wf1 pf_wf2].
    econstructor;
      [ | | eapply IHpf_p1; [ auto | reflexivity]
          | eapply IHpf_p2; [ auto | reflexivity]].
    + Transparent subst_ctx.
      unfold subst_ctx.
      destruct (Γ1 ⋓ Γ2) as [ | Γ]; [dependent destruction i | ].
      apply valid_valid.
    + apply subst_ctx_merge.
Qed.

Lemma subst_ctx_valid : forall σ Γ,
  is_valid Γ ->
  is_valid (subst_ctx Γ σ).
Proof.
  induction σ as [ | x σ]; intros [ | Γ] pf_valid; try invalid_contradiction.
  * apply valid_valid.
  * unfold subst_ctx. 
    apply valid_valid.
Qed.

Lemma types_subst_db : forall w (c : DeBruijn_Circuit w) Γ ,
      Types_DB Γ c ->
      forall {σ Γ'}, WF_σ Γ σ ->
      Γ' = subst_ctx Γ σ ->
      Types_DB Γ' (subst_db σ c).
Proof.
  induction 1; intros σ Γ'' pf_wf pf_Γ''.
  * subst. simpl.
    constructor.
    eapply types_subst_pat_db; eauto.
  * subst. simpl. destruct H1; subst.
    apply wf_merge_proj in pf_wf; destruct pf_wf.
    econstructor.
    + eapply types_subst_pat_db; [eauto | auto | reflexivity ].
    + apply IHTypes_DB.
      - admit.
      - rewrite subst_ctx_merge.
        admit.
    + split; [apply subst_ctx_valid; auto | apply subst_ctx_merge].
  * subst. simpl. destruct H2; subst.
    apply wf_merge_proj in pf_wf; destruct pf_wf.
    econstructor.
    + eapply types_subst_pat_db; [eauto | auto | reflexivity].
    + intros b.
      apply H1; [ | reflexivity].
      admit.
    + split; [apply subst_ctx_valid; auto | apply subst_ctx_merge].
Admitted.     
 
(***************************************************************    


    
    
******************************************************)             
    


(***************)
(* composition *)
(***************)


(* produces the substitution context *)
  
    
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
  | db_output p   => subst_db (mk_subst p in_c') c'
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
Admitted.

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
    * admit.
    * simpl.
      admit.
  - simpl. subst.
    econstructor.
    * eauto.
    * eapply IHTypes_DB; [reflexivity | apply types_c' | ]. admit (*?*).
    * split; [apply valid_valid | ]. admit.
  - simpl. subst.
    econstructor.
    * eauto.
    * intros b. eapply H1; [ reflexivity | apply types_c' | reflexivity].
    * admit.
    * admit.
Admitted.




(******************************************)
(* Turning HOAS circuits into DB circuits *)
(******************************************)

Fixpoint hoas_to_db {w} (c : Circuit w) (σ : subst_state) : DeBruijn_Circuit w :=
  match c with
  | output p   => db_output (subst_pat (get_σ σ) p)
  | gate g p f => (* p' will be the input to f, so a hoas-level pat *)
                  let p' := process_gate_pat g p σ in
                  (* p0 is the db-pat corresponding to p *)
                  let p0 := subst_pat (get_σ σ) p in
                  (* σ' is the updated substitution,to go with p' *)
                  let σ' := process_gate_state g p σ in
                  db_gate g p0 (hoas_to_db (f p') σ')
  | lift p f   => let p0 := subst_pat (get_σ σ) p in
                  let σ' := remove_pat p σ in
                  db_lift (subst_pat (get_σ σ) p) (fun b => hoas_to_db (f b) σ')
  end.

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

Definition fresh_pat {A} `{Gate_State A} (w : WType) (a : A) : (Pat w) :=
  fst (get_fresh_pat w a).

Notation "σ_{ n }" := (seq 0 n) (at level 20).

Definition subst_state_at n := Mk_subst_state (σ_{n}) n.
Notation "st_{ n }" := (subst_state_at n) (at level 20).


Definition hoas_to_db_box {w1 w2} (B : Box w1 w2) : DeBruijn_Box w1 w2 :=
  match B with
  | box f => let (p,σ) := get_fresh_pat w1 (st_{0}) in
             db_box w1 (hoas_to_db (f p) σ)
  end.


Lemma fmap_S_seq : forall len start,
    fmap S (seq start len) = seq (S start) len.
Proof. 
  induction len as [ | len]; intros start; simpl in *; auto.
  f_equal.
  rewrite IHlen.
  auto.
Qed.
  

Lemma seq_S : forall len start, seq start (S len) = seq start len ++ [start + len].
Proof.
  induction len; intros; simpl.
  * f_equal. omega.
  * f_equal.
    replace (start + S len) with (S start + len)%nat by omega.
    rewrite <- IHlen.
    simpl.
    auto.
Qed.


Lemma fresh_pat_eq : forall w n,  
    get_fresh_pat w (σ_{n})
    = (fresh_pat w (σ_{n}), σ_{(n + size_WType w)})%core.
Proof.
  unfold fresh_pat.
  induction w; intros; simpl.
  * repeat autounfold with monad_db.
    replace (n+1)%nat with (S n) by omega.
    repeat rewrite seq_length.
    simpl.
    f_equal.
    rewrite <- seq_S.
    simpl.
    auto.

  * repeat autounfold with monad_db.
    replace (n+1)%nat with (S n) by omega.
    repeat rewrite seq_length.
    simpl.
    f_equal.
    rewrite <- seq_S.
    simpl.
    auto.
  * f_equal. f_equal. omega.
  * repeat autounfold with monad_db.
    rewrite IHw1.
    rewrite IHw2.
    simpl.
    f_equal.
    f_equal.
    omega.
Qed.

Lemma fresh_pat_eq' : forall w n,  
    get_fresh_pat w (st_{n})
    = (fresh_pat w (st_{n}), st_{(n + size_WType w)})%core.
Proof.
  unfold fresh_pat.
  induction w; intros; simpl.
  * repeat autounfold with monad_db.
    replace (n+1)%nat with (S n) by omega.
    repeat rewrite seq_length.
    simpl.
    f_equal.
    rewrite <- seq_S.
    simpl.
    auto.
  *repeat autounfold with monad_db.
    replace (n+1)%nat with (S n) by omega.
    repeat rewrite seq_length.
    simpl.
    f_equal.
    rewrite <- seq_S.
    simpl.
    auto.
  * replace (n + 0) with n by omega.
    auto.
  * repeat autounfold with monad_db.
    rewrite IHw1.
    rewrite IHw2.
    simpl.
    f_equal.
    rewrite Nat.add_assoc.
    auto.
Qed.    


Lemma subst_var_seq : forall len start x, x < len ->
                                         subst_var (seq start len) (start + x) = x.
Proof.
  induction len as [ | len]; intros start x pf; [inversion pf | ].
  * simpl.
    destruct x; auto.
    + rewrite Nat.add_0_r.
      rewrite Nat.eqb_refl.
      auto.
    + replace (start + S x =? start) with false.
      - replace (start + S x) with (S start + x) by omega.
        rewrite IHlen; auto.
        apply lt_S_n; auto.
      - apply eq_sym.
        apply Nat.eqb_neq.
        omega.
Qed.
Lemma subst_var_σ_n : forall n x, x < n ->
                                  subst_var (σ_{n}) x = x.
Proof.
  intros.
  replace x with (0 + x) at 1 by auto.
  apply subst_var_seq; auto.
Qed.



Lemma in_seq_S : forall len start x,
    In x (seq (S start) len) -> In x (seq start len).
Admitted.

Lemma in_seq_lt : forall len start x, In x (seq start len) -> x < start + len.    
Proof.
  induction len; intros start x pf; simpl in *.
  * contradiction.
  * destruct pf.
    + subst. omega.
    + apply lt_trans with (start + len); [ | omega].
      apply IHlen.
      apply in_seq_S.
      auto.
Qed.

Lemma in_σ_n_lt : forall n x, In x (σ_{n}) -> x < n.
Proof.
  intros.
  replace n with (0 + n) by auto.
  apply in_seq_lt.
  auto.
Qed.


Lemma subst_id : forall {w} (p : Pat w) Γ,
  Types_Pat Γ p ->
  forall n, WF_σ Γ (σ_{n}) ->
  subst_pat (σ_{n}) p = p.
Proof.
  induction 1; intros n pf_wf; simpl; auto.
  * rewrite subst_var_σ_n; auto.
    destruct pf_wf.
    apply in_σ_n_lt.
    eapply pf_subset0.
    apply singleton_index; eauto.
  * rewrite subst_var_σ_n; auto.
    destruct pf_wf.
    apply in_σ_n_lt.
    eapply pf_subset0.
    apply singleton_index; eauto.
  * subst. apply wf_merge_proj in pf_wf.
    destruct pf_wf.
    rewrite IHTypes_Pat1; auto.
    rewrite IHTypes_Pat2; auto.
Qed.



Fixpoint pat_to_ctx {w} (p : Pat w) : OCtx :=
  match p with
  | unit => ∅
  | qubit x => singleton x Qubit
  | bit x   => singleton x Bit
  | pair p1 p2 => pat_to_ctx p1 ⋓ pat_to_ctx p2
  end.


Lemma fresh_pat_typed : forall {w} (p : Pat w) (σ : subst_state),
      p = fresh_pat w σ ->
      Types_Pat (pat_to_ctx p) p.
Proof.
  unfold fresh_pat.
  induction w; intros p σ H.
  - simpl in H. subst. simpl. constructor. apply singleton_singleton.
  - simpl in H. subst. simpl. constructor. apply singleton_singleton.
  - simpl in *. subst. simpl. constructor.
  - simpl in *. subst. autounfold with monad_db.
    rewrite surjective_pairing with (p := get_fresh_pat w1 σ).
    rewrite surjective_pairing with (p := get_fresh_pat w2 _).
    simpl.
    econstructor; [ | reflexivity | | ].
    * admit. (* lemma *)
    * eapply IHw1; auto.
    * eapply IHw2; auto.
Admitted.


(* consequence of previous lemma *)
Lemma subst_fresh_id : forall {w},
    subst_pat (σ_{size_WType w}) (fresh_pat w (st_{0}))
    = fresh_pat w (st_{0}).
Proof.
  intros.
  eapply subst_id.
  eapply fresh_pat_typed; auto.
  admit. (* lemma *)
Admitted.

About hoas_to_db. About db_compose.
Print Types_Compose.
Require Import HOASCircuits. About compose.
        
Lemma hoas_to_db_compose_correct : forall {w w'}
                                          (c : Circuit w) (f : Pat w -> Circuit w')
    (types : Types_Compose c f) σ σ' σ'' p,
    σ' = remove_OCtx (ctx_c types) σ ->
    (p, σ'') = get_fresh_pat w σ' ->
    
      hoas_to_db (compose c f) σ
      = db_compose (size_OCtx (ctx_in types)) (hoas_to_db c σ) (hoas_to_db (f p) σ'').
Admitted.


Lemma singleton_dom : forall x w Γ, SingletonCtx x w Γ -> Ctx_dom Γ = [x].
Proof.
  induction 1; simpl; auto.
  rewrite IHSingletonCtx. auto.
Qed.

Definition process_pat {w} (p : Pat w) (σ : substitution) : substitution :=
  σ ++ pat_to_list p.


Lemma subst_process_pat : forall w (p : Pat w),
    subst_pat (pat_to_list p) p = fresh_pat w (st_{0}).
(*Proof.
  induction p; simpl; auto.
  * rewrite Nat.eqb_refl; auto.
  * rewrite Nat.eqb_refl; auto.
  * unfold fresh_pat. simpl. autounfold with monad_db.
*)

Lemma subst_dom : forall w (p : Pat w) Γ, Types_Pat Γ p -> 
      subst_pat (OCtx_dom Γ) p = fresh_pat w (st_{0}).
Proof.
  induction 1; simpl; auto.
  * unfold fresh_pat. simpl. erewrite singleton_dom; [ | eauto].
    simpl. rewrite Nat.eqb_refl. auto.
  * unfold fresh_pat. simpl. erewrite singleton_dom; [ | eauto].
    simpl. rewrite Nat.eqb_refl. auto.
  * 
admit.
Admitted.



Definition f {w} (p : Pat w) := output p. Print subst_state. Print length_OCtx.
Lemma wf_f : forall w (p1 p2 : Pat w) Γ1 Γ2 σ1 σ2,
             Types_Pat Γ1 p1 -> Types_Pat Γ2 p2 ->
             σ1 = Mk_subst_state (OCtx_dom Γ1) (length_OCtx Γ1) ->
             σ2 = Mk_subst_state (OCtx_dom Γ2) (length_OCtx Γ2) ->
             hoas_to_db (output p1) σ1 = hoas_to_db (output p2) σ2.
Proof.
  intros w p1 p2 Γ1 Γ2 σ1 σ2 types_p1 types_p2 H_σ1 H_σ2.
  simpl.
  subst; simpl.
  f_equal.
  repeat rewrite subst_dom; auto.
Qed.
      
Definition opaque_box {w w'} (f : Pat w -> Circuit w') :=
  forall (p1 p2 : Pat w) Γ1 Γ2 σ1 σ2,
             Types_Pat Γ1 p1 -> Types_Pat Γ2 p2 ->
             σ1 = Mk_subst_state (OCtx_dom Γ1) (length_OCtx Γ1) ->
             σ2 = Mk_subst_state (OCtx_dom Γ2) (length_OCtx Γ2) ->
             hoas_to_db (f p1) σ1 = hoas_to_db (f p2) σ2.
