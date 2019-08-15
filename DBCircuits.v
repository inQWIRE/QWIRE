Require Import Prelim.
Require Import Monad.
Require Import Contexts.
Require Import HOASCircuits.

Open Scope circ_scope.
Global Opaque merge.

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


(**********************)  
(* De Bruijn Contexts *)
(**********************)

(* Produces a p and Γ such that Γ ⊢ p:Pat *)
Fixpoint get_fresh w (Γ : Ctx) : Pat w * Ctx:= 
  match w with
  | One   => (unit, [])
  | Bit   => (bit (length Γ), singleton (length Γ) w)
  | Qubit => (qubit (length Γ), singleton (length Γ) w)
  | w1 ⊗ w2 => let (p1, Γ1) := get_fresh w1 Γ in
              match Γ ⋓ Γ1 with
              | Invalid  => (dummy_pat, dummy_ctx)
              | Valid Γ' => let (p2, Γ2) := get_fresh w2 Γ' in
                           match Γ1 ⋓ Γ2 with
                           | Invalid   => (dummy_pat, dummy_ctx)
                           | Valid Γ'' => ((pair p1 p2), Γ'')
                           end
              end
  end.

Definition get_fresh_pat w Γ : Pat w := fst (get_fresh w Γ).
Definition get_fresh_state w Γ : Ctx := snd (get_fresh w Γ).

Lemma get_fresh_split : forall w Γ, 
  get_fresh w Γ = (get_fresh_pat w Γ, get_fresh_state w Γ).
Proof. intros. rewrite (surjective_pairing (get_fresh w Γ)). easy. Qed.

Lemma get_fresh_merge_valid : forall w Γ Γ0 (p : Pat w),
  (p, Γ) = get_fresh w Γ0 ->
  is_valid (Γ0 ⋓ Γ).
Proof.
  induction w.
  - intros Γ Γ0 p H.
    simpl in H.
    inversion H.
    rewrite merge_singleton_append.
    validate.
  - intros Γ Γ0 p H.
    simpl in H.
    inversion H.
    rewrite merge_singleton_append.
    validate.
  - intros Γ Γ0 p H.
    simpl in H.
    inversion H.
    rewrite merge_nil_r.
    validate.
  - intros Γ Γ0 p H.
    simpl in H.
    destruct (get_fresh w1 Γ0) as [p1 Γ1] eqn:E1.
    symmetry in E1. specialize (IHw1 _ _ _ E1).
    destruct (Γ0 ⋓ Γ1) as [|Γ01] eqn:EΓ01; try invalid_contradiction.
    destruct (get_fresh w2 Γ01) as [p2 Γ2] eqn:E2.
    symmetry in E2. specialize (IHw2 _ _ _ E2).
    rewrite <- EΓ01 in IHw2. rewrite <- merge_assoc in IHw2.
    destruct (Γ1 ⋓ Γ2) as [|Γ12] eqn:EΓ12; try invalid_contradiction.
    inversion H; subst.
    easy.
Qed.
    
Lemma get_fresh_typed : forall w Γ0 p Γ,
  (p, Γ) = get_fresh w Γ0 ->
  Γ ⊢ p:Pat.
Proof.
  induction w; intros Γ0 p Γ E.
  - simpl in E. inversion E. econstructor. apply singleton_singleton.
  - simpl in E. inversion E. econstructor. apply singleton_singleton.
  - simpl in E. inversion E. constructor.
  - simpl in E.
    destruct (get_fresh w1 Γ0) as [p1 Γ1] eqn:E1.
    symmetry in E1. specialize (get_fresh_merge_valid _ _ _ _ E1) as V1.
    destruct (Γ0 ⋓ Γ1) as [|Γ01] eqn:EΓ01; try invalid_contradiction.
    destruct (get_fresh w2 Γ01) as [p2 Γ2] eqn:E2.
    symmetry in E2. specialize (get_fresh_merge_valid _ _ _ _ E2) as V2.
    rewrite <- EΓ01 in V2. rewrite <- merge_assoc in V2.
    destruct (Γ1 ⋓ Γ2) as [|Γ12] eqn:EΓ12; try invalid_contradiction.
    inversion E; subst.
    rewrite <- EΓ12 in *.
    econstructor; try reflexivity.
    validate.
    eapply IHw1. apply E1.
    eapply IHw2. apply E2.
Qed.
    
(* Creates the same pattern as get_fresh, but returns Γ ⋓ get_fresh_state Γ *)

(* Approach using get_fresh:
Definition add_fresh w (Γ : Ctx) : Pat w * Ctx := 
  let (p, Γ') := get_fresh w Γ in  
  match Γ ⋓ Γ' with
  | Invalid => (dummy_pat _, dummy_ctx) (* inaccessible branch *)
  | Valid Γ'' => (p, Γ'')
  end.
*)

(* Direct, concatenation based approach *)
Fixpoint add_fresh w (Γ : Ctx) : Pat w * Ctx:= 
  match w with
  | One     => (unit, Γ)
  | Bit     => (bit (length Γ), Γ ++ [Some Bit])
  | Qubit   => (qubit (length Γ), Γ ++ [Some Qubit])
  | w1 ⊗ w2 => let (p1, Γ') := add_fresh w1 Γ in
              let (p2, Γ'') := add_fresh w2 Γ' in
              ((pair p1 p2), Γ'')
  end.

Definition add_fresh_pat w (Γ : Ctx) : Pat w := fst (add_fresh w Γ).
Definition add_fresh_state w (Γ : Ctx) : Ctx := snd (add_fresh w Γ).

Lemma add_fresh_split : forall w Γ, 
  add_fresh w Γ = (add_fresh_pat w Γ, add_fresh_state w Γ).
Proof. intros. rewrite (surjective_pairing (add_fresh w Γ)). easy. Qed.

Lemma add_fresh_state_merge : forall w (Γ Γ' : Ctx), 
    Γ' = add_fresh_state w Γ ->
    Valid Γ' = Γ ⋓ get_fresh_state w Γ.
Proof.
  induction w; intros Γ Γ' H.
  - unfold add_fresh_state, get_fresh_state in *.
    unfold add_fresh, get_fresh in *.
    simpl in *.
    rewrite merge_singleton_append.
    subst. easy.
  - unfold add_fresh_state, get_fresh_state in *.
    unfold add_fresh, get_fresh in *.
    simpl in *.
    rewrite merge_singleton_append.
    subst. easy.
  - unfold add_fresh_state, get_fresh_state in *.
    unfold add_fresh, get_fresh in *.
    simpl in *.
    rewrite merge_nil_r.
    subst; easy.
  - unfold add_fresh_state, get_fresh_state in *.
    specialize (IHw1 Γ (snd (add_fresh w1 Γ)) eq_refl).
    simpl in *.
    destruct (get_fresh w1 Γ) as [p1 Γ1] eqn:E1.
    simpl in *.
    destruct (Γ ⋓ Γ1) as [|Γ1'] eqn:E1'. invalid_contradiction.
    specialize (IHw2 Γ1' (snd (add_fresh w2 Γ1')) eq_refl).
    simpl in *.
    destruct (get_fresh w2 Γ1') as [p2 Γ2] eqn:E2.
    simpl in *.
    rewrite <- E1' in IHw2. rewrite <- merge_assoc in IHw2.
    destruct (Γ1 ⋓ Γ2) as [|Γ2'] eqn:E12. invalid_contradiction.
    simpl in *.
    rewrite H.
    simpl in *. inversion IHw1. subst.
    destruct (add_fresh w1 Γ) as [p1' Γ1''] eqn:A1.
    destruct (add_fresh w2 Γ1'') as [p2' Γ2''] eqn:A2.
    rewrite add_fresh_split in A2. inversion A2.
    simpl in *.
    rewrite <- IHw2.
    easy.
Qed.    


Lemma add_fresh_pat_eq : forall w Γ, add_fresh_pat w Γ = get_fresh_pat w Γ.
Proof.
  induction w; intros Γ; trivial.
  unfold add_fresh_pat, get_fresh_pat in *; simpl.
  
  destruct (add_fresh w1 Γ) as [pa1 Γa1] eqn:Ea1.
  destruct (add_fresh w2 Γa1) as [pa2 Γa2] eqn:Ea2.
  destruct (get_fresh w1 Γ) as [pg1 Γg1] eqn:Eg1.
  specialize (get_fresh_merge_valid _ _ _ _ (eq_sym Eg1)) as V1.
  destruct V1 as [Γ1' M1]. rewrite M1.
  destruct (get_fresh w2 Γ1') as [pg2 Γg2] eqn:Eg2.
  specialize (get_fresh_merge_valid _ _ _ _ (eq_sym Eg2)) as V2.
  rewrite <- M1 in V2. rewrite <- merge_assoc in V2.
  destruct (Γg1 ⋓ Γg2) as [|Γ2']; try invalid_contradiction.
  simpl.
  rewrite add_fresh_split, get_fresh_split in *.
  inversion Ea1. inversion Ea2.
  inversion Eg1. inversion Eg2.
  unfold get_fresh_pat, add_fresh_pat in *.
  rewrite IHw1 in *.
  rewrite IHw2 in *.
  apply f_equal2; trivial.
  symmetry in H1, H3.
  apply add_fresh_state_merge in H1.
  apply add_fresh_state_merge in H3.
  congruence.
Qed.

Lemma add_fresh_typed : forall w w0 (p : Pat w) (p0 : Pat w0) Γ Γ0,
  (p, Γ) = add_fresh w Γ0 ->
  Γ0 ⊢ p0:Pat ->
  Γ ⊢ (pair p0 p):Pat.
Proof.
  intros w w0 p p0 Γ Γ0 H H0.
  rewrite add_fresh_split in H.
  inversion H.
  erewrite add_fresh_state_merge; [|reflexivity].
  econstructor.
  3: apply H0.
  2: reflexivity.
  eapply get_fresh_merge_valid. 
  rewrite get_fresh_split. reflexivity.
  rewrite add_fresh_pat_eq.
  eapply get_fresh_typed.
  rewrite get_fresh_split. reflexivity.
Qed.

Lemma add_fresh_typed_empty : forall w (p : Pat w) Γ,
  (p, Γ) = add_fresh w [] ->
  Γ ⊢ p:Pat.
Proof.
  (* I'm sure the direct route is easy, but let's use our general case *)
  intros w p Γ H.
  specialize (add_fresh_typed _ _ _ _ _ _ H types_unit) as TP.
  dependent destruction TP.
  inversion TP1; subst.
  rewrite merge_nil_l in e. subst.
  easy.
Qed.

Lemma fresh_wtype : forall (w : WType) (Γ : Ctx), add_fresh_state w Γ = Γ ++ (add_fresh_state w []).
Proof.
  intros. generalize dependent Γ.
  induction w; unfold add_fresh_state; simpl; try reflexivity; intros.
  - induction Γ; simpl; try reflexivity.
    rewrite <- IHΓ. reflexivity.
  - repeat rewrite add_fresh_split. simpl.
    replace (add_fresh_state w2 (add_fresh_state w1 [])) with ((add_fresh_state w1 []) ++ (add_fresh_state w2 [])) by (rewrite <- IHw2; reflexivity).
    rewrite IHw2. rewrite IHw1. rewrite app_assoc. reflexivity.
Qed.


Definition remove_var (v : Var) (Γ : Ctx) : Ctx := trim (update_at Γ v None).  

Definition change_type (v : Var) (w : WType) (Γ : Ctx) := update_at Γ v (Some w).

Fixpoint ctx_dom (Γ : Ctx) :=
  match Γ with
  | [] => []
  | Some w :: Γ' => 0 :: fmap S (ctx_dom Γ')
  | None :: Γ' => fmap S (ctx_dom Γ')
  end.

Definition remove_pat {w} (p : Pat w) (Γ : Ctx) : Ctx :=
  fold_left (fun a x => remove_var x a)  (pat_to_list p) Γ.

Definition process_gate {w1 w2} (g : Gate w1 w2) 
         : Pat w1 -> Ctx -> Pat w2 * Ctx :=
  match g with 
  | U _ | BNOT | measQ => fun p st => (p,st)
  | init0 | init1      => fun _ st => add_fresh Qubit st
  | new0 | new1        => fun p st => add_fresh Bit st
  | meas               => fun p st => match p with 
                                   | qubit v => (bit v, change_type v Bit st) 
                                  end
  | discard | assert0 | assert1  => fun p st => (unit, remove_pat p st)
  end. 

Definition process_gate_pat {w1 w2} (g : Gate w1 w2) 
         : Pat w1 -> Ctx -> Pat w2 := fun p st => fst (process_gate g p st).

Definition process_gate_state {w1 w2} (g : Gate w1 w2) 
         : Pat w1 -> Ctx -> Ctx := fun p st => snd (process_gate g p st).
                                         
(**********)
(* Typing *)
(**********)


(* Although we use ordinary (nominal) contexts for typing, it should be the case
that they are always "minimal", meaning that the list is equivalent to a list of
WTypes (as opposed to list (option WType)). However, because of context
splitting, this will only be enforcable at the top level. *)

                         
Inductive Types_DB {w} (Γ : Ctx) : DeBruijn_Circuit w -> Prop :=
| types_db_output : forall p, Types_Pat Γ p -> Types_DB Γ (db_output p)
| types_db_gate   : forall (Γ1 Γ2 : Ctx) w1 w2 (g : Gate w1 w2) p c,
                    Types_Pat Γ1 p ->
                    Types_DB (process_gate_state g p Γ) c ->
                    Γ ⩵ Γ1 ∙ Γ2 ->
                    Types_DB Γ (db_gate g p c)
                             
| types_db_lift   : forall (Γ1 Γ2 Γ' : Ctx) p f,
                    Types_Pat Γ1 p ->
                    (forall b, Types_DB Γ' (f b)) ->
                    Γ ⩵ Γ1 ∙ Γ2 ->
                    Γ' = remove_pat p Γ -> (* Γ' is NOT Γ2 *)
                    Types_DB Γ (db_lift p f)
.


(*****************)
(* Substitutions *)
(*****************)

Fixpoint lookup_maybe (x : nat) (ls : list nat) : option nat :=
  match ls with
  | [] => None
  | y :: ls' => if x =? y then Some 0 else fmap S (lookup_maybe x ls')
  end.

(* if Γ has n elements occuring before index x, then maps_in_Ctx x Γ = n *)
Fixpoint maps_to (x : nat) (Γ : Ctx) : option nat :=
  match x, Γ with
  | _,    []           => None
  | 0,    None   :: _  => None
  | 0,    Some _ :: _  => Some 0
  | S x', Some _ :: Γ' => fmap S (maps_to x' Γ')
  | S x', None   :: Γ' => maps_to x' Γ'
  end.

Lemma maps_to_singleton : forall v W, maps_to v (singleton v W) = Some O.
Proof. induction v; auto. Qed.

Lemma maps_to_repeat : forall v n W, v < n ->
                                maps_to v (repeat (Some W) n) = Some v.
Proof.
  induction v; intros n W L; auto.
  - destruct n; try lia. easy.
  - destruct n; try lia.
    simpl. rewrite IHv by lia. easy.
Qed.

Definition subst_var (Γ : Ctx) (x : Var) : Var :=
  match maps_to x Γ with
  | Some y => y
  | None => 0
  end.
 
Fixpoint subst_pat (Γ : Ctx) {w} (p : Pat w) : Pat w :=
  match p with
  | unit    => unit
  | qubit x => qubit (subst_var Γ x)
  | bit   x => bit (subst_var Γ x)
  | pair p1 p2 => pair (subst_pat Γ p1) (subst_pat Γ p2)
  end.

Fixpoint subst_db (Γ : Ctx) {w} (c : DeBruijn_Circuit w) 
  : DeBruijn_Circuit w :=
  match c with
  | db_output p    => db_output (subst_pat Γ p)
  | db_gate g p c' => let p' := subst_pat Γ p in
                     let Γ' := process_gate_state g p Γ in
                     db_gate g p' (subst_db Γ' c')
  | db_lift p f    => let p' := subst_pat Γ p in
                     let Γ' := remove_pat p Γ in
                     db_lift p' (fun b => subst_db Γ' (f b))
  end.


(* Mapping relation *)

(* Not sure if we need things from here on *)
Fixpoint flatten_ctx (Γ : Ctx) :=
  match Γ with
  | []           => []
  | Some w :: Γ' => Some w :: flatten_ctx Γ'
  | None   :: Γ' => flatten_ctx Γ'
  end.

Definition flatten_octx Γ :=
  match Γ with
  | Valid Γ' => Valid (flatten_ctx Γ')
  | Invalid  => Invalid
  end.

Lemma SingletonCtx_dom : forall x w Γ,
      SingletonCtx x w Γ ->
      ctx_dom Γ = [x].
Proof.
  induction 1; simpl; auto.
  rewrite IHSingletonCtx.
  auto.
Qed.

Lemma SingletonCtx_flatten : forall x w Γ,
      SingletonCtx x w Γ ->
      flatten_ctx Γ = [Some w].
Proof. induction 1; auto. Qed.

(* assumes idxs is sorted *)
Fixpoint remove_indices (Γ : Ctx) (idxs : list nat) : Ctx :=
  match Γ with
  | [] => []
  | o :: Γ' => match idxs with
              | []           => Γ
              | 0 :: idxs'   => remove_indices Γ' (map pred idxs')
              | S i :: idxs' => o :: remove_indices Γ' (map pred idxs)
              end
  end.

Fixpoint get_nones (Γ : Ctx) : list nat := 
  match Γ with
  | [] => [] 
  | None :: Γ' => 0 :: (map S (get_nones Γ'))
  | Some w :: Γ' => map S (get_nones Γ')
  end.

Lemma remove_indices_empty : forall Γ, remove_indices Γ [] = Γ.
Proof. induction Γ; auto. Qed.

Lemma remove_indices_merge : forall (Γ Γ1 Γ2 : Ctx) idxs, 
  Γ ⩵ Γ1 ∙ Γ2 ->
  remove_indices Γ idxs ⩵ (remove_indices Γ1 idxs) ∙ (remove_indices Γ2 idxs).
Proof.
  intros.
  gen idxs.
  apply merge_fun_ind in H.
  dependent induction H; intros.
  - split. validate.
    rewrite merge_nil_l.
    easy.
  - split. validate.
    rewrite merge_nil_r.
    easy.
  - simpl.
    destruct idxs; [|destruct n].
    + apply merge_ind_fun.
      constructor; easy.
    + apply IHmerge_ind; easy.
    + simpl.
      apply merge_ind_fun.
      constructor.
      easy.
      apply merge_fun_ind.
      apply IHmerge_ind; easy.
Qed.

Lemma map_unmap : forall l, map pred (map S l) = l.
Proof.  induction l; intros; auto. simpl. rewrite IHl. easy. Qed.

Lemma remove_flatten : forall Γ, remove_indices Γ (get_nones Γ) = flatten_ctx Γ.
Proof.
  induction Γ; trivial.
  simpl.
  destruct a.
  - destruct (get_nones Γ) eqn:E.
    + simpl.
      rewrite <- IHΓ.
      rewrite remove_indices_empty.
      easy.
    + simpl.
      rewrite <- IHΓ.
      rewrite map_unmap.
      easy.
  - rewrite map_unmap.
    easy.
Qed.

Fixpoint hoas_to_db {w} Γ (c : Circuit w) : DeBruijn_Circuit w :=
  match c with
  | output p   => db_output (subst_pat Γ p)
  | gate g p f =>  (* p0 is the db-pat corresponding to p *)
                  let p0 := subst_pat Γ p in
                  (* p' and Γ' are the updated DB pattern and context *)
                  let (p',Γ') := process_gate g p Γ in
                  db_gate g p0 (hoas_to_db Γ' (f p'))
  | lift p f   =>  let p0 := subst_pat Γ p in
                  let Γ' := remove_pat p Γ in
                  db_lift p0 (fun b => hoas_to_db Γ' (f b))
  end.

Proposition hoas_to_db_typed : forall (Γ : Ctx) w (c : Circuit w),
      Γ ⊢ c :Circ ->
      Types_DB (flatten_ctx Γ) (hoas_to_db Γ c).
Proof.
  induction 1.
  * simpl. constructor. (* apply subst_pat_typed. subst. auto. *) admit.
  * simpl. admit.
  * simpl. admit.
Abort.

Definition hoas_to_db_box {w1 w2} (B : Box w1 w2) : DeBruijn_Box w1 w2 :=
  match B with
  | box f => let (p,Γ) := add_fresh w1 [] in
             db_box w1 (hoas_to_db Γ (f p))
  end.

Eval compute in (hoas_to_db_box (box (fun (p : Pat (Qubit ⊗ Bit)) => output p))).

(* Not sure we need these anymore *)
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
  * f_equal. lia.
  * f_equal.
    replace (start + S len) with (S start + len)%nat by lia.
    rewrite <- IHlen.
    simpl.
    auto.
Qed.

