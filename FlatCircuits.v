Require Import Contexts.
Require Import HOASCircuits.
Require Import Program.

Open Scope circ_scope.
Inductive Flat_Circuit : OCtx -> WType -> Set :=
| flat_output : forall {ctx ctx' w} {pf : ctx' = ctx}, 
                Pat ctx w -> Flat_Circuit ctx' w
| flat_gate   : forall {ctx ctx1 ctx1' ctx2 ctx2'} {w1 w2 w}
           {m1 : ctx1' = ctx1 ⋓ ctx} {m2 : ctx2' = ctx2 ⋓ ctx}
           {v1 : is_valid ctx1'} {v2 : is_valid ctx2'},
           Gate w1 w2
        -> Pat ctx1 w1
        -> Pat ctx2 w2
        -> Flat_Circuit ctx2' w
        -> Flat_Circuit ctx1' w
| flat_lift  : forall {ctx1 ctx2 ctx w w'}
         {m : ctx = ctx1 ⋓ ctx2} {v : is_valid ctx},
         Pat ctx1 w
      -> (interpret w -> Flat_Circuit ctx2 w')
      -> Flat_Circuit ctx w'
.

Fixpoint fresh_var (Γ_in : Ctx) : nat :=
  match Γ_in with
  | [] => 0
  | Some _ :: Γ_in' => S (fresh_var Γ_in')
  | None   :: _     => 0
  end.
Definition fresh_var_o (Γ_in : OCtx) : nat := 
  match Γ_in with
  | Invalid => 0
  | Valid Γ' => fresh_var Γ'
  end.

Lemma valid_fresh_var : forall (Γ : Ctx) W, 
      is_valid (Γ ⋓ singleton (fresh_var Γ) W).
Proof.
  induction Γ as [ | o Γ]; intros W.
  - apply valid_valid.
  - destruct o.
    * destruct (IHΓ W) as [Γ' H]. simpl in *.
      rewrite H. apply valid_valid.
    * assert (H : Valid Γ ⋓ ∅ = Valid Γ). { apply merge_nil_r. }
      simpl in *. rewrite H. apply valid_valid.
Qed.


Lemma disjoint_fresh_var_o : forall Γ W, Disjoint Γ (singleton (fresh_var_o Γ) W).
Proof.
  destruct Γ as [ | Γ]; intros W.
  * exact I.
  * unfold Disjoint. apply valid_fresh_var.
Qed.

Fixpoint fresh_ctx (Γ_in : OCtx) (W : WType) : OCtx :=
  match W with
  | One   => ∅
  | Qubit => singleton (fresh_var_o Γ_in) Qubit
  | Bit   => singleton (fresh_var_o Γ_in) Bit
  | W1 ⊗ W2 => let Γ1 := fresh_ctx Γ_in W1 in
               let Γ2 := fresh_ctx (Γ_in ⋓ Γ1) W2 in
               Γ1 ⋓ Γ2
  end.


Lemma fresh_ctx_merge_valid : forall W Γ_in, is_valid Γ_in -> is_valid (Γ_in ⋓ fresh_ctx Γ_in W).
Proof.
  induction W; intros Γ_in pf_Γ_in; simpl.
  - apply disjoint_valid; [ | auto | apply valid_valid].
    apply disjoint_fresh_var_o.
  - apply disjoint_valid; [ | auto | apply valid_valid].
    apply disjoint_fresh_var_o.
  - validate.
  - rewrite merge_assoc.
    apply IHW2. apply IHW1. auto.
Qed.

Lemma fresh_ctx_valid : forall W Γ_in, is_valid Γ_in -> is_valid (fresh_ctx Γ_in W).
Proof.
  intros.
  apply (fresh_ctx_merge_valid W) in H.
  apply valid_split_basic in H. 
  destruct H; auto.
Qed.


Program Fixpoint fresh_pat (Γ_in : OCtx) (W : WType) (pf : is_valid Γ_in) : Pat (fresh_ctx Γ_in W) W :=
  match W with
  | One     => unit
  | Qubit   => qubit (fresh_var_o Γ_in) _ _
  | Bit     => bit (fresh_var_o Γ_in) _ _
  | W1 ⊗ W2 => let p1 := fresh_pat Γ_in W1 _ in
               let p2 := fresh_pat (Γ_in ⋓ fresh_ctx Γ_in W1) W2 _ in
               pair _ _ _ _ _ _ _ p1 p2
  end.
Next Obligation. apply singleton_singleton. Defined.
Next Obligation. apply singleton_singleton. Defined.
Next Obligation.  apply fresh_ctx_merge_valid; auto. Defined.
Next Obligation.
  assert (H : is_valid (Γ_in ⋓ fresh_ctx Γ_in W1 ⋓ fresh_ctx (Γ_in ⋓ fresh_ctx Γ_in W1) W2))
    by (repeat apply fresh_ctx_merge_valid; auto).
  validate.
Defined.

(* 
Program Fixpoint fresh_pat (Γ_in : OCtx) (W : WType) (pf : is_valid Γ_in)
                         : {Γ_out : OCtx & is_valid Γ_out * Disjoint Γ_in Γ_out * Pat Γ_out W}%type :=
  match W with
  | One     => existT _ ∅ (_, unit)
  | Qubit   => let x := fresh_var_o Γ_in in existT _ (singleton x Qubit) (_,qubit x _ _)
  | Bit     => let x := fresh_var_o Γ_in in existT _ (singleton x Bit)   (_,bit x _ _)
  | W1 ⊗ W2 => 
    match fresh_pat Γ_in W1 _ with
    | existT _ Γ1 (disj1,p1) => 
      match fresh_pat (Γ_in ⋓ Γ1) W2 _ with
      | existT _ Γ2 (disj2,p2) => existT _ (Γ1 ⋓ Γ2) (_,pair _ _ _ _ _ _ _ p1 p2)
      end
    end
  end.
Next Obligation. split; [ apply valid_valid | apply disjoint_nil_r]. Defined.
Next Obligation. split; [ apply valid_valid | apply disjoint_fresh_var_o]. Defined.
Next Obligation. apply singleton_singleton. Defined.
Next Obligation. split; [ apply valid_valid | apply disjoint_fresh_var_o]. Defined.
Next Obligation. apply singleton_singleton. Defined.
Next Obligation. rename x into Γ1. apply disjoint_valid; auto. Defined.
Next Obligation. rename x0 into Γ1. rename x into Γ2.
                 split; [ apply disjoint_valid
                        | apply disjoint_merge]; auto;
                 [ apply disjoint_split with (Γ1 := Γ_in) 
                 | apply disjoint_split with (Γ2 := Γ1) ]; auto.
Defined.
Next Obligation. rename x0 into Γ1. rename x into Γ2.
                 apply disjoint_valid; auto.
                 apply disjoint_split with (Γ1 := Γ_in); auto.
Defined.
*)

(* Simpler modular version of fresh_pat *)

Definition from_HOAS {Γ W} (c : Circuit Γ W) : Flat_Circuit Γ W.
Proof. 
  induction c as [ Γ Γ' W eq p 
                 | Γ Γ1 Γ1' W1 W2 W valid1 eq1 g p1 f 
                 | Γ1 Γ2 Γ W W' valid eq p f ].
  - refine (flat_output p); auto.
  - assert (valid0 : is_valid Γ). 
    {
      destruct valid1 as [Γ0' valid1]. subst.
      destruct Γ as [ | Γ]; [rewrite merge_I_r in eq1; inversion eq1 | ].
      apply valid_valid.
    }
    set (p2 := fresh_pat Γ W2 valid0).
    assert (valid2' : is_valid (Γ ⋓ fresh_ctx Γ W2)).
    { apply fresh_ctx_merge_valid; auto. }
    assert (c' : Flat_Circuit (fresh_ctx Γ W2 ⋓ Γ) W).
    {
      apply H with (Γ2 := fresh_ctx Γ W2); auto.
      validate.
    }
    refine (flat_gate g p1 p2 c'); auto. auto. validate.
  - refine (flat_lift p H); auto. 
Defined.


Inductive Flat_Box : WType -> WType -> Set :=
| flat_box : forall {w1 w2} {ctx},
             Pat ctx w1 -> Flat_Circuit ctx w2 -> Flat_Box w1 w2
.
Definition from_HOAS_Box {W1 W2} (b : Box W1 W2) : Flat_Box W1 W2.
  destruct b as [W1 W2 b].
(*  destruct (fresh_pat ∅ W1) as [Γ [[valid_Γ _] p]]; [apply valid_valid | ].*)
  set (p := fresh_pat ∅ W1 (valid_valid [])).
  apply (flat_box p (from_HOAS (b _ p))).
Defined.

Close Scope circ_scope.

(* *)