Require Import Arith.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require Import Program.
Require Import Contexts.

Inductive Pat := var : Var -> Pat | unit | pair : Pat -> Pat -> Pat.

(* Dangerous to take this notation *)
Notation "a , b" := (Datatypes.pair a b) (at level 11, left associativity) : default_scope.
Notation "w1 , w2" := (pair w1 w2) (at level 11, left associativity) : circ_scope.
(* Notation "()" := unit : circ_scope. *)

(*
Parameter (Gate : Set).

Parameter (GateWType : Gate -> WType -> WType -> Set).
*)

Inductive WF_Pat : Ctx -> Pat -> WType -> Set :=
| wf_qubit : forall x ctx, SingletonCtx x Qubit ctx -> WF_Pat ctx (var x) Qubit
| wf_bit   : forall x ctx, SingletonCtx x Bit ctx -> WF_Pat ctx (var x) Bit
(*| wf_var  : forall x w ctx, SingletonCtx x w ctx -> WF_Pat ctx (var x) w*)
| wf_unit : forall ctx, EmptyCtx ctx -> WF_Pat ctx unit One
| wf_pair : forall g1 g2 g w1 w2 p1 p2, 
            MergeCtx g1 g2 g -> WF_Pat g1 p1 w1 -> WF_Pat g2 p2 w2 
         -> WF_Pat g (pair p1 p2) (Tensor w1 w2)
.

(*Definition wf_var W : {Γ : Ctx & {p : Pat & WF_Pat Γ p W}}.*)

(* p' ≼ p *)
Inductive Le_Pat : Pat -> Pat -> Set :=
| le_var : forall p x, Le_Pat p (var x)
| le_unit : Le_Pat unit unit
| le_pair : forall p1 p2 p1' p2',
            Le_Pat p1' p1 -> Le_Pat p2' p2 -> Le_Pat (pair p1' p2') (pair p1 p2)
.
Notation "p' ≼ p" := (Le_Pat p' p) (at level 50).

Definition Substitution := Var -> option Pat.
Fixpoint mk_subst {p' : Pat} {p : Pat} (pf : p' ≼ p) : Substitution :=
  match pf with
    | le_var p' y             => fun x => if beq_nat x y then Some p' else None
    | le_unit                 => fun x => None
    | le_pair _ _ _ _ pf1 pf2 => fun x => xor_option (mk_subst pf1 x) (mk_subst pf2 x)
  end.


Fixpoint subst_pat {p' : Pat} {p : Pat} (σ : p' ≼ p) (p0 : Pat) : Pat :=
  match p0 with
  | var y => match mk_subst σ y with
             | Some p0' => p0'
             | None     => var y
             end
  | unit  => unit
  | pair p1 p2 => pair (subst_pat σ p1) (subst_pat σ p2)
  end.

Definition Consistent_Subst {p' p} (σ : p' ≼ p) (p0 : Pat) (W : WType) : Set :=
  {Ω : Ctx & WF_Pat Ω (subst_pat σ p0) W}.
Definition Consistent_Ctx {p' p} (σ : p' ≼ p) (Γ : Ctx) := forall x {W} {pf : index Γ x = Some W},
           Consistent_Subst σ (var x) W.

Definition subst_ctx' {p' p} (σ : p' ≼ p) Ω (pf : Consistent_Ctx σ Ω) (x : Var) : option Ctx.
Proof.
  remember (index Ω x) as o; revert Heqo.
  refine (match o with 
          | None => fun _ => None
          | Some W => fun idx => _
          end).
  destruct (pf x W) as [Ω' H']; [ auto | ].
  exact (Some Ω').
Defined.  

Definition subst_ctx {p' p} (σ : p' ≼ p) Ω (pf : Consistent_Ctx σ Ω) : Ctx :=
  flatten_to_list 


Lemma wf_subst_pat : forall Ω p0 W, WF_Pat Ω p0 W
                  -> forall p' p (σ : p' ≼ p)