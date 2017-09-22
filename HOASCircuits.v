Require Export Contexts.
Require Import Arith.
Require Import List.
Import ListNotations.

Inductive Circuit : Set :=
| output : Pat -> Circuit
| gate   : forall {w1 w2}, Gate w1 w2 ->  Pat -> (Pat -> Circuit) -> Circuit
| lift   : Pat -> (bool -> Circuit) -> Circuit 
.

(* Subst x |-> p in p' *) 
Fixpoint subst_pat (x : Var) (p p' : Pat) : Pat := 
  match p' with
  | unit => unit 
  | var y => if x =? y then p else var y (* Is this the kind of check we want? *)
  | pair p1 p2 => pair (subst_pat x p p1) (subst_pat x p p2)
  end.

(* Ensure that this is capture-avoiding! *)
Fixpoint subst (x : Var) (p : Pat) (C : Circuit) : Circuit := 
  match C with 
  | output p' => output (subst_pat x p p')
  | gate g p' C => gate g (subst_pat x p p') (fun y => subst x p (C y))
  | lift v C => lift v (fun b => subst x p (C b))
  | let_unit p' C => let_unit (subst_pat x p p') (subst x p C)
  | let_pair p' C => let_pair (subst_pat x p p') (fun y z => subst x p (C y z))
  end.

Inductive Types_Circuit : OCtx -> Circuit -> WType -> Set :=
| types_output : forall {Γ Γ' W p} {pf : Γ = Γ'}, Types_Pat Γ p W -> 
                                             Types_Circuit Γ' (output p) W
| types_gate : forall {Γ Γ1 Γ1' Γ2 Γ2' p1 p2 W1 W2 W C} {g : Gate W1 W2} 
                 {V1: is_valid Γ1'} {M1: Γ1' = Γ1 ⋓ Γ} 
                 {V2: is_valid Γ2'} {M2: Γ2' = Γ2 ⋓ Γ},
               Types_Pat Γ1 p1 W1 ->
               Types_Pat Γ2 p2 W2 ->
               Types_Circuit Γ2' (C v) W ->
               Types_Circuit Γ1' (gate g p C) W  
.

Inductive Box : Set := box : (Pat -> Circuit) -> Box.

Definition unbox (b : Box)  (p : Pat) : Circuit := 
  match b with
  box c => c p
  end.

Fixpoint compose (c : Circuit) (f : Pat -> Circuit) : Circuit :=
  match c with 
  | output p     => f p
  | gate g p c'  => gate g p (fun p' => compose (c' p') f)
  | lift p c'    => lift p (fun bs => compose (c' bs) f)
  end.

(* Prevent compute from unfolding important fixpoints *)
Opaque merge.
Opaque Ctx.
Opaque is_valid.

Ltac validate :=
  repeat ((*idtac "validate";*) match goal with
  (* Pattern contexts are valid *)
  | [p : Pat ?Γ ?W |- _ ]             => apply pat_ctx_valid in p
  (* Solve trivial *)
  | [|- is_valid ∅ ]                  => apply valid_empty
  | [H : is_valid ?Γ |- is_valid ?Γ ] => exact H
  | [H: is_valid (?Γ1 ⋓ ?Γ2) |- is_valid (?Γ2 ⋓ ?Γ1) ] => rewrite merge_comm; exact H
  (* Remove nils *)
  | [|- context [∅ ⋓ ?Γ] ]             => rewrite (merge_nil_l Γ)
  | [|- context [?Γ ⋓ ∅] ]             => rewrite (merge_nil_r Γ)
  (* Reduce hypothesis to binary disjointness *)
  | [H: is_valid (?Γ1 ⋓ (?Γ2 ⋓ ?Γ3)) |- _ ] => rewrite (merge_assoc Γ1 Γ2 Γ3) in H
  | [H: is_valid (?Γ1 ⋓ ?Γ2 ⋓ ?Γ3) |- _ ]   => apply valid_split in H as [? [? ?]]
  (* Reduce goal to binary disjointness *)
  | [|- is_valid (?Γ1 ⋓ (?Γ2 ⋓ ?Γ3)) ] => rewrite (merge_assoc Γ1 Γ2 Γ3)
  | [|- is_valid (?Γ1 ⋓ ?Γ2 ⋓ ?Γ3) ]   => apply valid_join; validate
  end).

Definition Typed_Box (b : Box) (W1 W2 : WType) : Set := 
  forall Γ p, Types_Pat Γ p W1 -> Types_Circuit Γ (unbox b p) W2.

(* Automation *)

Ltac goal_has_evars := 
  match goal with 
  [|- ?G ] => has_evars G
  end.

Ltac type_check_once := 
  intros;
  compute in *; 
  subst; 
  repeat match goal with 
  | [ p : Pat _ One |- _ ]         => inversion p; subst; clear p
  end; 
  (* Runs monoid iff a single evar appears in context *)
  match goal with 
  | [|- is_valid ?Γ] => tryif (has_evar Γ)   
                        then (idtac (*"can't validate"; print_goal*))
                        else (idtac (*"validate"; print_goal*); validate)
  | [|- ?G ]         => tryif (has_evars G)  
                        then (idtac (*"can't monoid"; print_goal*))
                        else (idtac (*"monoid"; print_goal*); monoid)
  end.

(* Useful for debugging *)
Ltac type_check_num := 
  let pre := numgoals in idtac "Goals before: " pre "";
  [> type_check_once..];
  let post := numgoals in idtac "Goals after: " post "";
  tryif (guard post < pre) then type_check_num else idtac "done".

(* Easiest solution *)

Ltac type_check := let n := numgoals in do n [> type_check_once..].




(* *)