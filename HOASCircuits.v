Require Export Contexts.
Require Import List.
Import ListNotations.

Inductive bools := 
  | UT : bools
  | BT : bool -> bools
  | TT : bools -> bools -> bools
.
  
Inductive Circuit : Set :=
| output : Pat -> Circuit
| gate   : forall {w1 w2}, Gate w1 w2 ->  Pat -> (Pat -> Circuit) -> Circuit
| lift   : Pat -> (bools -> Circuit) -> Circuit
.

Inductive Lifts_Type : bools -> WType -> Set :=
  | lifts_unit :  Lifts_Type UT One
  | lifts_qubit :  forall b, Lifts_Type (BT b) Qubit
  | lifts_bit :  forall b, Lifts_Type (BT b) Bit
  | lifts_tensor : forall LL LC RL RC, Lifts_Type LC LL ->
                                  Lifts_Type RC RL ->
                                  Lifts_Type (TT LC RC) (Tensor LL RL).

Inductive Types_Circuit : OCtx -> Circuit -> WType -> Set :=
| types_output : forall {Γ Γ' w p} {pf : Γ = Γ'}, Types_Pat Γ p w -> 
                                             Types_Circuit Γ' (output p) w
| types_gate : forall {Γ Γ1 Γ1' Γ2 Γ2' p1 p2 w1 w2 w C} {g : Gate w1 w2} 
                 {v1: is_valid Γ1'} {m1: Γ1' = Γ1 ⋓ Γ} 
                 {v2: is_valid Γ2'} {m2: Γ2' = Γ2 ⋓ Γ},
               Types_Pat Γ1 p1 w1 ->
               Types_Pat Γ2 p2 w2 ->
               Types_Circuit Γ2' (C p2) w ->
               Types_Circuit Γ1' (gate g p1 C) w  
| types_lift : forall {Γ1 Γ2 p Γ w w' f bs} {v : is_valid Γ} {m : Γ = Γ1 ⋓ Γ2},         
               Types_Pat Γ1 p w -> 
               Lifts_Type bs w ->
               Types_Circuit Γ2 (f bs) w' ->
               Types_Circuit Γ (lift p f) w'.

(* Old def:
Inductive Circuit : OCtx -> WType -> Set :=
| output : forall {Γ Γ' w} {pf : Γ = Γ'}, Pat Γ w -> Circuit Γ' w
| gate   : forall {Γ Γ1 Γ1' w1 w2 w}
           {v1 : is_valid Γ1'} {m1 : Γ1' = Γ1 ⋓ Γ},
           Gate w1 w2
        -> Pat Γ1 w1
        -> (forall {Γ2 Γ2'} {v2 : is_valid Γ2'} {m2 : Γ2' = Γ2 ⋓ Γ},
            Pat Γ2 w2 -> Circuit Γ2' w)
        -> Circuit Γ1' w
| lift : forall {Γ1 Γ2 Γ w w'} {v : is_valid Γ} {m : Γ = Γ1 ⋓ Γ2},
         Pat Γ1 w
      -> (interpret w -> Circuit Γ2 w')
      -> Circuit Γ w'
. 
*)

(* Old Box / Unbox:

Inductive Box : WType -> WType -> Set :=
| box : forall {w1} {w2}, 
        (forall {Γ}, Pat Γ w1 -> Circuit Γ w2) -> Box w1 w2.

Definition unbox {Γ Γ'} {w1} {w2} {pf : Γ = Γ'} (b : Box w1 w2)  (p : Pat Γ w1)
           : Circuit Γ' w2.
Proof.
  destruct b. subst. exact (c _ p).
Defined.

*)

Inductive Box : Set := box : (Pat -> Circuit) -> Box.

Definition unbox (b : Box )  (p : Pat) : Circuit := 
  match b with
  box c => c p
  end.

Definition Typed_Box (b : Box) (W1 W2 : WType) : Set := 
  forall Γ p, Types_Pat Γ p W1 -> Types_Circuit Γ (unbox b p) W2.

(* Prevent compute from unfolding important fixpoints *)
Opaque merge.
Opaque Ctx.
Opaque is_valid.

(* Need to rewrite *)
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

Fixpoint compose (c : Circuit) (f : Pat -> Circuit) : Circuit :=
  match c with 
  | output p     => f p
  | gate g p c'  => gate g p (fun p' => compose (c' p') f)
  | lift p c'    => lift p (fun bs => compose (c' bs) f)
  end.

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