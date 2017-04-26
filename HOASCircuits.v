Require Export Contexts.
Require Import List.
Import ListNotations.


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



(*
Inductive Circuit : OCtx -> WType -> Set :=
| output : forall {ctx ctx' w}, ctx' = ctx -> Pat ctx w -> Circuit ctx' w
| gate   : forall ctx {ctx1 ctx1'} {w1 w2 w}, 
          is_valid ctx1'
        -> ctx1' = ctx1 ⋓ ctx            
        -> Gate w1 w2
        -> Pat ctx1 w1
        -> (forall {ctx2 ctx2'},
              is_valid ctx2'
            -> ctx2' = ctx2 ⋓ ctx 
            -> Pat ctx2 w2 -> Circuit ctx2' w)
        -> Circuit ctx1' w
| lift : forall {ctx1 ctx2 ctx w w'},
         is_valid ctx -> ctx = ctx1 ⋓ ctx2
      -> Pat ctx1 w
      -> (interpret w -> Circuit ctx2 w')
      -> Circuit ctx w'
. *)

Inductive Box : WType -> WType -> Set :=
| box : forall {w1} {w2}, 
        (forall {Γ}, Pat Γ w1 -> Circuit Γ w2) -> Box w1 w2.

Definition unbox {Γ Γ'} {w1} {w2} {pf : Γ = Γ'} (b : Box w1 w2)  (p : Pat Γ w1)
           : Circuit Γ' w2.
Proof.
  destruct b. subst. exact (c _ p).
Defined.

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

Require Program. 
Arguments gate Γ Γ1 {Γ1' w1 w2 w v1 m1}. 
Arguments lift Γ1 Γ2 {Γ w w' v m}.
Program Fixpoint compose Γ1 {Γ1'} {W} (c : Circuit Γ1 W) {Γ W'} 
        {v1 : is_valid Γ1'} {m1 : Γ1' = Γ1 ⋓ Γ}
        (f : forall {Γ2 Γ2'} (m2 : Γ2' = Γ2 ⋓ Γ) (v2 : is_valid Γ2'), 
             Pat Γ2 W -> Circuit Γ2' W')
        : Circuit Γ1' W' :=
  match c with 
  | output p1          => f _ _ p1
  | gate Γ0 Γ01 g p1 h => gate (Γ0 ⋓ Γ) Γ01 g p1 (fun Γ02 _ _ _ q => 
                          compose _ (h Γ02 (Γ02 ⋓ Γ0) _ _ q) (fun _ _ => f))
  | lift Γ01 Γ02 p h   => lift Γ01 (Γ02 ⋓ Γ) p (fun x => 
                          compose Γ02 (h x) (fun _ _ => f))
  end.
Next Obligation. monoid. Defined.
Next Obligation. validate. Defined.
Next Obligation. monoid.  Defined.
Next Obligation. monoid. Defined.
Next Obligation. validate. Defined.
Arguments gate {Γ Γ1 Γ1' w1 w2 w v1 m1}. 
Arguments lift {Γ1 Γ2 Γ w w' v m}.
Arguments compose {Γ1 Γ1' W} c {Γ W' v1 m1}.


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