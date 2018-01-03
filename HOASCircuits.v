Require Export Contexts.
Require Import List.
Import ListNotations.

(*
Inductive CType := 
  | C_Unit : CType
  | C_Bit  : CType
  | C_Pair : CType -> CType -> CType.
  
Fixpoint from_CType (c : CType) := 
  match c with
  | C_Unit => Datatypes.unit
  | C_Bit => bool 
  | C_Pair C1 C2 => Datatypes.prod (from_CType C1) (from_CType C2)
  end.

Inductive Lifts_Type : bools -> WType -> Set :=
  | lifts_unit :  Lifts_Type UT One
  | lifts_qubit :  forall b, Lifts_Type (BT b) Qubit
  | lifts_bit :  forall b, Lifts_Type (BT b) Bit
  | lifts_tensor : forall LL LC RL RC, Lifts_Type LC LL ->
                                  Lifts_Type RC RL ->
                                  Lifts_Type (TT LC RC) (Tensor LL RL).

Fixpoint ctype_of_pat (p : Pat) : Set := 
  match p with 
  | unit => Datatypes.unit
  | qubit n => bool 
  | bit n => bool 
  | pair C1 C2 => Datatypes.prod (ctype_of_pat C1) (ctype_of_pat C2)
  end.
*)

Inductive Circuit : Set :=
| output : Pat -> Circuit
| gate   : forall {w1 w2}, Gate w1 w2 ->  Pat -> (Pat -> Circuit) -> Circuit
| lift   : Pat -> (bool -> Circuit) -> Circuit.

Inductive Box : Set := box : (Pat -> Circuit) -> Box.

Definition unbox (b : Box)  (p : Pat) : Circuit := 
  match b with box c => c p end.

Fixpoint compose (c : Circuit) (f : Pat -> Circuit) : Circuit :=
  match c with 
  | output p     => f p
  | gate g p c'  => gate g p (fun p' => compose (c' p') f)
  | lift p c'    => lift p (fun bs => compose (c' bs) f)
  end.

(* Typed Circuits and Boxes *)

Inductive Types_Circuit : OCtx -> Circuit -> WType -> Set :=
| types_output : forall {Γ Γ' w p} {pf : Γ = Γ'}, Types_Pat Γ p w -> 
                                             Types_Circuit Γ' (output p) w
| types_gate : forall {Γ Γ1 Γ1' p1 w1 w2 w C} {g : Gate w1 w2} 
                 {v1: is_valid Γ1'} {m1: Γ1' = Γ1 ⋓ Γ},               
                 Types_Pat Γ1 p1 w1 ->
                 (forall Γ2 Γ2' p2 {v2: is_valid Γ2'} {m2: Γ2' = Γ2 ⋓ Γ}, 
                   Types_Pat Γ2 p2 w2 ->
                   Types_Circuit Γ2' (C p2) w) ->
                 Types_Circuit Γ1' (gate g p1 C) w  
| types_lift_bit : forall {Γ1 Γ2 p Γ w f} {v : is_valid Γ} {m : Γ = Γ1 ⋓ Γ2},         
                     Types_Pat Γ1 p Bit -> 
                     (forall b, Types_Circuit Γ2 (f b) w) ->
                     Types_Circuit Γ (lift p f) w
| types_lift_qubit : forall {Γ1 Γ2 p Γ w f} {v : is_valid Γ} {m : Γ = Γ1 ⋓ Γ2},     
                     Types_Pat Γ1 p Qubit -> 
                     (forall b, Types_Circuit Γ2 (f b) w) ->
                     Types_Circuit Γ (lift p f) w.

Definition Typed_Box (b : Box) (W1 W2 : WType) : Set := 
  forall Γ p, Types_Pat Γ p W1 -> Types_Circuit Γ (unbox b p) W2.

(* Prevent compute from unfolding important fixpoints *)
Opaque merge.
Opaque Ctx.
Opaque is_valid.

(* Automation *)

Ltac validate :=
  repeat ((*idtac "validate";*) match goal with
  (* Pattern contexts are valid *)
  | [H : Types_Pat ?Γ ?p ?W |- _ ]    => apply pat_ctx_valid in H
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


Ltac goal_has_evars := 
  match goal with 
  [|- ?G ] => has_evars G
  end.

Ltac type_check_once := 
  compute in *; 
  intros;
  subst; 
  repeat match goal with 
  | [ H : Types_Pat _ ?p One |- _ ]           => is_var p; inversion H; subst
  | [ H : Types_Pat _ ?p (Tensor _ _) |- _ ]  => is_var p; inversion H; subst
  | [ |- Types_Circuit _ _ _ ]                => econstructor; type_check_once
  | [ |- Types_Circuit _ (if ?b then _ else _) _ ] => destruct b; type_check_once
  | [ H : Types_Pat _ ?p ?W |- Types_Pat _ ?p ?W ] => apply H
  | [ |- Types_Pat _ _ _ ]                   => econstructor; type_check_once
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

(* Composition lemma *)

Lemma compose_typing : forall Γ1 Γ1' Γ c f W W'  
        {v1 : is_valid Γ1'} {m1 : Γ1' = Γ1 ⋓ Γ},
        Types_Circuit Γ1 c W ->
        (forall p {Γ2 Γ2'} (m2 : Γ2' = Γ2 ⋓ Γ) (v2 : is_valid Γ2'), 
                    Types_Pat Γ2 p W -> Types_Circuit Γ2' (f p) W') ->
        Types_Circuit Γ1' (compose c f) W'.
Proof.
  intros Γ1 Γ1' Γ c f W W' v1 m1 H.
  generalize dependent Γ.
  generalize dependent Γ1'.
  generalize dependent f.
  induction H; intros; subst; simpl.
  + eapply H; trivial. 
  + econstructor; try apply t; subst; validate; monoid.
    intros.
    eapply H; try apply H4; subst; validate; monoid.
    validate.
    intros.
    eapply H0; try apply H8; subst; validate; monoid.
  + econstructor; try apply t; subst; validate; monoid.
    intros.
    simpl.
    eapply H; validate; monoid.
    intros.
    eapply H0; try apply H4; subst; validate; monoid. 
  + eapply (types_lift_qubit t).
    Unshelve.
    4: monoid.
    2: validate.
    intros.     
    eapply H; validate; monoid.
    intros.
    eapply H0. 
    subst; monoid.
    validate.    
    assumption.
Qed.

Lemma unbox_typing : forall Γ p W1 W2 c, Types_Pat Γ p W1 ->
                                    Typed_Box c W1 W2 ->
                                    Types_Circuit Γ (unbox c p) W2.
Proof. unfold Typed_Box in *. auto. Qed.


(* *)