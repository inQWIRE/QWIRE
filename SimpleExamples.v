Require Import Datatypes.
Require Export TypeChecking.
Require Import HOASLib.
Import ListNotations.
Open Scope list_scope.

(*******************)
(** Teleportation **)
(*******************)

Notation H := (U _H).
Notation X := (U _X).
Notation Y := (U _Y).
Notation Z := (U _Z).
Notation CNOT := (U CNOT).
Variable _I : Unitary 1 (Qubit 1).
Notation I := (U _I).

Definition bell00 : Box One (Qubit 2 ⊗ Qubit 2) :=
  box_ _ ⇒  
    gate_ a     ← init0 @();
    gate_ b     ← init0 @();
    gate_ a     ← H @a;
    gate_ (a,b) ← CNOT @(a,,b); 
    (a,b).

(* Type inference works, but isn't giving as simple of an expression as we'd like? *)
Definition bell00' : Box One (Qubit _ ⊗ Qubit _) :=
  box_ _ ⇒  
    gate_ a     ← init0 @();
    gate_ b     ← init0 @();
    gate_ a     ← H @a;
    gate_ (a,b) ← CNOT @(a,,b); 
    (a,b).
Print bell00'. 

Definition alice : Box (Qubit 0 ⊗ Qubit 2) (Bit ⊗ Bit) :=
  box_ qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← H   @q;
    gate_ x     ← meas @q;
    gate_ y     ← meas @a;
    (x,y).

Definition bob : Box (Bit ⊗ Bit ⊗ Qubit 2) (Qubit 4) :=
  box_ (x,y,b) ⇒ 
    gate_ (y,b)    ← U (bit_ctrl _X) @(y,,b);
    gate_ (x,b)    ← U (bit_ctrl _Z) @(x,,b);
    discard_ (x,y) ;  
    output b.

Definition teleport : Box (Qubit 0) (Qubit 4) :=
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,,a) ;
    unbox bob (x,,y,,b).

(* Now with error correction! *)

Definition bell_EC : Box One (Qubit 2 ⊗ Qubit 2) :=
  box_ () ⇒  
    gate_ a ← init0 @();
    gate_ b ← init0 @();
    gate_ a ← H @a;
    gate_ (a,b) ← CNOT @(a,,b); 
    output (a,,b).

Definition alice_EC : Box (Qubit 0 ⊗ Qubit 2) (Bit ⊗ Bit) :=
  box_ qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← EC   @q;
    gate_ q     ← H    @q;
    gate_ x     ← meas @q;
    gate_ y     ← meas @a;
    output (x,,y).

Definition bob_EC : Box (Bit ⊗ Bit ⊗ Qubit 2) (Qubit 1) :=
  box_ (x,y,b) ⇒ 
    gate_ (y,b)    ← U (bit_ctrl _X) @(y,,b);
    gate_ b        ← EC              @b;
    gate_ (x,b)    ← U (bit_ctrl _Z) @(x,,b);
    discard_ (x,y) ;  
    output b.

Definition teleport_EC : Box (Qubit 0) (Qubit 1) :=
  box_ q ⇒
    let_ (a,b) ← unbox bell_EC () ;
    let_ (x,y) ← unbox alice_EC (q,,a) ;
    unbox bob_EC (x,,y,,b).

Lemma teleport_EC_WT : Typed_Box teleport_EC 3.
Proof. 
  (* manually doing what type_check does, but with some added calls to lia *)
  unfold teleport_EC, bell_EC, alice_EC, bob_EC.  
  unfold Typed_Box. 
  intros.
  simpl in *.
  dependent destruction p.
  econstructor. econstructor.
  simpl. lia. simpl. lia.
  intros.
  econstructor. econstructor.
  simpl. lia. simpl. lia.
  intros.
  econstructor. admit. auto. auto.
  intros.
  eapply types_gate_U. 
(* why can't I apply this here? *)


admit. auto. 
  intros.
  econstructor. admit.
  simpl. lia.
  intros.




  match goal with 
    | H: @Types_Circuit _ _ _ ?c |- @Types_Circuit _ _ ?c 
                               => exact H
  | [ |- @Types_Circuit _ _ _ _ ] => econstructor; type_check_once

  | [ |- @Types_Circuit _ _ _ (if ?b then _ else _) ]
                                => destruct b; type_check_once

  (* compose_typing : specify goal. *)                                  
  | [ |- @Types_Circuit _ _ _ _ ] =>  eapply compose_typing; type_check_once 

  | [ H : forall a b, Types_Pat _ _ -> Types_Circuit _ _ |- Types_Circuit _ _] 
                                => apply H; type_check_once

  | [ H : @Types_Pat _ _ ?p |- @Types_Pat _ _ ?p ] 
                                => exact H
  | [ H : @Types_Pat ?Γ1 _ ?p |- @Types_Pat ?Γ2 _ ?p ] 
                                   (* in case they don't line up exactly *)
                                => replace Γ2 with Γ1; [exact H | monoid]

  | [ |- Types_Pat _ _ ]        => econstructor; type_check_once
  | [ |- ?Γ == ?Γ1 ∙ ?Γ2 ]      => has_evars (Γ1 ⋓ Γ2 ⋓ Γ)
  | [ |- _ == _ ∙ _ ]           => solve_merge
  end.
  econstructor.
  2: { simpl. lia.

eauto with typed_db.
  

 type_check. Qed.


Ltac goal_has_evars := 
  match goal with 
  [|- ?G ] => has_evars G
  end.

Ltac invert_patterns := 
  repeat match goal with
  | [ p : Pat One |- _ ] => dependent destruction p
  | [ p : Pat Qubit |- _] => dependent destruction p
  | [ p : Pat Bit |- _] => dependent destruction p
  | [ p : Pat (_ ⊗ _) |- _ ] => dependent destruction p
  | [ H : Types_Pat ?Γ () |- _ ]           => is_var Γ; inversion H; subst
  | [ H : Types_Pat ?Γ (qubit _) |- _ ]    => is_var Γ; inversion H; subst
  | [ H : Types_Pat ?Γ (bit _)   |- _ ]    => is_var Γ; inversion H; subst
  | [ H : Types_Pat ?Γ (pair _ _) |- _ ]   => is_var Γ; dependent destruction H
  end.

Create HintDb typed_db.

Ltac type_check_once := 
  intros;
  try match goal with 
  | [|- Typed_Box _ ]           => solve [eauto with typed_db] (* extensible *)
  | [|- @Typed_Box  ?W1 ?W2 ?c] => unfold Typed_Box in *; try unfold c
  end;
  intros;
  simpl in *;
  subst; 
  invert_patterns;
  repeat match goal with 
  | [ b : bool |- _ ]              => destruct b 
  | [ H : _ == _ ∙ _ |- _ ]     => destruct H
    | H: @Types_Circuit _ _ ?c |- @Types_Circuit _ _ ?c 
                               => exact H
  | [ |- @Types_Circuit _ _ _ ] => econstructor; type_check_once

  | [ |- @Types_Circuit _ _ (if ?b then _ else _) ]
                                => destruct b; type_check_once

  (* compose_typing : specify goal. *)                                  
  | [ |- @Types_Circuit _ _ _ ] =>  eapply compose_typing; type_check_once 

  | [ H : forall a b, Types_Pat _ _ -> Types_Circuit _ _ |- Types_Circuit _ _] 
                                => apply H; type_check_once

  | [ H : @Types_Pat _ _ ?p |- @Types_Pat _ _ ?p ] 
                                => exact H
  | [ H : @Types_Pat ?Γ1 _ ?p |- @Types_Pat ?Γ2 _ ?p ] 
                                   (* in case they don't line up exactly *)
                                => replace Γ2 with Γ1; [exact H | monoid]

  | [ |- Types_Pat _ _ ]        => econstructor; type_check_once
  | [ |- ?Γ == ?Γ1 ∙ ?Γ2 ]      => has_evars (Γ1 ⋓ Γ2 ⋓ Γ)
  | [ |- _ == _ ∙ _ ]           => solve_merge
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
