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

Inductive Circuit (w : WType) : Set :=
| output : Pat w -> Circuit w
| gate   : forall {w1 w2}, 
           Gate w1 w2 ->  Pat w1 -> (Pat w2 -> Circuit w) -> Circuit w
| lift   : Pat Bit -> (bool -> Circuit w) -> Circuit w.

Inductive Box w1 w2 : Set := box : (Pat w1 -> Circuit w2) -> Box w1 w2.
Arguments output {w}.
Arguments gate {w w1 w2}.
Arguments lift {w}.
Arguments box {w1 w2}.

Definition unbox {w1 w2} (b : Box w1 w2)  (p : Pat w1) : Circuit w2 := 
  match b with box c => c p end.

Fixpoint compose {w1 w2} (c : Circuit w1) (f : Pat w1 -> Circuit w2) : Circuit w2 :=
  match c with 
  | output p     => f p
  | gate g p c'  => gate g p (fun p' => compose (c' p') f)
  | lift p c'    => lift p (fun bs => compose (c' bs) f)
  end.

(* Typed Circuits and Boxes *)

Inductive Types_Circuit : OCtx -> forall {w}, Circuit w -> Set :=
| types_output : forall {Γ Γ' w} {p : Pat w} {pf : Γ = Γ'}, Types_Pat Γ p -> 
                                             Types_Circuit Γ' (output p)
| types_gate : forall {Γ Γ1 Γ1' w1 w2 w} {C : Pat w2 -> Circuit w} {p1 : Pat w1} {g : Gate w1 w2} 
                 {v1: is_valid Γ1'} {m1: Γ1' = Γ1 ⋓ Γ},               
                 Types_Pat Γ1 p1 ->
                 (forall Γ2 Γ2' (p2 : Pat w2) {v2: is_valid Γ2'} {m2: Γ2' = Γ2 ⋓ Γ}, 
                   Types_Pat Γ2 p2 ->
                   Types_Circuit Γ2' (C p2)) ->
                 Types_Circuit Γ1' (gate g p1 C)
| types_lift_bit : forall {Γ1 Γ2 Γ w } {p : Pat Bit} {f : bool -> Circuit w} 
                          {v : is_valid Γ} {m : Γ = Γ1 ⋓ Γ2},         
                     Types_Pat Γ1 p -> 
                     (forall b, Types_Circuit Γ2 (f b)) ->
                     Types_Circuit Γ (lift p f).
(*
| types_lift_qubit : forall {Γ1 Γ2 p Γ w f} {v : is_valid Γ} {m : Γ = Γ1 ⋓ Γ2},     
                     Types_Pat Γ1 p Qubit -> 
                     (forall b, Types_Circuit Γ2 (f b) w) ->
                     Types_Circuit Γ (lift p f) w.
*)

Definition Typed_Box {W1 W2 : WType} (b : Box W1 W2) : Set := 
  forall Γ (p : Pat W1), Types_Pat Γ p -> Types_Circuit Γ (unbox b p).

(* Prevent compute from unfolding important fixpoints *)
Opaque merge.
Opaque Ctx.
Opaque is_valid.

(* Automation *)

Ltac validate :=
  repeat ((*idtac "validate";*) match goal with
  (* Pattern contexts are valid *)
  | [H : Types_Pat _ _ |- _ ]    => apply pat_ctx_valid in H
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

Lemma compose_typing : forall Γ1 Γ1' Γ W W' (c : Circuit W) (f : Pat W -> Circuit W')
        {v1 : is_valid Γ1'} {m1 : Γ1' = Γ1 ⋓ Γ},
        Types_Circuit Γ1 c ->
        (forall p {Γ2 Γ2'} (m2 : Γ2' = Γ2 ⋓ Γ) (v2 : is_valid Γ2'), 
                    Types_Pat Γ2 p -> Types_Circuit Γ2' (f p) ) ->
        Types_Circuit Γ1' (compose c f).
Proof.
  do 7 intro. intros v1 m1 types_c types_f.
  generalize dependent Γ.
  generalize dependent Γ1'.
  generalize dependent f.
  induction types_c; intros; subst; simpl.
  + eapply types_f; trivial. 
  + econstructor; try apply t. validate. monoid.
    intros Γ2 Γ2' p2 v2 m2 types_p2.
    eapply H; [ | | apply types_p2 | validate | | ]; subst; monoid; validate.
    intros p Γ3 Γ2' m2 v2 types_p.
    eapply types_f; subst; [monoid | validate | apply types_p].
  + econstructor; try apply t; subst; validate; monoid.
    intros.
    eapply H; validate; monoid.
    intros p' Γ3 Γ2' m3 v2 types_p'.
    eapply types_f; try apply types_p'; subst; validate; monoid.
Qed.

Lemma unbox_typing : forall Γ W1 W2 (p : Pat W1) (c : Box W1 W2), 
                                    Types_Pat Γ p ->
                                    Typed_Box c ->
                                    Types_Circuit Γ (unbox c p).
Proof. unfold Typed_Box in *. auto. Qed.


Record Types_Compose {w w'} (c : Circuit w) (f : Pat w -> Circuit w') :=
  { ctx_c : OCtx  (* Γ1 *)
  ; ctx_out: OCtx (* Γ1' *)
  ; ctx_in : OCtx (* Γ *)
  ; pf_ctx : ctx_out == ctx_c ∙ ctx_in (* Γ1' = Γ1 ⋓ Γ *)
  ; types_c : Types_Circuit ctx_c c 
  ; types_f : forall p Γ2 Γ2', Γ2' == Γ2 ∙ ctx_in -> 
                               Types_Pat Γ2 p -> Types_Circuit Γ2' (f p) 
  }.

Arguments ctx_c {w w' c f}.
Arguments ctx_out {w w' c f}.
Arguments ctx_in  {w w' c f}.
Arguments pf_ctx {w w' c f}.
Arguments types_c {w w' c f}.


(* *)