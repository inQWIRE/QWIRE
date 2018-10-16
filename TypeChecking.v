Require Export HOASCircuits.

(** Projecting out elements of tensors **)

Open Scope circ_scope.
Definition wproj {Var} {W1 W2} (p : Pat Var (W1 ⊗ W2)) : Pat Var W1 * Pat Var W2 :=
  match p with
  | pair p1 p2 => (p1, p2)  
  end.

(*** Typechecking Tactic ***)

(* Prevent compute from unfolding important fixpoints *)
Open Scope circ_scope.
Opaque wproj.
Global Opaque merge.
Global Opaque Ctx.
Global Opaque is_valid.

Fixpoint pair_circ' {Var} {W1 W2} (p : Pat Var W1) (c2 : Circuit Var W2) : Circuit Var (W1 ⊗ W2) :=
  match c2 with
  | output p2   => output (pair p p2)
  | gate g p1 f => gate g p1 (fun p2 => pair_circ' p (f p2))
  | lift p1 f   => lift p1 (fun x => pair_circ' p (f x))
  end.
Fixpoint pair_circ {Var} {W1 W2} (c1 : Circuit Var W1) (c2 : Circuit Var W2) : Circuit Var (W1 ⊗ W2) :=
  match c1 with
  | output p1   => pair_circ' p1 c2
  | gate g p1 f => gate g p1 (fun p2 => pair_circ (f p2) c2)
  | lift p f    => lift p (fun b => pair_circ (f b) c2)
  end.
Notation "( x , y , .. , z )" := (pair_circ .. (pair_circ x y) .. z) (at level 0) : circ_scope.


(*** Notations ***)

Set Printing Coercions.

(* These tactics construct circuits by calling out to type_check *)


Notation letpair p1 p2 p c := (let (p1,p2) := wproj p in c).

Notation "'box_' p ⇒ C" := (box (fun p => C)) 
    (at level 13) : circ_scope.
Notation "'box_' () ⇒ C" := (box (fun _ => C)) 
    (at level 13) : circ_scope.
Notation "'box_' ( p1 , p2 ) ⇒ C" := (box (fun p => letpair p1 p2 p C)) 
    (at level 13) : circ_scope.
Notation "'box_' ( p1 , p2 , p3 ) ⇒ C" := (box (fun p =>
    let (y,p3) := wproj p in
    let (p1,p2) := wproj y in C)) 
    (at level 13) : circ_scope.
Notation "'box_' ( p1 , ( p2 , p3 ) ) ⇒ C" := (box (fun x =>
    let (p1,y) := wproj x in
    let (p2,p3) := wproj y in C)) 
    (at level 13) : circ_scope.
Notation "'box_' ( ( p1 , p2 ) , ( p3 , p4 ) ) ⇒ C" := (box (fun x =>
    let (y,z) := wproj x in
    let (p1,p2) := wproj y in
    let (p3,p4) := wproj z in
    C)) 
    (at level 13) : circ_scope.

(* Notations for patterns *)
Notation "()" := unit : circ_scope.
(* Now a bit ugly, since we tend to use (a,b) with the newer $ notation *)
Notation "( x ,, y ,, .. ,, z )" := (pair .. (pair x y) .. z) (at level 0) : circ_scope.


(* Notations for circuits *)
Notation comp p c1 c2 := (compose c1 (fun p => c2)).
Notation "'let_' p ← c1 ; c2" := (comp p c1 c2)
                            (at level 14, right associativity) : circ_scope.
Notation "'let_' () ← c1 ; c2" := 
    (compose c1 (fun _ => c2)) 
                            (at level 14, right associativity) : circ_scope.
Notation "'let_' ( p1 , p2 ) ← c1 ; c2" := 
    (compose c1 (fun x => letpair p1 p2 x c2)) 
                            (at level 14, right associativity) : circ_scope.
Notation "'let_' ( p1 , p2 , p3 ) ← c1 ; c2" :=
    (compose c1 (fun x => let (y,p3) := wproj x in
                       let (p1,p2) := wproj y in c2))
                            (at level 14, right associativity) : circ_scope.
Notation "'let_' ( ( p1 , p2 ) , p3 ) ← c1 ; c2" := 
    (compose c1 (fun x => let (y,p3) := wproj x in
                       let (p1,p2) := wproj y in c2))
                            (at level 14, right associativity) : circ_scope.
Notation "'let_' ( p1 , ( p2 , p3 ) ) ← c1 ; c2" :=
    (compose c1 (fun x => let (p1,y) := wproj x in
                       let (p2,p3) := wproj y in c2))
                            (at level 14, right associativity) : circ_scope.
Notation "'let_' ( ( p1 , p2 ) , ( p3 , p4 ) ) ← c1 ; c2" :=
    (compose c1 (fun x => let (y,z) := wproj x in
                       let (p1, p2) := wproj y in
                       let (p3, p4) := wproj z in c2))
                            (at level 14, right associativity) : circ_scope.
Notation "'let_' ( p1 , ( p2 , ( p3 , ( p4 , ( p5 , p6 ) ) ) ) ) ← c1 ; c2" :=
    (compose c1 (fun x => let (p1,y) := wproj x in
                       let (p2,z) := wproj y in
                       let (p3,a) := wproj z in
                       let (p4,b) := wproj a in
                       let (p5,p6) := wproj b in c2))
                            (at level 14, right associativity) : circ_scope.

Notation "'gate_' p2 ← g @ p ; c2" := (gate g p (fun p2 => c2))
         (at level 14, right associativity).
Notation "'gate_' () ← g @ p ; c2" := (gate g p (fun _ => c2))
         (at level 14, right associativity).
Notation "'gate_' ( p1 , p2 ) ← g @ p ; c2" := 
    (gate g p (fun x => letpair p1 p2 x c2))
                            (at level 14, right associativity) : circ_scope.
Notation "'gate_' ( p1 , p2 , p3 ) ← g @ p ; c2" :=
    (gate g p (fun x => let (y, p3) := wproj x in
                     let (p1, p2) := wproj y in c2))
                           (at level 14, right associativity) : circ_scope.
Notation "'gate_' ( ( p1 , p2 ) , p3 ) ← g @ p ; c2" := 
    (gate g p (fun x => let (y, p3) := wproj x in
                     let (p1, p2) := wproj y in c2))
                            (at level 14, right associativity) : circ_scope.
Notation "'gate_' ( p1 , ( p2 , p3 ) ) ← g @ p ; c2" :=
    (gate g p (fun x => let (p1, y) := wproj x in
                     let (p2, p3) := wproj y in c2))
                            (at level 14, right associativity) : circ_scope.
Notation "'gate_' ( ( p1 , p2 ) , ( p3 , p4 ) ) ← g @ p ; c2" :=
    (gate g p (fun x => let (y, z) := wproj x in
                     let (p1, p2) := wproj y in
                     let (p3, p4) := wproj z in c2))
                            (at level 14, right associativity) : circ_scope.
Notation "'gate_' ( p1 , ( p2 , ( p3 , ( p4 , ( p5 , p6 ) ) ) ) ) ← g @ p ; c2" :=
    (gate g p (fun x => let (p1,y) := wproj x in
                       let (p2,z) := wproj y in
                       let (p3,a) := wproj z in
                       let (p4,b) := wproj a in
                       let (p5,p6) := wproj b in c2))
                            (at level 14, right associativity) : circ_scope.

Notation "'discard_' p ; c" := (gate discard p (fun _ => c))
         (at level 14, right associativity) : circ_scope.
Notation "'discard_' ( p1 , p2 ) ; c" := (gate discard p1 (fun _ => gate discard p2 
                                                                      (fun _ => c)))
         (at level 14, right associativity) : circ_scope.
Notation "'discard_' ( p1 , p2 , p3 ) ; c" := (gate discard p1 
                                                 (fun _ => gate discard p2 
                                                   (fun _ => gate discard p3 
                                                     (fun _ => c))))
         (at level 14, right associativity) : circ_scope.
Notation "'discard_' ( ( p1 , p2 ) , p3 ) ; c" := (gate discard p1 
                                                 (fun _ => gate discard p2 
                                                   (fun _ => gate discard p3 
                                                     (fun _ => c))))
         (at level 14, right associativity) : circ_scope.
Notation "'discard_' ( p1 , ( p2 , p3 ) ) ; c" := (gate discard p1 
                                                 (fun _ => gate discard p2 
                                                   (fun _ => gate discard p3 
                                                     (fun _ => c))))
         (at level 14, right associativity) : circ_scope.
Notation "'discard_' ( ( p1 , p2 ) , ( p3 , p4 ) ) ; c" :=
  (gate discard p1 
        (fun _ => gate discard p2 
                    (fun _ => gate discard p3 
                                (fun _ => gate discard p4 
                                            (fun _ => c)))))
         (at level 14, right associativity) : circ_scope.
Notation "'discard_' ( p1 , ( p2 , ( p3 , ( p4 , ( p5 , p6 ) ) ) ) ) ; c" :=
    (gate discard p1 (fun _ => gate discard p2 
                      (fun _ => gate discard p3
                      (fun _ => gate discard p4
                      (fun _ => gate discard p5
                      (fun _ => gate discard p6))))))
                            (at level 14, right associativity) : circ_scope.

Delimit Scope circ_scope with qc.

(* Automation *)

Ltac goal_has_evars := 
  match goal with 
  [|- ?G ] => has_evars G
  end.

Ltac invert_patterns := 
  repeat match goal with
  | [ p : Pat _ One |- _ ] => dependent destruction p
  | [ p : Pat _ Qubit |- _] => dependent destruction p
  | [ p : Pat _ Bit |- _] => dependent destruction p
  | [ p : Pat _ (_ ⊗ _) |- _ ] => dependent destruction p
  | [ H : Types_Pat ?Γ () |- _ ]           => is_var Γ; inversion H; subst
  | [ H : Types_Pat ?Γ (qubit _) |- _ ]    => is_var Γ; inversion H; subst
  | [ H : Types_Pat ?Γ (bit _)   |- _ ]    => is_var Γ; inversion H; subst
  | [ H : Types_Pat ?Γ (pair _ _) |- _ ]   => is_var Γ; dependent destruction H
  end.

Create HintDb typed_db.

Ltac type_check_once := 
  intros;
  try match goal with 
  | [|- Typed_Box _ _ ]          => solve [eauto with typed_db] (* extensible *)
  | [|- @Typed_Box _ ?W1 ?W2 ?c] => unfold Typed_Box in *; try unfold c
  end;
  intros;
  simpl in *;
  subst; 
  invert_patterns;
  repeat match goal with 
  | [ b : bool |- _ ]              => destruct b 
  | [ H : _ == _ ∙ _ |- _ ]     => destruct H
    | H: @Types_Circuit _ _ _ ?c |- @Types_Circuit _ _ _ ?c 
                               => exact H
  | [ |- @Types_Circuit _ _ _ _ ] => econstructor; type_check_once

  | [ |- @Types_Circuit _ _ _ (if ?b then _ else _) ]
                                => destruct b; type_check_once

  (* compose_typing : specify goal. *)                                  
  | [ |- @Types_Circuit _ _ _ _ ] =>  eapply compose_typing; type_check_once 

  | [ H : forall a b, Types_Pat _ _ -> Types_Circuit _ _ |- Types_Circuit _ _] 
                                => apply H; type_check_once

  | [ H : @Types_Pat _ _ _ ?p |- @Types_Pat _ _ _ ?p ] 
                                => exact H
  | [ H : @Types_Pat _ ?Γ1 _ ?p |- @Types_Pat _ ?Γ2 _ ?p ] 
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


(** Example **)

Ltac destruct_merges :=
  repeat match goal with
  | [ H : _ == _ ∙ _ |- _ ]  => destruct H
  end.

(* Three typing derivations for a simple circuit *)
(* Corresponds to thesis figure 9.1 *)
Definition cnot12 {Var} : Square_Box Var (Qubit ⊗ Qubit ⊗ Qubit) :=
  box_ (p0,p1,p2) ⇒ 
    gate_ (p3,p4) ← CNOT @(p1,,p2);
    output (p0,,p3,,p4).

(* In functional syntax 
Definition entangle23 : Square_Box (Qubit ⊗ Qubit ⊗ Qubit) :=
  box_ (p0,p1,p2) ⇒ 
    let_ (p3,p4) ← CNOT $ (p1,p2);
    (p0,p3,p4).
*)

Lemma cnot12_WT_manual {Var} : Typed_Box Var cnot12.
Proof.    
  (* manual - no evars *)
  unfold Typed_Box, cnot12. 
  intros Γ p TP. simpl.
  dependent destruction TP.
  dependent destruction TP1.
  rename Γ0 into Γ, Γ1 into Γ0. rename Γ into Γ1.
  rename p3 into p1.
  rename TP1_1 into TP0, TP1_2 into TP1.  
  apply @types_gate with (Γ := Γ0) (Γ1 := Γ1 ⋓ Γ2); try solve_merge.
  - (* type input pattern `(p1,p2)` *)
About types_pair.
    apply (@types_pair _ Γ1 Γ2); try solve_merge.
    + apply TP1. (* types p1 *)
    + apply TP2. (* types p2 *)
  - (* types `output (p0, p3, p4)` *)
    intros Γ Γ' p M TP.
    dependent destruction TP.
    apply (@types_output _ _ _ _ _ eq_refl).
    (* types (p0, p3, p4) *)
    apply (types_pair (Γ0 ⋓ Γ3) (Γ4)); try solve_merge.
    + (* types (p0, p3) *)
      apply (types_pair Γ0 Γ3); try solve_merge.
      * apply TP0. (* types p0 *)
      * apply TP3. (* types p3 *)
    + apply TP4. (* types p4 *)
Qed.
    
Lemma cnot12_WT_evars {Var} : Typed_Box Var cnot12.
Proof.    
  (* manual with evars *)
  unfold Typed_Box, cnot12. 
  intros; simpl.
  invert_patterns.
  eapply types_gate.
  Focus 1.  
    eapply @types_pair. (* types (p1, p2) *)
      4: eauto. (* types p2 *)
      3: eauto. (* types p1 *)
      2: monoid. (* unifies ?Γ = Γ1 ⋓ Γ2 *)
      1: validate. (* solves is_valid (Γ1 ⋓ Γ2) *)
  Focus 2. (* 3 *)
    split. (* _ == _ ∙ _ *) 
      2: monoid. (* unifies Γ0 ⋓ Γ1 ⋓ Γ2 = Γ1 ⋓ Γ2 ⋓ ?Γ *)
      1: validate. (* solves is_valid (Γ0 ⋓ Γ1 ⋓ Γ2) *)
  Focus 1. (* 2 *)
    intros; simpl.
    invert_patterns.
    eapply @types_output.
    Focus 1.
      monoid.
    Focus 1. (* 2 *) 
      destruct_merges; subst.
      eapply @types_pair.
      Focus 4.
        eauto. (* types p4 *)
      Focus 3.
        eapply @types_pair. (* types (p0,p3) *)
          4: eauto. (* types p3 *)
          3: eauto. (* types p0 *)
          2: monoid. (* unifies ?Γ = Γ0 ⋓ Γ3 *)
          1: validate. (* solves is_valid (Γ1 ⋓ Γ2) *)
      Focus 2.
        monoid. (* unifies Γ3 ⋓ Γ4 ⋓ Γ0 = Γ0 ⋓ Γ3 ⋓ Γ4 *)
      Focus 1.   
        validate. (* solves is_valid (Γ1 ⋓ Γ2) *)
Qed.

(* More succint, maybe less readable *)
Lemma cnot23_WT_evars' {Var} : Typed_Box Var cnot12.
Proof.    
  unfold Typed_Box, cnot12. 
  intros; simpl.
  invert_patterns.
  eapply types_gate.
  - eapply @types_pair.
    3: eauto.
    3: eauto.
    2: monoid.
    validate.
  - intros; simpl.
    invert_patterns.
    eapply @types_output.
    + monoid.
    + destruct_merges; subst.
      eapply @types_pair.
      4: eauto.
      Focus 3.
        econstructor.
        3: eauto.
        3: eauto.
        2: monoid.
        validate.
      Unfocus.
      2: monoid.
      subst; validate.
      subst; validate.
  - split. 
    validate.
    monoid.
Qed.  


Lemma cnot23_WT_auto {Var} : Typed_Box Var cnot12.
Proof.    
  (* using only type_check *)
  type_check.
Qed.
