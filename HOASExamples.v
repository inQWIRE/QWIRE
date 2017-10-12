Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import Contexts.
Require Import HOASCircuits.
(* Import TC. *)
Import ListNotations.
Open Scope list_scope.

(** Projecting out elements of tensors **)

Open Scope circ_scope.
Definition wproj {W1 W2} (p : Pat (W1 ⊗ W2)) : Pat W1 * Pat W2 :=
  match p with
  | pair p1 p2 => (p1, p2)  
  end.

(*** Typechecking Tactic ***)

(* Prevent compute from unfolding important fixpoints *)
Open Scope circ_scope.
Opaque wproj.
Opaque merge.
Opaque Ctx.
Opaque is_valid.



(*** Notations ***)

Set Printing Coercions.

(* These tactics construct circuits by calling out to type_check *)


Tactic Notation (at level 0) "make_circ" uconstr(C) := refine C; type_check.

Tactic Notation (at level 0) "box_" uconstr(C) := refine(C); type_check.

Notation letpair p1 p2 p c := (let (p1,p2) := wproj p in c).

Notation "'box_' p ⇒ C" := (box (fun p => C)) (at level 8).
Notation "'box_' () ⇒ C" := (box (fun _ => C)) (at level 8).
(*Notation "( x , y ) ⇒ C" := (box (fun _ z => letpair x y z C)) (at level 8).*)


(* Notations for patterns *)
Notation "()" := unit : circ_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) (at level 0) : circ_scope.


(* Notations for circuits *)
Notation comp p c1 c2 := (compose c1 (fun p => c2)).
Notation "'let_' p ← c1 ; c2" := (comp p c1 c2)
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' () ← c1 ; c2" := 
    (compose c1 (fun _ => c2)) 
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( p1 , p2 ) ← c1 ; c2" := 
    (compose c1 (fun x => letpair p1 p2 x c2)) 
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( p1 , p2 , p3 ) ← c1 ; c2" :=
    (compose c1 (fun x => let (y,p3) := wproj x in
                       let (p1,p2) := wproj y in c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( ( p1 , p2 ) , p3 ) ← c1 ; c2" := 
    (compose c1 (fun x => let (y,p3) := wproj x in
                       let (p1,p2) := wproj y in c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( p1 , ( p2 , p3 ) ) ← c1 ; c2" :=
    (compose c1 (fun x => let (p1,y) := wproj x in
                       let (p2,p3) := wproj y in c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( ( p1 , p2 ) , ( p3 , p4 ) ) ← c1 ; c2" :=
    (compose c1 (fun x => let (y,z) := wproj x in
                       let (p1, p2) := wproj y in
                       let (p3, p4) := wproj z in c2))
                            (at level 12, right associativity) : circ_scope.


Notation "'gate_' p2 ← g @ p ; c2" := (gate g p (fun p2 => c2))
         (at level 12, right associativity).
Notation "'gate_' () ← g @ p ; c2" := (gate g p (fun _ => c2))
         (at level 12, right associativity).
Notation "'gate_' ( p1 , p2 ) ← g @ p ; c2" := 
    (gate g p (fun x => letpair p1 p2 x c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'gate_' ( p1 , p2 , p3 ) ← g @ p ; c2" :=
    (gate g p (fun x => let (y, p3) := wproj x in
                     let (p1, p2) := wproj y in c2))
                           (at level 12, right associativity) : circ_scope.
Notation "'gate_' ( ( p1 , p2 ) , p3 ) ← g @ p ; c2" := 
    (gate g p (fun x => let (y, p3) := wproj x in
                     let (p1, p2) := wproj y in c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'gate_' ( p1 , ( p2 , p3 ) ) ← g @ p ; c2" :=
    (gate g p (fun x => let (p1, y) := wproj x in
                     let (p2, p3) := wproj y in c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'gate_' ( ( p1 , p2 ) , ( p3 , p4 ) ) ← g @ p ; c2" :=
    (gate g p (fun x => let (y, z) := wproj x in
                     let (p1, p2) := wproj y in
                     let (p3, p4) := wproj z in c2))
                            (at level 12, right associativity) : circ_scope.

Notation lift_pat x p c := (lift p (fun x => c)).
Notation "'lift_' x ← p ; c" := (lift_pat x p c) 
         (at level 12, right associativity) : circ_scope.


Notation "'lift_' ( x , y ) ← p ; c" := (let (p1,p2) := wproj p in
                                     lift_pat x p1 (lift_pat y p2 c)) 
         (at level 12, right associativity) : circ_scope.



(* Alt def. of WellTypedness
Definition WT (b : Box) (W1 W2 : WType) :=
*)   


(* Automation *)
(*
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

*)
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


Ltac type_check_once := 
  (* Should not use compute. Unfold what we have to. *)
  (* compute in *; *)
  intros;
  try match goal with 
  | [|- @Typed_Box  ?W1 ?W2 ?c] => unfold Typed_Box in *; try unfold c
  end;
  intros;
  simpl in *;
  subst; 
  invert_patterns;
  repeat match goal with 
  (* Should break this down by case - in lift case, 
     need to choose bit or qubit as appropriate *)
  | [ |- @Types_Circuit _ _ _ ]     => econstructor; type_check_once
  | [ |- @Types_Circuit _ _ (if ?b then _ else _) ] => destruct b; type_check_once
  (* compose_typing : specify goal. *)                                  
  | [ |- @Types_Circuit _ _ _ ]               =>  eapply compose_typing; type_check_once 
  | [ H : forall a b, Types_Pat _ _ -> Types_Circuit _ _ |- Types_Circuit _ _] 
    => apply H; type_check_once
  | [ H : @Types_Pat _ _ ?p |- @Types_Pat _ _ ?p ] => apply H
  | [ |- Types_Pat _ _ ]                   => econstructor; type_check_once
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

Definition id_circ {W} : Box W W :=
  box_ p ⇒ (output p).
Lemma id_circ_WT : forall W, Typed_Box (@id_circ W).
Proof. type_check. Qed.

Definition boxed_gate {W1 W2} (g : Gate W1 W2) : Box W1 W2 := 
  box_ p ⇒   
    gate_ p2 ← g @p;
    output p2.
Lemma boxed_gate_WT {W1 W2} (g : Gate W1 W2) : Typed_Box (boxed_gate g).
Proof. type_check. Qed.

Definition new_discard : Box One One := 
  box_ () ⇒ 
    gate_ b ← new0 @();
    gate_ () ← discard @b;
    output (). 
Lemma new_discard_WT : Typed_Box new_discard.
Proof. type_check. Qed.

Definition init_discard : Box One One:= 
  box_ () ⇒ 
    gate_ q ← init0 @();
    gate_ b ← meas @q;
    gate_ () ← discard @b;
    output (). 
Lemma init_discard_WT : Typed_Box init_discard.
Proof. type_check. Qed.

Definition hadamard_measure : Box Qubit Bit :=
  box_ q ⇒ 
    gate_ q ← H @q;
    gate_ b ← meas @q;
    output b.
Lemma hadamard_measure_WT : Typed_Box hadamard_measure.
Proof. type_check. Qed.

Definition deutsch (U_f : Unitary (Qubit ⊗ Qubit)) : Box One Bit :=
  box_ () ⇒ 
    gate_ x ← init0 @();
    gate_ x ← H @x;
    gate_ y ← init1 @();
    gate_ y ← H @y;
    gate_ (x,y) ← U_f @(x,y);
    gate_ x ← H @x; (* found through verification! *)
    gate_ y ← meas @y;
    gate_ () ← discard @y;
    gate_ x ← meas @x;
    output x.
Lemma deutsch_WT : forall U_f, Typed_Box (deutsch U_f).
Proof. type_check. Qed.

Definition lift_deutsch (U_f : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)) : Box One Bit :=
  box_ () ⇒
    gate_ x    ← init0 @();
    gate_ x    ← H @x;
    gate_ y    ← init1 @();
    gate_ y    ← H @y;
    let_ (x,y) ← unbox U_f (x,y);
    gate_ y    ← meas @y;
    gate_ x ← H @x;
    lift_ _    ← y;
    gate_ x ← meas @x;
    output x.
Lemma lift_deutsch_WT : forall U_f, Typed_Box U_f ->
                               Typed_Box (lift_deutsch U_f).
Proof. type_check. Qed.

Definition init (b : bool) : Box One Qubit :=
  if b then boxed_gate init1 else boxed_gate init0.
Lemma init_WT : forall b, Typed_Box (init b).
Proof. destruct b; type_check. Defined.

Definition inSeq {w1 w2 w3} (c1 : Box w1 w2) (c2 : Box w2 w3): Box w1 w3 :=
  box_ p1 ⇒ 
    let_ p2 ← unbox c1 p1;
    unbox c2 p2.
Lemma inSeq_WT : forall W1 W2 W3 (c1 : Box W1 W2) (c2 : Box W2 W3), 
                 Typed_Box c1 -> Typed_Box c2 -> Typed_Box (inSeq c1 c2).
Proof. type_check. Qed.

Definition inPar {w1 w2 w1' w2'} 
                 (c1 : Box w1 w2) (c2 : Box w1' w2') : Box (w1 ⊗ w1') (w2 ⊗ w2'):=
  box_ p12 ⇒ 
    let_ (p1,p2) ← output p12; 
    let_ p1'     ← unbox c1 p1;
    let_ p2'     ← unbox c2 p2; 
    output (p1',p2').
Lemma inPar_WT : forall W1 W1' W2 W2' (c1 : Box W1 W2) (c2 : Box W1' W2'), 
  Typed_Box c1 -> Typed_Box c2 ->
  Typed_Box (inPar c1 c2).
Proof. type_check. Qed.

(** Teleport **)

Definition bell00 : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒  
    gate_ a ← init0 @();
    gate_ b ← init0 @();
    gate_ a ← H @a;
    gate_ z ← CNOT @(a,b);
    output z.

Lemma bell00_WT : Typed_Box bell00.
Proof. type_check. Qed.

Definition alice : Box (Qubit ⊗ Qubit) (Bit ⊗ Bit) :=
  box_ qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← H @q;
    gate_ x     ← meas @q;
    gate_ y     ← meas @a;
    output (x,y).
Lemma alice_WT : Typed_Box alice.
Proof. type_check. Qed.

Definition bob : Box (Bit ⊗ Bit ⊗ Qubit) Qubit:=
  box_ xyb ⇒ 
    let_ ((x,y),b) ← output xyb ; 
    gate_ (y,b)  ← bit_ctrl σx @(y,b);
    gate_ (x,b)  ← bit_ctrl σz @(x,b);
    gate_ ()     ← discard @y ;   
    gate_ ()     ← discard @x ;
    output b.
Lemma bob_WT : Typed_Box bob.
Proof. type_check. Qed.

Definition teleport :=
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    unbox bob (x,y,b).

Lemma teleport_WT : Typed_Box teleport.
Proof. type_check. Defined.

(* Now simplification is quick! *)
(* Note, however, that there are still hidden "compose"s in teleport,
   since our pairs all use let bindings and composition. 
   Sometimes, having let and compose will be unavoidable, since we name the 
   output of a multi-qubit unitary "x" *)
Lemma eteleport : exists x, teleport = x.
Proof.
  unfold teleport.
  unfold bell00, alice, bob.
  simpl.
(* compute. *)
  eauto.
Qed.

Parameter id_gate: Gate Qubit Qubit.

Definition bob_lift : Box (Bit ⊗ Bit ⊗ Qubit) Qubit :=
  box_ xyb ⇒
    let_ (xy, b) ← output xyb; 
    lift_ (u,v)  ← xy;
    gate_ b      ← (if v then σx else id_gate) @b;
    gate_ b      ← (if u then σz else id_gate) @b;
    output b.
Lemma bob_lift_WT : Typed_Box bob_lift.
Proof. type_check. Defined.

Definition bob_lift' := 
  box_ xyb ⇒
    let_ (xy, b) ← output xyb; 
    lift_ (u,v)  ← xy;
    match u,v with
    | true,  true  => gate_ b ← σx @b; gate_ b ← σz @b; output b
    | true,  false => gate_ b ← σz @b; output b
    | false, true  => gate_ b ← σx @b; output b
    | false, false => output b
    end.
Lemma bob_lift_WT' : Typed_Box bob_lift'.
Proof. type_check. Defined.

Definition teleport_lift : Box Qubit Qubit :=
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    unbox bob_lift (x,y,b).
Lemma teleport_lift_WT : Typed_Box teleport_lift.
Proof. type_check. Defined.


(* teleport lift outside of bob *)
Definition bob_distant (u v : bool) : Box Qubit Qubit :=
  box_ b ⇒
    gate_ b      ← (if v then σx else id_gate) @b;
    gate_ b      ← (if u then σz else id_gate) @b;
    output b.
Lemma bob_distant_WT : forall b1 b2, Typed_Box (bob_distant b1 b2).
Proof. type_check. Defined.

Definition teleport_distant : Box Qubit Qubit :=
  box_ q ⇒
    let_ (a,b)  ← unbox bell00 () ;
    let_ (x,y)  ← unbox alice (q,a) ;
    lift_ (u,v) ← (x,y) ;
    unbox (bob_distant u v) b.
Lemma teleport_distant_WT : Typed_Box teleport_distant.
Proof. type_check. Qed.

Definition teleport_direct :=
  box_ q ⇒  
  (* bell00 *)
    gate_ a     ← init0 @();
    gate_ b     ← init0 @();
    gate_ a     ← H @a;
    gate_ (a,b) ← CNOT @(a,b);

  (* alice *)
    gate_ (q,a) ← CNOT @(q,a);
    gate_ q     ← H @q;
    gate_ x     ← meas @q;
    gate_ y     ← meas @a;

  (* bob *)
    gate_ (y,b)  ← bit_ctrl σx @(y,b);
    gate_ (x,b)  ← bit_ctrl σz @(x,b);
    gate_ ()     ← discard @y;   
    gate_ ()     ← discard @x;
    output b.
Lemma teleport_direct_WT : Typed_Box teleport_direct.
Proof. type_check. Qed.

Lemma teleport_eq : teleport = teleport_direct.
Proof.
  unfold teleport, teleport_direct.
  simpl.
  repeat (f_equal; apply functional_extensionality; intros).
  invert_patterns.
  About letpair.
  assert (H : wproj (qubit v3, qubit v4) = Datatypes.pair (qubit v3) (qubit v4))
    by reflexivity.
  rewrite H. clear H.
  repeat (f_equal; apply functional_extensionality; intros). 
  invert_patterns. 
  assert (H : wproj (qubit v5, qubit v6) = Datatypes.pair (qubit v5) (qubit v6))
    by reflexivity.
  rewrite H; clear H.
  simpl. reflexivity.
Qed.

(* Right associative Tensor *)
Fixpoint NTensor (n : nat) (W : WType) := 
  match n with 
  | 0    => One
  | 1    => W
  | S n' => W ⊗ NTensor n' W
  end.

Infix "⨂" := NTensor (at level 30). 
(* Transparent Tensor. *)
(* Opaque NTensor. *)

Fixpoint inSeqMany (n : nat) {W} (c : Box W W) : Box W W:= 
  match n with
  | 0 => id_circ
  | 1 => c
  | S n' => inSeq c (inSeqMany n' c)
  end.

(* I'd rather be able to prove this directly using type_check *)
Lemma inSeqMany_WT : forall n W (c : Box W W), 
      Typed_Box c -> Typed_Box (inSeqMany n c).
Proof. intros. induction n as [ | [ | ]]; type_check.
Qed.

(* Zero-indexed variant. I don't know why this is necessary *)
(* This will be fairly common *)
(*
Fixpoint inParManyZ (n : nat) {W W'} (c : Box W W') : Box (S n ⨂ W) (S n ⨂ W') :=
  match n with 
  | 0 => c
  | S n' => inPar c (inParManyZ n' c)
  end. 
*)

Program Fixpoint inParMany (n : nat) {W W'} (c : Box W W') : Box (n ⨂ W) (n ⨂ W') := 
  match n with 
  | 0 => id_circ
  | S n' => match n' with
            | 0 => c
            | S n'' => inPar c (inParMany n' c)
            end
  end.

Lemma inParMany_WT : forall n W W' (c : Box W W'), Typed_Box c  -> 
                                 Typed_Box (inParMany n c).
Proof. intros. induction n as [ | [ | n']]; type_check. 
Qed.       


(** Quantum Fourier Transform **)

Parameter RGate : nat -> Unitary Qubit.

(* Check against Quipper implementation *)
(* n + 2 = number of qubits, m = additional argument *)
Fixpoint rotations (n m : nat) {struct n}
                 : Box (Qubit ⊗ (S n ⨂ Qubit)) (Qubit ⊗ (S n ⨂ Qubit)) :=
  match n with
  | 0    => id_circ
  | S n' => match n' with
            | 0 => id_circ
            | S _ => 
               box_ w ⇒
               let_ (c,(q,qs))  ← output w;  
               let_ (c,qs)      ← unbox (rotations n' m) (c,qs);
               gate_ (c,q)      ← ctrl (RGate (m + 2 - n')) @(c,q);
               output (c,(q,qs))
            end
   end.
Lemma rotations_WT : forall n m, 
    Typed_Box (rotations n m).
(* not sure why this used to be easier: induction n; [|destruct n]; type_check.  *)
Proof. 
  induction n as [ | [ | n]]; type_check.
  (* doesn't look like the IH, but actually is *) apply IHn. 
  type_check.
Qed. 


Opaque rotations.
Program Fixpoint qft (n : nat) : Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  match n with 
  | 0    => id_circ
  | S n' => match n' with
           | 0 => boxed_gate H
           | S n'' => box_ qqs ⇒
                     let_ (q,qs) ← output qqs; 
                       let_ qs     ← unbox (qft n') qs; 
                       let_ (q,qs) ← unbox (rotations n'' n') (q,qs);
                       gate_ q     ← H @q;
                       output (q,qs)
           end
  end.
Lemma qft_WT : forall n, Typed_Box  (qft n).
Proof. induction n as [ | [ | n]]; type_check.
       apply rotations_WT; type_check.
Qed.

(** Coin flip **)

Definition coin_flip : Box One Bit :=
  box_ () ⇒
    gate_ q  ← init0 @();
    gate_ q  ← H @q;
    gate_ b  ← meas @q;
    output b.
Lemma coin_flip_WT : Typed_Box coin_flip.
Proof. type_check. Qed.

Fixpoint coin_flips (n : nat) : Box One Bit :=
  box_ () ⇒
  match n with
  | 0    => gate_ x ← new1 @(); output x
  | S n' => let_  c     ← unbox (coin_flips n') ();
           gate_ q     ← init1 @();
           gate_ (c,q) ← bit_ctrl H @(c,q);
           gate_ ()    ← discard @c;
           gate_ b     ← meas @q;
           output b
  end.
Lemma coin_flips_WT : forall n, Typed_Box (coin_flips n).
Proof. intros. induction n; type_check. Qed.

Fixpoint coin_flips_lift (n : nat) : Box One Bit := 
  box_ () ⇒ 
  match n with
  | 0    => gate_ q ← new1 @(); output q
  | S n' => let_ q  ← unbox (coin_flips_lift n') ();
           lift_ x ← q;
           if x then unbox coin_flip ()
                else gate_ q ← new0 @(); output q
  end.
Lemma coin_flips_lift_WT : forall n, Typed_Box (coin_flips_lift n).
Proof. intros. induction n; type_check. Qed.

Definition unitary_transpose {W} (U : Unitary W) : Box W W := 
  box_ p ⇒
    gate_ p ← U @p;
    gate_ p ← transpose U @p;
    output p.
Lemma unitary_transpose_WT : forall W (U : Unitary W), Typed_Box (unitary_transpose U).
Proof. type_check. Qed.

(* Produces qubits *)
Program Fixpoint prepare_basis (li : list bool) : Box One (length li ⨂ Qubit) :=
  match li with
  | []       => id_circ
  | b :: bs => match bs with
               | nil => init b
               | _ :: _ => box_ () ⇒ 
                         let_ p1 ← unbox (init b) (); 
                         let_ p2 ← unbox (prepare_basis bs) ();
                         output (p1, p2)
                end
  end.
Lemma prepare_basis_WT : forall li, 
  Typed_Box (prepare_basis li).
Proof. induction li; [type_check | ].
       destruct li; type_check;
        apply init_WT; assumption.
Qed.

Program Definition lift_eta : Box Bit Qubit :=
  box_ q ⇒ 
    lift_ x ← q;
    unbox (prepare_basis [x]) ().
Lemma lift_eta_bit_WT : Typed_Box lift_eta.
Proof. type_check. apply init_WT. type_check. Qed.
(*Lemma lift_eta_qubit_WT : Typed_Box lift_eta Qubit Qubit.
Proof. econstructor 4; type_check. apply init_WT. constructor. Qed.*)

Definition lift_meas : Box Bit Bit :=
  box_ q ⇒
    lift_ x ← q;
    gate_ p ← (if x then new1 else new0) @();
    output p.
Lemma lift_meas_WT : Typed_Box lift_meas.
Proof. type_check. Qed.
(*Lemma lift_meas_WT' : Typed_Box lift_meas Qubit Bit.
(* Needs to be explicitly told the constructor *)
Proof. econstructor 4; type_check. Qed. 
*)

(** Classical Gates **)

(* NOT already exists *)

Definition AND : Box (Qubit ⊗ Qubit) Qubit :=
  box_ ab ⇒
    let_ (a,b)      ← output ab;
    gate_ z         ← init0 @();
    gate_ (a,(b,z)) ← T @(a,(b,z));
    gate_ a         ← meas @a;
    gate_ b         ← meas @b;
    gate_ ()        ← discard @a;   
    gate_ ()        ← discard @b;   
    output z.
Lemma AND_WT : Typed_Box AND.
Proof. type_check. Qed.

Definition OR : Box (Qubit ⊗ Qubit) Qubit :=
  box_ ab ⇒ 
    let_ (a,b)       ← output ab;
    gate_ a'         ← NOT @a;
    gate_ b'         ← NOT @b;
    let_ z           ← unbox AND (a',b');
    gate_ z'         ← NOT @z;
    output z'.
Lemma OR_WT : Typed_Box OR.
Proof. type_check. Qed.

(** Invalid Circuits **)
Definition absurd_circ : Box Qubit (Bit ⊗ Qubit) :=
  box_ w ⇒ 
    gate_ x  ← meas @w ;
    gate_ w' ← H @w ;
    output (x,w').
Definition absurd_fail : Typed_Box absurd_circ.
Proof. type_check. Abort.

Definition unmeasure : Box Qubit Qubit :=
  box_ q ⇒ 
    gate_ q ← H @q ;
    gate_ b ← meas @q ;
    output q.
Lemma unmeasure_fail : Typed_Box unmeasure.
Proof. type_check. (* not a very useful end state; it's not clear that it's failing *)
Abort.

Definition unused_qubit : Box Qubit One :=
  box_ w ⇒ 
   gate_ w ← H @w ;
   output ().
Lemma unused_qubit_fail : Typed_Box unused_qubit.
Proof. type_check. Abort.

Definition clone : Box Qubit (Qubit ⊗ Qubit) := box_ p ⇒ (output (p,p)).
Lemma clone_WT : Typed_Box clone.
Proof. type_check. Abort.

Program Definition split_qubit : Box Qubit (Qubit ⊗ Qubit) :=
  box_ w ⇒ 
    let_ (w1,w2)  ← output w ;
    gate_ w2'     ← H @w2 ; 
    output (w1,w2').
Next Obligation. Abort.

Close Scope circ_scope.
(* *)