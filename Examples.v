Require Import Arith.
Require Import List.
Require Import Contexts.
Import ListNotations.
Open Scope list_scope.

(* Some wire patterns *)
Definition q   := var 0.
Definition w   := var 1.
Definition w'  := var 2.
Definition a   := var 3.
Definition b   := var 4.
Definition x   := var 5.
Definition y   := var 6.
Definition w1  := var 7.
Definition w1' := var 8.
Definition w2  := var 9.
Definition w2' := var 10.
 
(* Getting contexts for input patterns *)

Open Scope default_scope.

Fixpoint get_singleton (v : Var) (W : WType) : Ctx := 
  match v with
  | O => [Some W]
  | (S v') => None :: get_singleton v' W
  end.

Fixpoint manual_merge_atom (W1 W2 : option WType) : option WType := 
  match W1, W2 with
  | None, W' => W'
  | W', None => W'
  | _, _     => None (* ERROR CASE *) 
  end.

Fixpoint manual_merge (ctx1 ctx2 : Ctx) : Ctx :=
  match (ctx1, ctx2) with 
  | [], _ => ctx2
  | _, [] => ctx1
  | (c1 :: ctx1'), (c2 :: ctx2') => 
    (manual_merge_atom c1 c2) :: (manual_merge ctx1' ctx2')
  end.

Fixpoint make_context (p : Pat) (W : WType) : Ctx :=
  match p with
  | var v => get_singleton v W
  | unit => []
  | pair p1 p2 => match W with 
               | W1 ⊗ W2 => manual_merge (make_context p1 W1) (make_context p2 W2)
               | _ => [] (* Fails *)
               end
  end.


(* Should be element of, but company coq is annoying *)
(* Infix " ⊂ " := get_context (at level 50). *)

Notation "'Box' w ⊂ W => C" := (box (make_context w W) w C _ _) (at level 60) 
                               : circ_scope.

Close Scope default_scope.
Open Scope circ_scope.


(*** Tactics ***)

Ltac type_check_circ :=
  try (progress (
  intros; compute; (* just to unfold obligations, actually *)
  repeat (
  [ > repeat match goal with
  | [ |- Unitary _ ]              => constructor (* unique *)
  | [ |- GateWType _ _ _ ]        => constructor (* unique *)
  | [ |- SingletonCtx 0 _ _]      => apply SingletonHere (* unique *)
  | [ |- SingletonCtx (S ?n) _ _] => apply SingletonLater (* unique *)
  | [ |- EmptyCtx _ ]             => apply EmptyNil (* now only option *) 
  | [ |- WF_Pat _ unit _ ]        => apply wf_unit (* unit case *)
  | [ |- WF_Pat _ (var ?v) _ ]    => apply wf_var (* variable. w inferred later? *)
  | [ |- WF_Pat _ (pair ?p1 ?p2) _ ]  => eapply wf_pair (* g1 g2 exist. quantified *)
  end ..];
  match goal with (* two ctxs must be concrete *)
  | [ |- MergeCtx [] _ _]                        => apply MergeNilL
  | [ |- MergeCtx _ [] _]                        => apply MergeNilR
  | [ |- MergeCtx _ _ []]                        => apply MergeNilL (* Both work *)
  | [ |- MergeCtx (?c1::?ctx1) (?c2::?ctx2) _]   => apply MergeCons
  | [ |- MergeCtx (?c::?ctx) _ (?c::?ctx)]       => apply MergeNilR (* identical *)
  | [ |- MergeCtx _ (?c::?ctx) (?c::?ctx)]       => apply MergeNilL (* identical *)
  | [ |- MergeCtx (?c1::?ctx1) _  (?c::?ctx)]    => apply MergeCons (* distinct *)
  | [ |- MergeCtx _ (?c2::?ctx2) (?c::?ctx)]     => apply MergeCons (* distinct *)
  | [ |- MergeOption (Some ?w) _ _]              => apply MergeLeft
  | [ |- MergeOption _ (Some ?w) _]              => apply MergeRight
  | [ |- MergeOption None None _]                => apply MergeNone
  | [ |- MergeOption _ _ None]                   => apply MergeNone
  | [ |- MergeOption None _ (Some ?w)]           => apply MergeRight
  | [ |- MergeOption _ None (Some ?w)]           => apply MergeLeft
  | [ |- WF_Circuit _ _ _]                       => econstructor
  end )); type_check_circ).

(*** Paper Examples ***)

Local Obligation Tactic := type_check_circ.

Program Definition hadamard_measure : Boxed_Circ Qubit Bit :=
  Box w ⊂ Qubit => 
    (gate H w w' 
    (gate meas w' b 
    (output b))).

(* Explicit Proof:

  unfold hadamard_measure_obligation_1. simpl.
  econstructor.
  3: constructor.
  3: repeat constructor.
  3: repeat constructor.  
  repeat constructor.
  repeat constructor.
  econstructor.
  3: constructor.
  3: repeat constructor.
  3: repeat constructor.
  repeat constructor.
  repeat constructor.
  constructor.
  repeat constructor.
Defined.
*)

(* This - correctly - fails to type check!*)
(*
Program Definition absurd_circ : Boxed_Circ Qubit (Bit ⊗ Qubit) := 
  Box w ⊂ Qubit =>
    (gate meas w x 
    (gate H w w'
    (output (x,w')))).
Obligation 2. Abort. 
*)

Program Definition inSeq {W1 W2 W3 : WType} 
  (c1 : Boxed_Circ W1 W2) (c2 : Boxed_Circ W2 W3) : Boxed_Circ W1 W3  := 
  Box w1 ⊂ W1 =>
    (compose w2 (unbox c1 w1) (unbox c2 w2)).
Obligation 2. type_check_circ. Admitted. (* subst not yet defined *)

Program Definition inPar {W1 W2 W1' W2'} 
  (c : Boxed_Circ W1 W2) (c' : Boxed_Circ W1' W2') : Boxed_Circ (W1⊗W1') (W2⊗W2') :=
  Box (w1,w1') ⊂ (W1 ⊗ W1') =>
    (compose w2 (unbox c w1) (
       compose w2 (unbox c' w1') (output (w2,w2')))).
Obligation 2. type_check_circ. Admitted. (* subst not yet defined *)


Program Definition init (b : bool) : Boxed_Circ One Qubit := 
  if b then (Box unit ⊂ One => (gate init1 unit w (output w)))
       else (Box unit ⊂ One => (gate init0 unit w (output w))).

Program Definition bell00 : Boxed_Circ One (Qubit ⊗ Qubit) :=
  Box unit ⊂ One =>
    (gate init0 unit a
    (gate init0 unit b
    (gate H a a
    (gate CNot (a,b) (a,b)
    (output (a,b)))))).

Program Definition alice : Boxed_Circ (Qubit⊗Qubit) (Bit⊗Bit) :=
  Box (q,a) ⊂ Qubit⊗Qubit =>
    (gate CNot (q,a) (q,a)
    (gate H q q
    (gate meas q x
    (gate meas a y
    (output (x,y)))))).

Program Definition bob : Boxed_Circ (Bit⊗Bit⊗Qubit) Qubit :=
  Box (x,y,b) ⊂ (Bit⊗Bit⊗Qubit) =>
    (gate (bit_control σx) (y,b) (y,b)
    (gate (bit_control σz) (x,b) (x,b)
    (gate discard y unit 
    (gate discard x unit
    (output b))))).

Program Definition teleport : Boxed_Circ Qubit Qubit :=
  Box q ⊂ Qubit =>
    (compose (a,b) (unbox bell00 unit)
    (compose (x,y) (unbox alice (q,a))
    (unbox bob (x,y,b)))).
Obligation 2. type_check_circ. Admitted.

(* For when run is implemented: *)

Parameter run : Circuit -> bool.

Program Definition flip : bool := 
  run 
  (gate init0 unit q
  (gate H q q
  (gate meas q b
  (output b)))).



(* *)