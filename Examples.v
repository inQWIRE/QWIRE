Require Import Arith.
Require Import List.
Require Import Contexts.
Import ListNotations.
Open Scope list_scope.

(*
Notation "W1 ⊗ W2" := (Tensor W1 W2) (at level 50). 

(* Our gate set *)
Parameter H : Gate.
Parameter CNot : Gate.
Parameter σx σy σz : Gate. 
Parameter meas : Gate.

(* Gate Signatures *)
(*
Parameter H_type : (GateWType H Qubit Qubit).
Parameter σx_type : (GateWType σx Qubit Qubit). 
Parameter σy_type : (GateWType σy Qubit Qubit). 
Parameter σz_type : (GateWType σz Qubit Qubit). 
Parameter CNot_type : (GateWType CNot (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)).

Parameter meas_type : (GateWType meas Qubit Bit).

*)

(*
Inductive GateWType : Gate -> WType -> WType -> Set :=
  | H_type: (GateWType H Qubit Qubit)
  | σx_type : (GateWType σx Qubit Qubit) 
  | σy_type : (GateWType σy Qubit Qubit) 
  | σz_type : (GateWType σz Qubit Qubit) 
  | CNot_type : (GateWType CNot (Qubit ⊗ Qubit) (Qubit ⊗ Qubit))
  | meas_type : (GateWType meas Qubit Bit).
*)

Definition GetGateType (g : Gate) :=
  match g with 
  | H => GateWType H Qubit Qubit
  | σx => (GateWType σx Qubit Qubit) 
  | σy => (GateWType σy Qubit Qubit) 
  | σz => (GateWType σz Qubit Qubit) 
  | CNot => (GateWType CNot (Qubit ⊗ Qubit) (Qubit ⊗ Qubit))
  | meas => (GateWType meas Qubit Bit)
  end.
*)

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



(* These only work for simple patterns *)

Fixpoint get_context' (v : Var) (W : WType) : Ctx := 
  match v with
  | O => [Some W]
  | (S v') => None :: get_context' v' W
  end.

(*
Definition get_context (p : Pat) (W : WType) : Ctx :=
  match p with
  | var v => get_context' v W
  | _ => []
  end.
*)

Open Scope default_scope.

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

Close Scope default_scope.
Open Scope circ_scope.

Fixpoint get_context (p : Pat) (W : WType) : Ctx :=
  match p with
  | var v => get_context' v W
  | unit => []
  | pair p1 p2 => match W with 
               | W1 ⊗ W2 => manual_merge (get_context p1 W1) (get_context p2 W2)
               | _ => [] (* Fails *)
               end
  end.



(*** Tactics ***)

(*
Ltac type_check_circ :=
  simpl; 
  repeat (match goal with
    | [ |- GateWType _ _ _ ]   => constructor (* unique *)
    | [ |- EmptyCtx _ ]        => constructor (* unique *)
    | [ |- SingletonCtx _ _ _] => constructor (* unique *)
    | [ |- WF_Pat _ _ _ ]      => constructor (* easy in the Bit/Qubit case *)
    | [ |- WF_Circuit _ _ _]   => econstructor 
  end);
  repeat match goal with
    | [ |- MergeCtx _ _ _] => repeat constructor (* multiple options: always last *)
  end.
*)

(* Works - general
Ltac type_check_circ :=
  compute; (* just to unfold obligations, actually *)
  repeat match goal with
    | [ |- GateWType _ _ _ ]   => constructor (* unique *)
    | [ |- EmptyCtx _ ]        => constructor (* unique *)
    | [ |- SingletonCtx _ _ _] => constructor (* unique *)
    | [ |- WF_Pat _ _ _ ]      => econstructor (* easy in the Bit/Qubit case *)
  end;
  repeat match goal with
    | [ |- MergeCtx [] _ _]    => constructor (* two ctxs must be concrete *)
    | [ |- MergeCtx _ [] _]    => constructor
    | [ |- MergeCtx _ _ []]    => constructor
    | [ |- MergeCtx (?c1::?ctx1) (?c2::?ctx2) _]    => constructor
    | [ |- MergeCtx (?c1::?ctx1) _ (?c::?ctx)]      => constructor
    | [ |- MergeCtx _ (?c2::?ctx2) (?c::?ctx)]      => constructor
    | [ |- MergeOption _ _ _]  => constructor
  end;
  repeat match goal with
    | [ |- WF_Circuit _ _ _]   => econstructor; type_check_circ
    | [ |- MergeCtx _ _ _]     => (* constructor; *) type_check_circ (* go back! *)
  end.
*)

(* Works - precise 
Ltac type_check_circ :=
  compute; (* just to unfold obligations, actually *)
  repeat match goal with
  | [ |- GateWType _ _ _ ]        => constructor (* unique *)
  | [ |- EmptyCtx _ ]             => apply EmptyNil (* not fine! *)
  | [ |- SingletonCtx 0 _ _]      => apply SingletonHere (* unique *)
  | [ |- SingletonCtx (S ?n) _ _] => apply SingletonLater (* unique *)
  | [ |- WF_Pat _ unit _ ]        => apply wf_unit (* unit case *)
  | [ |- WF_Pat _ (var ?v) _ ]    => apply wf_var (* variable. w inferred later? *)
  | [ |- WF_Pat _ (pair ?p1 ?p2) _ ]  => eapply wf_pair (* g1 g2 exist. quantified *)
  end;
  repeat match goal with (* two ctxs must be concrete *)
  | [ |- MergeCtx [] _ _]                        => apply MergeNilL
  | [ |- MergeCtx _ [] _]                        => apply MergeNilR
  | [ |- MergeCtx _ _ []]                        => apply MergeNilL (* Both work *)
  | [ |- MergeCtx (?c1::?ctx1) (?c2::?ctx2) _]   => apply MergeCons
  | [ |- MergeCtx (?c1::?ctx1) _ (?c::?ctx)]     => apply MergeCons
  | [ |- MergeCtx _ (?c2::?ctx2) (?c::?ctx)]     => apply MergeCons
  | [ |- MergeOption (Some ?w) _ _]              => apply MergeLeft
  | [ |- MergeOption _ (Some ?w) _]              => apply MergeRight
  | [ |- MergeOption None None _]                => apply MergeNone
  | [ |- MergeOption _ _ None]                   => apply MergeNone
  end;
  repeat match goal with
  | [ |- WF_Circuit _ _ _]   => econstructor; type_check_circ
  | [ |- MergeCtx _ _ _]     => (* constructor; *) type_check_circ (* go back! *)
  end.
*)

(*
Ltac type_check_circ :=
  compute; (* just to unfold obligations, actually *)
  repeat match goal with
  | [ |- Unitary _ ]              => constructor (* unique *)
  | [ |- GateWType _ _ _ ]        => constructor (* unique *)
  | [ |- SingletonCtx 0 _ _]      => apply SingletonHere (* unique *)
  | [ |- SingletonCtx (S ?n) _ _] => apply SingletonLater (* unique *)
  | [ |- EmptyCtx _ ]             => apply EmptyNil (* now only option *) 
  | [ |- WF_Pat _ unit _ ]        => apply wf_unit (* unit case *)
  | [ |- WF_Pat _ (var ?v) _ ]    => apply wf_var (* variable. w inferred later? *)
  | [ |- WF_Pat _ (pair ?p1 ?p2) _ ]  => eapply wf_pair (* g1 g2 exist. quantified *)
  end;
  repeat match goal with (* two ctxs must be concrete *)
  | [ |- MergeCtx [] _ _]                        => apply MergeNilL
  | [ |- MergeCtx _ [] _]                        => apply MergeNilR
  | [ |- MergeCtx _ _ []]                        => apply MergeNilL (* Both work *)
  | [ |- MergeCtx (?c1::?ctx1) (?c2::?ctx2) _]   => apply MergeCons
  | [ |- MergeCtx (?c1::?ctx1) _ (?c::?ctx)]     => apply MergeCons
  | [ |- MergeCtx _ (?c2::?ctx2) (?c::?ctx)]     => apply MergeCons
  | [ |- MergeOption (Some ?w) _ _]              => apply MergeLeft
  | [ |- MergeOption _ (Some ?w) _]              => apply MergeRight
  | [ |- MergeOption None None _]                => apply MergeNone
  | [ |- MergeOption _ _ None]                   => apply MergeNone
  | [ |- MergeOption None _ (Some ?w)]           => apply MergeRight
  | [ |- MergeOption _ None (Some ?w)]           => apply MergeLeft
  | [ |- WF_Circuit _ _ _]                       => econstructor; type_check_circ
  end.
*)

(*
Ltac tcheck1 :=
  compute; (* just to unfold obligations, actually *)
  match goal with
  | [ |- Unitary _ ]              => constructor (* unique *)
  | [ |- GateWType _ _ _ ]        => constructor (* unique *)
  | [ |- EmptyCtx _ ]             => apply EmptyNil (* dangerous? *) 
  | [ |- SingletonCtx 0 _ _]      => apply SingletonHere (* unique *)
  | [ |- SingletonCtx (S ?n) _ _] => apply SingletonLater (* unique *)
  | [ |- WF_Pat _ unit _ ]        => apply wf_unit (* unit case *)
  | [ |- WF_Pat _ (var ?v) _ ]    => apply wf_var (* variable. w inferred later? *)
  | [ |- WF_Pat _ (pair ?p1 ?p2) _ ]  => eapply wf_pair (* g1 g2 exist. quantified *)
  end.

Ltac tcheck2 :=
  match goal with (* two ctxs must be concrete *)
  | [ |- MergeCtx [] _ _]                        => apply MergeNilL
  | [ |- MergeCtx _ [] _]                        => apply MergeNilR
  | [ |- MergeCtx _ _ []]                        => apply MergeNilL (* Both work *)
  | [ |- MergeCtx (?c1::?ctx1) (?c2::?ctx2) _]   => apply MergeCons
  | [ |- MergeCtx (?c1::?ctx1) (?c::?ctx) (?c::?ctx)]     => apply MergeCons
  | [ |- MergeOption (Some ?w) _ _]              => apply MergeLeft
  | [ |- MergeOption _ (Some ?w) _]              => apply MergeRight
  | [ |- MergeOption None None _]                => apply MergeNone
  | [ |- MergeOption _ _ None]                   => apply MergeNone
  | [ |- MergeOption None _ (Some ?w)]           => apply MergeRight
  | [ |- MergeOption _ None (Some ?w)]           => apply MergeLeft
  | [ |- WF_Circuit _ _ _]                       => econstructor
  end.
*)

Ltac type_check_circ :=
  try (progress (
  compute; (* just to unfold obligations, actually *)
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
  | [ |- MergeCtx (?c::?ctx) _ (?c::?ctx)]       => apply MergeNilR (*dangerous set *)
  | [ |- MergeCtx _ (?c::?ctx) (?c::?ctx)]       => apply MergeNilL (*dangerous set *)
  | [ |- MergeCtx (?c1::?ctx1) _  (?c::?ctx)]    => apply MergeCons (*dangerous set *)
  | [ |- MergeCtx _ (?c2::?ctx2) (?c::?ctx)]     => apply MergeCons (*dangerous set *)
  | [ |- MergeOption (Some ?w) _ _]              => apply MergeLeft
  | [ |- MergeOption _ (Some ?w) _]              => apply MergeRight
  | [ |- MergeOption None None _]                => apply MergeNone
  | [ |- MergeOption _ _ None]                   => apply MergeNone
  | [ |- MergeOption None _ (Some ?w)]           => apply MergeRight
  | [ |- MergeOption _ None (Some ?w)]           => apply MergeLeft
  | [ |- WF_Circuit _ _ _]                       => econstructor
  end )); type_check_circ).

(*** Paper Examples ***)

(*
Definition hadamard_measure_c : Circuit := 
gate H w0 w1 (gate meas w1 w2 (output w2)).

Program Definition hadamard_measure : Boxed_Circ Qubit Bit  :=
  box _ w0 hadamard_measure_c _ _. 
*)


Program Definition hadamard_measure : Boxed_Circ Qubit Bit :=
  box _ w 
    (gate H w w' 
    (gate meas w' b 
    (output b))) _ _.
Obligation 1. apply (get_context w Qubit). Defined.
Obligation 2. type_check_circ. Defined.
Obligation 3. type_check_circ. Defined.

(*

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

(* This fails to type check *)
Program Definition absurd_circ : Boxed_Circ Qubit (Bit ⊗ Qubit) := 
  box _ w
    (gate meas w x 
    (gate H w w'
    (output (x,w')))) _ _.
Obligation 1. apply (get_context w Qubit). Defined.
Obligation 2. type_check_circ. Defined.
Obligation 3. type_check_circ. Admitted. (* Doesn't Typecheck *)

Program Definition inSeq {W1 W2 W3 : WType} 
  (c1 : Boxed_Circ W1 W2) (c2 : Boxed_Circ W2 W3) : Boxed_Circ W1 W3  := 
  box _ w1 
    (compose w2 (unbox c1 w1) (unbox c2 w2)) _ _.
Obligation 1. apply (get_context w1 W1). Defined.
Obligation 2. type_check_circ. Defined.
Obligation 3. simpl. type_check_circ. Admitted. (* subst not yet defined *)

Program Definition inPar {W1 W2 W1' W2'} 
  (c : Boxed_Circ W1 W2) (c' : Boxed_Circ W1' W2') : Boxed_Circ (W1⊗W1') (W2⊗W2') :=
  box _ (w1,w1')
    (compose w2 (unbox c w1) (
       compose w2 (unbox c' w1') (output (w2,w2')))) _ _.
Obligation 1. apply (get_context (w1,w1') (W1⊗W1')). Defined.
Obligation 2. type_check_circ. Defined.
Obligation 3. type_check_circ. Admitted. (* subst not yet defined *)


Program Definition init (b : bool) : Boxed_Circ One Qubit := 
  if b then (box _ unit (gate init1 unit w (output w)) _ _)
       else (box _ unit (gate init0 unit w (output w)) _ _).
Obligation 1. apply []. Defined.
Obligation 2. type_check_circ. Defined.
Obligation 3. type_check_circ. Defined.
Obligation 4. apply []. Defined.
Obligation 5. type_check_circ. Defined.
Obligation 6. type_check_circ. Defined.

Program Definition bell00 : Boxed_Circ One (Qubit ⊗ Qubit) :=
  box _ unit
    (gate init0 unit a
    (gate init0 unit b
    (gate H a a
    (gate CNot (a,b) (a,b)
    (output (a,b)))))) _ _.
Obligation 1. apply []. Defined.
Obligation 2. type_check_circ. Defined.
Obligation 3. type_check_circ. Defined. 

(*
  compute.
  econstructor.
  constructor. (* apply MergeNilR. *)
  apply MergeNilR.
  constructor.
  repeat constructor.
  repeat constructor.

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

  econstructor.
  3: constructor.
  Focus 3.
    econstructor; [| repeat constructor | repeat constructor].
    repeat constructor.
  repeat constructor.
  Focus 2.
    econstructor; [| repeat constructor | repeat constructor].
    repeat constructor.
  repeat constructor.
  
  econstructor.
  econstructor.
  2: repeat constructor.
  2: repeat constructor.
  repeat constructor.


type_check_circ. Defined.
*)

(*
econstructor;

(repeat match goal with
          | |- GateWType _ _ _ => constructor | _ => idtac end).



[ > match goal with 
    | |- GateWType _ _ _ => constructor | _ => idtac end ..].


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

  econstructor.
  3: constructor.
  3: repeat constructor.
  3: repeat constructor.
  repeat constructor.
  repeat constructor.

  econstructor.
  3: constructor.
  Focus 3.
    econstructor; [| repeat constructor | repeat constructor].
    repeat constructor.
  repeat constructor.
  Focus 2.
    econstructor; [| repeat constructor | repeat constructor].
    repeat constructor.
  repeat constructor.
  
  econstructor.
  econstructor.
  2: repeat constructor.
  2: repeat constructor.
  repeat constructor.
Defined.
*)

Program Definition alice : Boxed_Circ (Qubit⊗Qubit) (Bit⊗Bit) :=
  box _ (q,a)
    (gate CNot (q,a) (q,a)
    (gate H q q
    (gate meas q x
    (gate meas a y
    (output (x,y)))))) _ _.
Obligation 1. apply (get_context (q,a) (Qubit⊗Qubit)). Defined.
Obligation 2. type_check_circ. Defined.
Obligation 3. type_check_circ. Defined.

 (* Fails: type_check_circ. 2: constructor.*)
(* tcheck1. tcheck2. all:tcheck1. all:tcheck2. all:tcheck2. Defined. *)


(*
  econstructor.
  3: constructor.
  3: econstructor. 
  4: repeat constructor. 
  4: repeat constructor. 
  4: econstructor. 
  5:repeat constructor.  
  5:repeat constructor.  
  3:repeat constructor.  
  3:repeat constructor.
  compute.
  constructor.
  constructor.

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

  econstructor.
  3: constructor.
  3: repeat constructor. 
  3: repeat constructor. 
  repeat constructor. 
  repeat constructor. 

  econstructor.
  econstructor.
  2: repeat constructor. 
  2: repeat constructor. 
  repeat constructor. 
Defined.
*)

Program Definition bob : Boxed_Circ (Bit⊗Bit⊗Qubit) Qubit :=
  box _ (x,y,b)
    (gate (bit_control σx) (y,b) (y,b)
    (gate (bit_control σz) (x,b) (x,b)
    (gate discard y unit 
    (gate discard x unit
    (output b))))) _ _.
Obligation 1. apply (get_context (x,y,b) (Bit⊗Bit⊗Qubit)). Defined.
Obligation 2. type_check_circ. Defined.
Obligation 3. type_check_circ. Defined. 

Program Definition teleport : Boxed_Circ Qubit Qubit :=
  box _ q
    (compose (a,b) (unbox bell00 unit)
    (compose (x,y) (unbox alice (q,a))
    (unbox bob (x,y,b)))) _ _.
Obligation 1. apply (get_context q Qubit). Defined.
Obligation 2. type_check_circ. Defined.
Obligation 3. type_check_circ. Admitted.

