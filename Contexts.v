Require Import Arith.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Inductive WType := Qubit | Bit | One | Tensor : WType -> WType -> WType.

Notation "W1 ⊗ W2" := (Tensor W1 W2) (at level 1, left associativity): circ_scope. 

Open Scope circ_scope.

(* Coq interpretations of wire types *)
Fixpoint interpret (w:WType) : Set :=
  match w with
    | Qubit => bool
    | Bit => bool 
    | One => Datatypes.unit
    | Tensor w1 w2 => (interpret w1) * (interpret w2)
  end.

(*
Inductive NCtx := 
  End : WType -> NCtx
| Cons : option WType -> NCtx -> NCtx.
Inductive Ctx := Empty | NEmpty : NCtx -> Ctx.
*)
Definition Var := nat.
Definition Ctx := list (option WType).

(* Padding with nones is dangerous! Trying alternative.
Inductive EmptyCtx : Ctx -> Set :=
| EmptyNil : EmptyCtx []
| EmptyCons : forall ctx, EmptyCtx ctx -> EmptyCtx (None :: ctx)
.

Inductive SingletonCtx : Var -> WType -> Ctx -> Set :=
| SingletonHere : forall w ctx, EmptyCtx ctx -> SingletonCtx 0 w (Some w :: ctx)
| SingletonLater : forall x w ctx, SingletonCtx x w ctx -> SingletonCtx (S x) w (None :: ctx)
.
*)

(* Temporarily leaving this. If it works, can delete. *)
Inductive EmptyCtx : Ctx -> Set := EmptyNil : EmptyCtx [].

Inductive SingletonCtx : Var -> WType -> Ctx -> Set :=
| SingletonHere : forall w, SingletonCtx 0 w [Some w]
| SingletonLater : forall x w ctx, SingletonCtx x w ctx -> SingletonCtx (S x) w (None :: ctx).

(* Dead Code? 
Inductive AddCtx : Var -> WType -> Ctx -> Ctx -> Set :=
| AddHere : forall w ctx, AddCtx 0 w (None :: ctx) (Some w :: ctx)
| AddLater : forall x w ctx ctx' m, AddCtx x w ctx ctx' -> AddCtx (S x) w (m :: ctx) (m :: ctx')
.
*)

Inductive MergeOption : option WType -> option WType -> option WType -> Set :=
| MergeNone : MergeOption None None None
| MergeLeft : forall a, MergeOption (Some a) None (Some a)
| MergeRight : forall a, MergeOption None (Some a) (Some a)
.

Inductive MergeCtx : Ctx -> Ctx -> Ctx -> Set :=
| MergeNilL : forall ctx, MergeCtx [] ctx ctx
| MergeNilR : forall ctx, MergeCtx ctx [] ctx
| MergeCons : forall o1 o2 o g1 g2 g, 
              MergeOption o1 o2 o -> MergeCtx g1 g2 g -> MergeCtx (o1 :: g1) (o2 :: g2) (o :: g)
.

(* Syntax *)

Inductive Pat := var : Var -> Pat | unit | pair : Pat -> Pat -> Pat.

(* Dangerous to take this notation *)
Notation "a , b" := (Datatypes.pair a b) (at level 11, left associativity) : default_scope.
Notation "w1 , w2" := (pair w1 w2) (at level 11, left associativity) : circ_scope.
(* Notation "()" := unit : circ_scope. *)

(*
Parameter (Gate : Set).

Parameter (GateWType : Gate -> WType -> WType -> Set).
*)

Inductive Gate : Set := 
  | H | σx | σy | σz | CNot 
  | init0 | init1 | new0 | new1 | meas | discard
  | control : Gate -> Gate
  | bit_control : Gate -> Gate
  | transpose : Gate -> Gate
.

Inductive Unitary : Gate -> Set := 
  | U_H : Unitary H | U_σx : Unitary σx | U_σy : Unitary σy | U_σz : Unitary σz 
  | U_CNot : Unitary CNot 
  | U_control : forall g, Unitary g -> Unitary (control g)
  | U_bit_control : forall g, Unitary g -> Unitary (bit_control g)
  | U_transpose : forall g, Unitary g -> Unitary (transpose g)
.

(* We have GateWType guarantee that only unitary gates are controlled/transposed *)
Inductive GateWType : Gate -> WType -> WType -> Set :=
  | H_type: (GateWType H Qubit Qubit)
  | σx_type : (GateWType σx Qubit Qubit) 
  | σy_type : (GateWType σy Qubit Qubit) 
  | σz_type : (GateWType σz Qubit Qubit) 
  | CNot_type : (GateWType CNot (Qubit ⊗ Qubit) (Qubit ⊗ Qubit))
  | init0_type : (GateWType init0 One Qubit)
  | init1_type : (GateWType init1 One Qubit)
  | new0_type : (GateWType new0 One Bit)
  | new1_type : (GateWType new1 One Bit)
  | meas_type : (GateWType meas Qubit Bit)
  | discard_type : (GateWType discard Bit One)
  | control_type : forall g W, Unitary g -> GateWType g W W -> 
                              GateWType (control g) (Qubit⊗W) (Qubit⊗W)
  | bit_control_type : forall g W, Unitary g -> GateWType g W W -> 
                              GateWType (bit_control g) (Bit⊗W) (Bit⊗W)
  | transpose_type : forall g W, Unitary g -> GateWType g W W -> 
                              GateWType (transpose g) W W
. 

Inductive Circuit  :=
| output : Pat -> Circuit
| gate : Gate -> Pat -> Pat -> Circuit -> Circuit (* 1st pat is input, 2nd output *)
| lift : forall {w:WType}, Pat -> (interpret w -> Circuit) -> Circuit
.

Notation "p2 <- 'gate' g p1 ; C" := (gate g p1 p2) (at level 10) : circ_scope.
Delimit Scope circ_scope with circ.

(* Lift notation? *)

Inductive WF_Pat : Ctx -> Pat -> WType -> Set :=
| wf_var  : forall x w ctx, SingletonCtx x w ctx -> WF_Pat ctx (var x) w
| wf_unit : forall ctx, EmptyCtx ctx -> WF_Pat ctx unit One
| wf_pair : forall g1 g2 g w1 w2 p1 p2, 
            MergeCtx g1 g2 g -> WF_Pat g1 p1 w1 -> WF_Pat g2 p2 w2 
         -> WF_Pat g (pair p1 p2) (Tensor w1 w2)
.

Inductive WF_Circuit : Ctx -> Circuit -> WType -> Set :=
| wf_output : forall ctx p w, WF_Pat ctx p w -> WF_Circuit ctx (output p) w
| wf_gate   : forall ctx ctx1 ctx2 ctx1' ctx2' g p1 p2 c w1 w2 w,
              MergeCtx ctx1 ctx ctx1'
           -> MergeCtx ctx2 ctx ctx2'
           -> GateWType g w1 w2
           -> WF_Pat ctx1 p1 w1
           -> WF_Pat ctx2 p2 w2
           -> WF_Circuit ctx2' c w
           -> WF_Circuit ctx1' (gate g p1 p2 c) w
| wf_lift   : forall ctx1 ctx2 ctx p w w' f,
              MergeCtx ctx1 ctx2 ctx
           -> WF_Pat ctx1 p w
           -> (forall (x:interpret w), WF_Circuit ctx2 (f x) w')
           -> WF_Circuit ctx (lift p f) w'
.

Fixpoint subst (p' : Pat) (p : Pat) (c : Circuit) : Circuit.
Admitted.
(* Substitution has all these restrictions on p being concrete... 
   can we get rid of that? *)


Inductive Boxed_Circ : WType -> WType -> Set := 
| box : forall w1 w2 ctx p c, WF_Pat ctx p w1 -> WF_Circuit ctx c w2 -> Boxed_Circ w1 w2
.

Arguments box {w1} {w2} _ p c _ _.

Definition unbox {w1} {w2} (c : Boxed_Circ w1 w2) p' : Circuit :=
  match c with
    | box _ p c _ _ => subst p' p c
  end.
Lemma wf_unbox : forall ctx w1 w2 p (c : Boxed_Circ w1 w2),
                 WF_Pat ctx p w1 -> WF_Circuit ctx (unbox c p) w2.
Admitted.


Fixpoint compose  (p : Pat) (c:Circuit) (c' : Circuit) : Circuit :=
  match c with
    | output p' => subst p' p c'
    | gate p2 g p1 c => gate p2 g p1 (compose p c c')
    | lift p' f => lift p' (fun x => compose p (f x) c')
  end.

Lemma wf_compose : forall ctx ctx1 ctx2 ctx1' ctx2' p c c' w w',
      MergeCtx ctx1 ctx ctx1'
   -> MergeCtx ctx2 ctx ctx2'
   -> WF_Circuit ctx1 c w
   -> WF_Pat ctx2 p w
   -> WF_Circuit ctx2' c' w'
   -> WF_Circuit ctx1' (compose p c c') w'.
Admitted.
