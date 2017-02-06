Require Import Arith.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Contexts.

Inductive WType := Qubit | Bit | One | Tensor : WType -> WType -> WType.

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

Inductive EmptyCtx : Ctx -> Set :=
| EmptyNil : EmptyCtx []
| EmptyCons : forall ctx, EmptyCtx ctx -> EmptyCtx (None :: ctx)
.

Inductive SingletonCtx : Var -> WType -> Ctx -> Set :=
| SingletonHere : forall w ctx, EmptyCtx ctx -> SingletonCtx 0 w (Some w :: ctx)
| SingletonLater : forall x w ctx, SingletonCtx x w ctx -> SingletonCtx (S x) w (None :: ctx)
.

Inductive AddCtx : Var -> WType -> Ctx -> Ctx -> Set :=
| AddHere : forall w ctx, AddCtx 0 w (None :: ctx) (Some w :: ctx)
| AddLater : forall x w ctx ctx' m, AddCtx x w ctx ctx' -> AddCtx (S x) w (m :: ctx) (m :: ctx')
.

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

Inductive Pat : Ctx -> WType -> Set :=
| var  : forall x w ctx, SingletonCtx x w ctx -> Pat ctx w
| unit : forall ctx, EmptyCtx ctx -> Pat ctx One
| pair : forall ctx1 ctx2 ctx w1 w2,
         MergeCtx ctx1 ctx2 ctx
      -> Pat ctx1 w1
      -> Pat ctx2 w2
      -> Pat ctx (Tensor w1 w2)
.

Parameter (Gate : WType -> WType -> Set).

Inductive Circuit : Ctx -> WType -> Set :=
| output : forall {ctx w}, Pat ctx w -> Circuit ctx w
| gate   : forall ctx {ctx1 ctx1' w1 w2 w},
           Gate w1 w2
        -> Pat ctx1 w1
        -> (forall {ctx2 ctx2'}, MergeCtx ctx2 ctx ctx2' 
            -> Pat ctx2 w2 -> Circuit ctx2' w)
        -> MergeCtx ctx1 ctx ctx1'
        -> Circuit ctx1' w
.

Inductive Box : WType -> WType -> Set :=
| box : forall {w1} {w2}, 
        (forall {ctx}, Pat ctx w1 -> Circuit ctx w2) -> Box w1 w2.

Definition unbox {ctx} {w1} {w2} (b : Box w1 w2) : Pat ctx w1 -> Circuit ctx w2 :=
  match b with
    box f => f ctx
  end.

Fixpoint compose {ctx1} {w} (c : Circuit ctx1 w)
                 : forall {ctx} {ctx1'} {w'}, 
                  (forall ctx2 ctx2', MergeCtx ctx2 ctx ctx2'
                                    -> Pat ctx2 w 
                                    -> Circuit ctx2' w') 
               -> MergeCtx ctx1 ctx ctx1' -> Circuit ctx1' w'.
  refine (match c with
            output p1 => fun _ _ _ f pfM => f _ _ pfM p1
          | gate ctx g p1 h pfM => _
          end). 
  clear w c ctx1; 
  rename c0 into ctx1, c1 into ctx1', w0 into w1, w1 into w2, w2 into w.
  intros ctx0 ctx01 w' f pfM'.
  refine (gate _ g p1 (fun ctx2 ctx2' pfM'' p2 => compose _ _ (h _ _ _ p2) _ _ _ _ _) _).
    - admit.
    - intros ctx3 ctx3' pfM3 p3. eapply (f _ _ _ p3).
    - admit.
    - admit.
Admitted.

