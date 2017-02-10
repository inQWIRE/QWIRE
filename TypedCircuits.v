Require Import Arith.
Require Import List.
Import ListNotations.
Open Scope list_scope.



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
Fixpoint MergeOptionF (o1 : option WType) (o2 : option WType) 
         : option (option WType) :=
  match o1, o2 with
  | None, _ => Some o2
  | _, None => Some o1
  | Some _, Some _ => None
  end.
Fixpoint MergeCtxF (Γ1 : Ctx) (Γ2 : Ctx) : option Ctx :=
  match Γ1, Γ2 with
  | [], _ => Some Γ2
  | _, [] => Some Γ1
  | (o1 :: Γ1'), (o2 :: Γ2') => 
    match MergeOptionF o1 o2, MergeCtxF Γ1' Γ2' with
    | Some o, Some Γ => Some (o :: Γ)
    | _, _           => None
    end
  end.

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
(*
Program Fixpoint compose {ctx1} {w} (c : Circuit ctx1 w)
                 : forall {ctx} {ctx1'} {w'}, 
                  (forall ctx2 ctx2', MergeCtx ctx2 ctx ctx2'
                                    -> Pat ctx2 w 
                                    -> Circuit ctx2' w') 
               -> MergeCtx ctx1 ctx ctx1' -> Circuit ctx1' w' :=
  match c with
    | output p1 => _
    | gate ctx g p1 h pfM => _
  end.
*)

Lemma mergeF : forall {Γ1 Γ2 Γ}, MergeCtxF Γ1 Γ2 = Some Γ -> MergeCtx Γ1 Γ2 Γ.
Proof.
  induction Γ1 as [ | o1 Γ1']; simpl; intros Γ2 Γ H; inversion H; subst; try constructor.
  destruct Γ2 as [ | o2 Γ2']. inversion H; subst. constructor.
  destruct o1; destruct o2; simpl in *; try (inversion H1; fail).
  - remember (MergeCtxF Γ1' Γ2'). 
    destruct o; simpl in *; try (inversion H1; fail).
    inversion H; subst. constructor. constructor. apply IHΓ1'; auto.
  - remember (MergeCtxF Γ1' Γ2'). 
    destruct o; simpl in *; try (inversion H1; fail).
    inversion H; subst. constructor. constructor. apply IHΓ1'; auto.
  - remember (MergeCtxF Γ1' Γ2'). 
    destruct o; simpl in *; try (inversion H1; fail).
    inversion H; subst. constructor. constructor. apply IHΓ1'; auto.
Qed.    
Open Scope type_scope.

Definition Disjoint Γ1 Γ2 := {Γ : Ctx & MergeCtxF Γ1 Γ2 = Some Γ}.
Definition Subset Γ1 Γ := {Γ2 : Ctx & MergeCtxF Γ1 Γ2 = Some Γ}.

Lemma mergeDisjoint : forall Γ1 Γ2 Γ3 Γ Γ',
      MergeCtx Γ1 Γ2 Γ -> MergeCtx Γ Γ3 Γ' -> Disjoint Γ1 Γ3 * Disjoint Γ2 Γ3.
Admitted.

Lemma disjointTrans : forall Γ1 Γ2 Γ Γ', MergeCtx Γ1 Γ2 Γ -> Disjoint Γ1 Γ' -> Disjoint Γ2 Γ' 
                      -> Disjoint Γ Γ'.
Admitted.

Lemma mergeAssoc : forall Γ1 Γ2 Γ3 Γ Γ' Γ0,
      MergeCtx Γ1 Γ2 Γ -> MergeCtx Γ Γ3 Γ' 
   -> MergeCtxF Γ2 Γ3 = Some Γ0
   -> (MergeCtx Γ2 Γ3 Γ0) * (MergeCtx Γ1 Γ0 Γ').
Admitted.

Lemma mergeSymm : forall {Γ1 Γ2 Γ}, MergeCtx Γ1 Γ2 Γ -> MergeCtx Γ2 Γ1 Γ.
Admitted.

Fixpoint compose {Γ1} {W} (c : Circuit Γ1 W)
                 : forall {Γ} {Γ1'} {W'}, 
                  (forall {Γ2} {Γ2'}, MergeCtx Γ2 Γ Γ2'
                                    -> Pat Γ2 W
                                    -> Circuit Γ2' W') 
               -> MergeCtx Γ1 Γ Γ1' -> Circuit Γ1' W'.
  refine (match c with
            output p1 => fun Γ Γ1' W' f pfM => f _ _ pfM p1
          | gate ctx g p1 h pfM => fun Γ Γ1' W' f pfM0 => _
          end). 
  clear W c Γ1.
  rename w into W1, w0 into W2, w1 into W.
  rename c0 into Γ01, c1 into Γ1, ctx into Γ0.
  destruct (mergeDisjoint Γ01 Γ0 Γ Γ1 Γ1') as [[Γ01' pfM1] [Γ0' pfM2]]; auto.
  destruct (mergeAssoc Γ01 Γ0 Γ Γ1 Γ1' Γ0') as [pfM3 pfM4]; auto.
  refine (gate _ g p1 (fun Γ02 Γ02' pfM' q => _) pfM4);
    destruct (mergeDisjoint Γ0 Γ Γ02 Γ0' Γ02') as [[Γ002 pfM6] [Γ02'' pfM5]];
      try (auto; apply mergeSymm; auto).
  refine (compose _ _ (h Γ02 Γ002 _ q) _ _ _ f _).
  - apply mergeSymm. apply mergeF. apply pfM6.
  - (* Γ002 = Γ0 ⋓ Γ02 *)
    (* Γ02' = Γ02 ⋓ Γ0' = Γ02 ⋓ (Γ0 ⋓ Γ) *)
    (* So want to show that (Γ0 ⋓ Γ02) ⋓ Γ = Γ02 ⋓ (Γ0 ⋓ Γ) *)
    (* First show that (Γ02 ⋓ Γ0) ⋓ Γ = Γ02 ⋓ (Γ0 ⋓ Γ) *)
    (* Before that, show that Γ002 _|_ Γ *)
    (* To do that, show that Γ0 _|_ Γ*) 
    assert (pfDisjoint1 : Disjoint Γ0 Γ).
      exists Γ0'; auto.
    assert (pfDisjoint2 : Disjoint Γ02 Γ).
      admit.
    assert (pfDisjoint3 : Disjoint Γ002 Γ).
      apply disjointTrans with (Γ1 := Γ0) (Γ2 := Γ02); auto. apply mergeF; auto.
    destruct pfDisjoint1 as [ Γ0001 pfDisjoint1].
    destruct pfDisjoint3 as [ Γ0002 pfDisjoint3]. 
    (* as a result of mergeAssoc, we want Γ002 ⋓ Γ = Γ02' *)

    edestruct (mergeAssoc Γ02 Γ0 Γ).
    * eapply mergeSymm. eapply mergeF. eauto. 
    * eapply mergeF. exact pfDisjoint3.
    * exact pfDisjoint1.
    * 
    


Admitted.

