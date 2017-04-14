Require Export Contexts.
Require Import List.
Import ListNotations.

(* Typed Circuits Scope [UC is UntypedCircuits] *)
(* Module TC. *)

(* need to change to contexts *)
Inductive Pat : OCtx -> WType -> Set :=
(* | var  : forall x w ctx, SingletonCtx x w ctx -> Pat ctx w *)
| unit : Pat ∅ One
| qubit : forall x ctx, (SingletonCtx x Qubit ctx) -> Pat ctx Qubit 
| bit : forall x ctx, (SingletonCtx x Bit ctx) -> Pat ctx Bit 
| pair : forall ctx1 ctx2 ctx w1 w2,
        is_valid ctx 
      -> ctx = ctx1 ⋓ ctx2
      -> Pat ctx1 w1
      -> Pat ctx2 w2
      -> Pat ctx (Tensor w1 w2).

Lemma pat_ctx_valid : forall Γ W, Pat Γ W -> is_valid Γ.
Proof. intros Γ W p. unfold is_valid. inversion p; eauto. Qed.

Inductive Unitary : WType -> Set := 
  | H : Unitary Qubit 
  | σx : Unitary Qubit
  | σy : Unitary Qubit
  | σz : Unitary Qubit
  | CNOT : Unitary (Qubit ⊗ Qubit)
  | control : forall {W} (U : Unitary W), Unitary (Qubit ⊗ W) 
  | bit_control : forall {W} (U : Unitary W), Unitary (Bit ⊗ W) 
  | transpose : forall {W} (U : Unitary W), Unitary W.

Inductive Gate : WType -> WType -> Set := 
  | U : forall {W} (u : Unitary W), Gate W W
  | init0 : Gate One Qubit
  | init1 : Gate One Qubit
  | new0 : Gate One Bit
  | new1 : Gate One Bit
  | meas : Gate Qubit Bit
  | discard : Gate Bit One.

Coercion U : Unitary >-> Gate.

Inductive Circuit : OCtx -> WType -> Set :=
| output : forall {ctx ctx' w}, ctx' = ctx -> Pat ctx w -> Circuit ctx' w
| gate   : forall ctx {ctx1 ctx1'} {w1 w2 w}, 
          is_valid ctx1'
        -> ctx1' = ctx1 ⋓ ctx            
        -> Gate w1 w2
        -> Pat ctx1 w1
        -> (forall {ctx2 ctx2'},
              is_valid ctx2'
            -> ctx2' = ctx2 ⋓ ctx 
            -> Pat ctx2 w2 -> Circuit ctx2' w)
        -> Circuit ctx1' w
| lift : forall {ctx1 ctx2 ctx w w'},
         is_valid ctx -> ctx = ctx1 ⋓ ctx2
      -> Pat ctx1 w
      -> (interpret w -> Circuit ctx2 w')
      -> Circuit ctx w'
.

Inductive Box : WType -> WType -> Set :=
| box : forall {w1} {w2}, 
        (forall {ctx}, Pat ctx w1 -> Circuit ctx w2) -> Box w1 w2.

Definition unbox {ctx ctx'} {w1} {w2} (b : Box w1 w2) : 
  ctx = ctx' -> Pat ctx w1 -> Circuit ctx' w2.
  refine (match b with box f => _ end). intros M; subst; auto. Defined.

(*
End TC.
Import TC.
*)


(* Prevent compute from unfolding important fixpoints *)
Opaque merge.
Opaque Ctx.
Opaque is_valid.

Ltac validate :=
  repeat ((*idtac "validate";*) match goal with
  (* Pattern contexts are valid *)
  | [p : Pat ?Γ ?W |- _ ]             => apply pat_ctx_valid in p
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


(* A bit of a mess from attempting to reproduce Jen's code line by line. *)
Fixpoint compose {Γ1} {W} (c : Circuit Γ1 W)
                 : forall {Γ Γ1' W'}, 
                  is_valid Γ1' ->
                  Γ1' = Γ1 ⋓ Γ ->
                  (forall {Γ2 Γ2'}, is_valid Γ2' -> Γ2' = Γ2 ⋓ Γ -> Pat Γ2 W  -> 
                                    Circuit Γ2' W') 
                -> Circuit Γ1' W'.
  refine (match c with
            output _ p1             => fun Γ Γ1' W' v pfM f => f _ _ _ _ p1
          | gate Γ0 v pfM' g p1 h   => fun Γ Γ1' W' v pfM f => 
            gate (Γ0 ⋓ Γ) _ _ g p1 (fun Γ02 _ _ _ q =>
                compose _ _ (h Γ02 (Γ0 ⋓ Γ02) _ _ q) _ _ _ _ _ f)
          | lift v m p h            => fun Γ Γ1' W' v pfM f => 
            lift _ _ p (fun x => compose _ _ (h x) _ _ _ _ _ f)
          end);
    subst;
    monoid; validate. 
Defined.



(* *)