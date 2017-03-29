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

(* A bit of a mess from attempting to reproduce Jen's code line by line. *)
Fixpoint compose {Γ1} {W} (c : Circuit Γ1 W)
                 : forall {Γ Γ1' W'}, 
                  is_valid Γ1' ->
                  Γ1' = Γ1 ⋓ Γ ->
                  (forall {Γ2 Γ2'}, is_valid Γ2' -> Γ2' = Γ2 ⋓ Γ -> Pat Γ2 W  -> 
                               Circuit Γ2' W') 
                -> Circuit Γ1' W'.
  refine (match c with
            output _ p1             => fun Γ Γ1' W' v pfM f => _ (* f _ _ pfM p1 *)
          | gate ctx v pfM' g p1 h  => fun Γ Γ1' W' v pfM f => _
          | lift v m p h            => fun Γ Γ1' W' v pfM f => _
          end). 
- (*output case*)
  eapply f; eauto.
  subst; apply p1.
- (* gate case*)
  clear W c Γ1;
  rename w into W1, w0 into W2, w1 into W.
  rename ctx into Γ0, o into Γ01, o0 into Γ1.
  rename pfM' into Merge_Γ01_Γ0_Γ1, pfM into Merge_Γ1_Γ_Γ1'.
  remember (Γ0 ⋓ Γ) as Γ0' eqn:Merge_Γ0_Γ_Γ0'. 
    destruct Γ0' as [|Γ0']. contradict v.
                            rewrite Merge_Γ1_Γ_Γ1', Merge_Γ01_Γ0_Γ1.
                            rewrite <- merge_assoc.
                            rewrite <- Merge_Γ0_Γ_Γ0'.
                            rewrite merge_I_r. 
                            apply not_valid.
  assert (Merge_Γ01_Γ0'_Γ1' : Γ1' = Γ01 ⋓ Γ0').
    rewrite Merge_Γ1_Γ_Γ1', Merge_Γ01_Γ0_Γ1, Merge_Γ0_Γ_Γ0', merge_assoc. reflexivity.
  refine (gate _ v Merge_Γ01_Γ0'_Γ1' g p1 (fun Γ02 Γ02' v02' Merge_Γ02_Γ0'_Γ02' q => _)).
  remember (Γ0 ⋓ Γ02) as Γ002 eqn:Merge_Γ_Γ02_Γ002. 
    destruct Γ002 as [|Γ002]. contradict v02'.
                              rewrite Merge_Γ02_Γ0'_Γ02', Merge_Γ0_Γ_Γ0'.
                              rewrite merge_assoc, (merge_comm Γ02 _).
                              rewrite <- Merge_Γ_Γ02_Γ002. simpl.
                              apply not_valid.
  remember (Γ ⋓ Γ02) as Γ02'' eqn:Merge_Γ0_Γ002_Γ02''.
    destruct Γ02'' as [|Γ02'']. contradict v02'.
                                rewrite Merge_Γ02_Γ0'_Γ02', Merge_Γ0_Γ_Γ0'.
                                rewrite (merge_comm Γ0 _), merge_assoc, 
                                (merge_comm Γ02), <- Merge_Γ0_Γ002_Γ02''; simpl.
                                apply not_valid.
  refine (compose _ _ (h Γ02 Γ002 _ _ q) _ _ _ _ _ f); subst.
  unfold is_valid; eauto.
  rewrite merge_comm; assumption.
  assumption.
  rewrite Merge_Γ_Γ02_Γ002, Merge_Γ0_Γ_Γ0'. monoid.
- clear W c Γ1.
  rename w into W, w0 into W0, o into Γ0, o0 into Γ2, o1 into Γ1. 
  refine (lift _ _ p (fun x => compose _ _ (h x) _ _ _ _ _ f)); auto.
  * rewrite merge_assoc. subst. auto.
  * subst.
    destruct (valid_split _ _ _ v) as [H1 [H2 H3]]; auto.
Qed.

(* *)