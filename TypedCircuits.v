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

Definition Var := nat.
Definition Ctx := list (option WType).
(* Definition OCtx := option Ctx. *)

Inductive OCtx := 
| Invalid : OCtx 
| Valid : Ctx -> OCtx.

Inductive SingletonCtx : Var -> WType -> Ctx -> Set :=
| SingletonHere : forall w, SingletonCtx 0 w (Some w :: [])
| SingletonLater : forall x w ctx, SingletonCtx x w ctx -> SingletonCtx (S x) w (None::ctx)
.

Definition merge_wire (o1 o2 : option WType) : OCtx :=
  match o1, o2 with
  | None, o2 => Valid [o2]
  | Some w1, None => Valid [Some w1]
  | _, _ => Invalid
  end.

Fixpoint merge' (Γ1 Γ2 : Ctx) : OCtx :=
  match Γ1, Γ2 with
  | [], _ => Valid Γ2
  | _, [] => Valid Γ1
  | o1 :: Γ1', o2 :: Γ2' => match merge_wire o1 o2 with
                           | Invalid => Invalid
                           | Valid Γ0 => match merge' Γ1' Γ2' with
                                        | Invalid => Invalid
                                        | Valid Γ' => Valid (Γ0 ++ Γ')
                                        end
                           end
  end.                            

Definition merge (Γ1 Γ2 : OCtx) : OCtx :=
  match Γ1, Γ2 with
  | Valid Γ1', Valid Γ2' => merge' Γ1' Γ2'
  | _, _ => Invalid
  end. 

Notation "∅" := (Valid []).
Infix "⋓" := merge (left associativity, at level 40).
Coercion Valid : Ctx >-> OCtx.

(* Typed Circuits Scope [UC is UntypedCircuits] *)
Module TC.

Inductive Pat : OCtx -> WType -> Set :=
(* | var  : forall x w ctx, SingletonCtx x w ctx -> Pat ctx w *)
| unit : Pat ∅ One
| qubit : forall x ctx, (SingletonCtx x Qubit ctx) -> Pat ctx Qubit 
| bit : forall x ctx, (SingletonCtx x Bit ctx) -> Pat ctx Bit 
| pair : forall ctx1 ctx2 ctx w1 w2,
        ctx = ctx1 ⋓ ctx2
      -> Pat ctx1 w1
      -> Pat ctx2 w2
      -> Pat ctx (Tensor w1 w2).

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
| gate   : forall ctx {ctx1 ctx1' w1 w2 w}, 
          ctx1' = ctx1 ⋓ ctx            
        -> Gate w1 w2
        -> Pat ctx1 w1
        -> (forall {ctx2 ctx2'}, ctx2' = ctx2 ⋓ ctx 
            -> Pat ctx2 w2 -> Circuit ctx2' w)
        -> Circuit ctx1' w.

Inductive Box : WType -> WType -> Set :=
| box : forall {w1} {w2}, 
        (forall {ctx}, Pat ctx w1 -> Circuit ctx w2) -> Box w1 w2.

Definition unbox {ctx ctx'} {w1} {w2} (b : Box w1 w2) : 
  ctx = ctx' -> Pat ctx w1 -> Circuit ctx' w2.
  refine (match b with box f => _ end). intros M; subst; auto. Qed.

End TC.
Import TC.

Open Scope type_scope.

(* Facts about ⋓ *)

Lemma merge_merge' : forall (Γ1 Γ2 : Ctx), Γ1 ⋓ Γ2 = (merge' Γ1 Γ2).
Proof. reflexivity. Qed.

(* Note that the reverse is not always true - we would need to 
   check validity and not-emptyness of the contexts *)
Lemma merge_cancel_l : forall Γ Γ1 Γ2 , Γ1 = Γ2 -> Γ ⋓ Γ1 = Γ ⋓ Γ2.
Proof. intros; subst; reflexivity. Qed.

Lemma merge_cancel_r : forall Γ Γ1 Γ2 , Γ1 = Γ2 -> Γ1 ⋓ Γ = Γ2 ⋓ Γ.
Proof. intros; subst; reflexivity. Qed.

Lemma merge_I_l : forall Γ, Invalid ⋓ Γ = Invalid. Proof. reflexivity. Qed.

Lemma merge_I_r : forall Γ, Γ ⋓ Invalid = Invalid. Proof. destruct Γ; reflexivity. Qed.

Lemma merge_invalid_iff : forall (o1 o2 : option WType) (Γ1 Γ2 : Ctx), 
  Valid (o1 :: Γ1) ⋓ Valid (o2 :: Γ2) = Invalid <-> 
  merge_wire o1 o2 = Invalid \/ Γ1 ⋓ Γ2 = Invalid.
Proof.
  intros o1 o2 Γ1 Γ2.
  split.  
  + intros H.
    destruct o1, o2; auto; right; simpl in H.    
    - rewrite <- merge_merge' in H.
      destruct (Γ1 ⋓ Γ2); trivial.
      inversion H.
    - rewrite <- merge_merge' in H.
      destruct (Γ1 ⋓ Γ2); trivial.
      inversion H.
    - rewrite <- merge_merge' in H.
      destruct (Γ1 ⋓ Γ2); trivial.
      inversion H.
  + intros H.
    inversion H.
    simpl. rewrite H0; reflexivity.
    simpl.
    destruct (merge_wire o1 o2); trivial.
    rewrite merge_merge' in H0.
    rewrite H0.
    reflexivity.
Qed.

Lemma merge_nil_l : forall Γ, ∅ ⋓ Γ = Γ. Proof. destruct Γ; reflexivity. Qed.

Lemma merge_nil_r : forall Γ, Γ ⋓ ∅ = Γ. 
Proof. destruct Γ; trivial. destruct c; trivial. Qed. 

Lemma merge_comm : forall Γ1 Γ2, Γ1 ⋓ Γ2 = Γ2 ⋓ Γ1. 
Proof.
  intros Γ1 Γ2.
  destruct Γ1 as [|Γ1], Γ2 as [|Γ2]; trivial.
  generalize dependent Γ2.
  induction Γ1. 
  + destruct Γ2; trivial.
  + destruct Γ2; trivial.
    simpl.
    unfold merge in IHΓ1. 
    rewrite IHΓ1.
    destruct a, o; reflexivity.
Qed.    

Lemma merge_assoc : forall Γ1 Γ2 Γ3, Γ1 ⋓ Γ2 ⋓ Γ3 = Γ1 ⋓ (Γ2 ⋓ Γ3). 
Proof.
  intros Γ1 Γ2 Γ3.
  destruct Γ1 as [|Γ1], Γ2 as [|Γ2], Γ3 as [|Γ3]; try rewrite merge_I_r; trivial. 
  generalize dependent Γ3. generalize dependent Γ1.
  induction Γ2 as [| o2 Γ2']. 
  + intros. rewrite merge_nil_l, merge_nil_r; reflexivity.
  + intros Γ1 Γ3.
    destruct Γ1 as [|o1 Γ1'], Γ3 as [| o3 Γ3'] ; trivial.
    - rewrite 2 merge_nil_l.
      reflexivity.
    - rewrite 2 merge_nil_r.
      reflexivity.
    - destruct o1, o2, o3; trivial.
      * simpl. destruct (merge' Γ2' Γ3'); reflexivity.
      * simpl. destruct (merge' Γ1' Γ2'), (merge' Γ2' Γ3'); reflexivity.
      * simpl. destruct (merge' Γ1' Γ2') eqn:M12, (merge' Γ2' Γ3') eqn:M23.
        reflexivity.
        rewrite <- merge_merge' in *.
        rewrite <- M23.
        rewrite <- IHΓ2'.
        rewrite M12. 
        reflexivity.
        rewrite <- merge_merge' in *.
        apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite IHΓ2'.
        rewrite M23.
        reflexivity.
        destruct (merge' Γ1' c0) eqn:M123.
        rewrite <- merge_merge' in *.
        apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite IHΓ2'.
        rewrite M23.
        assumption.
        simpl.
        rewrite <- merge_merge' in *.
        rewrite <- M12.
        rewrite IHΓ2'.
        rewrite M23, M123.
        reflexivity.
      * simpl. destruct (merge' Γ1' Γ2'), (merge' Γ2' Γ3'); reflexivity.
      * simpl. destruct (merge' Γ1' Γ2') eqn:M12, (merge' Γ2' Γ3') eqn:M23.
        reflexivity.
        rewrite <- merge_merge' in *.
        rewrite <- M23.
        rewrite <- IHΓ2'.
        rewrite M12. 
        reflexivity.
        rewrite <- merge_merge' in *.
        apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite IHΓ2'.
        rewrite M23.
        reflexivity.
        destruct (merge' Γ1' c0) eqn:M123.
        rewrite <- merge_merge' in *.
        apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite IHΓ2'.
        rewrite M23.
        assumption.
        simpl.
        rewrite <- merge_merge' in *.
        rewrite <- M12.
        rewrite IHΓ2'.
        rewrite M23, M123.
        reflexivity.
      * simpl. destruct (merge' Γ1' Γ2') eqn:M12, (merge' Γ2' Γ3') eqn:M23.
        reflexivity.
        rewrite <- merge_merge' in *.
        rewrite <- M23.
        rewrite <- IHΓ2'.
        rewrite M12. 
        reflexivity.
        rewrite <- merge_merge' in *.
        apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite IHΓ2'.
        rewrite M23.
        reflexivity.
        destruct (merge' Γ1' c0) eqn:M123.
        rewrite <- merge_merge' in *.
        apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite IHΓ2'.
        rewrite M23.
        assumption.
        simpl.
        rewrite <- merge_merge' in *.
        rewrite <- M12.
        rewrite IHΓ2'.
        rewrite M23, M123.
        reflexivity.
      * simpl. destruct (merge' Γ1' Γ2') eqn:M12, (merge' Γ2' Γ3') eqn:M23.
        reflexivity.
        rewrite <- merge_merge' in *.
        rewrite <- M23.
        rewrite <- IHΓ2'.
        rewrite M12. 
        reflexivity.
        rewrite <- merge_merge' in *.
        apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite IHΓ2'.
        rewrite M23.
        reflexivity.
        destruct (merge' Γ1' c0) eqn:M123.
        rewrite <- merge_merge' in *.
        apply merge_invalid_iff. right.
        rewrite <- M12.
        rewrite IHΓ2'.
        rewrite M23.
        assumption.
        simpl.
        rewrite <- merge_merge' in *.
        rewrite <- M12.
        rewrite IHΓ2'.
        rewrite M23, M123.
        reflexivity.
Qed.


(* A bit of a mess from attempting to reproduce Jen's code line by line. *)
Fixpoint compose {Γ1} {W} (c : Circuit Γ1 W)
                 : forall {Γ} {Γ1'} {W'}, 
                  Γ1' = Γ1 ⋓ Γ ->
                  (forall {Γ2} {Γ2'}, Γ2' = Γ2 ⋓ Γ -> Pat Γ2 W  -> Circuit Γ2' W') 
                -> Circuit Γ1' W'.
  refine (match c with
            output _ p1 => fun Γ Γ1' W' pfM f => _ (* f _ _ pfM p1 *)
          | gate ctx pfM' g p1 h  => fun Γ Γ1' W' pfM f => _
          end). 
  (*output case*)
  eapply f.
  apply pfM.
  subst.
  apply p1.
  (* gate case*)
  clear W c Γ1;
  rename w into W1, w0 into W2, w1 into W;
  rename o into Γ01, o0 into Γ1, ctx into Γ0.
  rename pfM' into Merge_Γ01_Γ0_Γ1, pfM into Merge_Γ1_Γ_Γ1'.
  remember (Γ0 ⋓ Γ) as Γ0' eqn:Merge_Γ0_Γ_Γ0'. 
  assert (Merge_Γ01_Γ0'_Γ1' : Γ1' = Γ01 ⋓ Γ0').
    rewrite Merge_Γ1_Γ_Γ1', Merge_Γ01_Γ0_Γ1, Merge_Γ0_Γ_Γ0'. apply merge_assoc.
  refine (gate _ Merge_Γ01_Γ0'_Γ1' g p1 (fun Γ02 Γ02' Merge_Γ02_Γ0'_Γ02' q => _)).
  remember (Γ0 ⋓ Γ02) as Γ002 eqn:Merge_Γ_Γ02_Γ002. 
  remember (Γ ⋓ Γ02) as Γ02'' eqn:Merge_Γ0_Γ002_Γ02''.
  refine (compose _ _ (h Γ02 Γ002 _ q) _ _ _ _ f); subst.
  apply merge_comm.
  rewrite (merge_comm Γ0 Γ02), merge_assoc; reflexivity.
Qed.

(* *)