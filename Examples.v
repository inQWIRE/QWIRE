Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import TypedCircuits.
Import TC.
Import ListNotations.
Open Scope list_scope.
        
(* Merging Contexts *)
Program Definition mmerge_atom (o1 o2 : option WType) {dis : [o1] ∥ [o2]} :=
  match o1, o2 with
  | None, None   => None
  | None, Some W => Some W 
  | Some W, None => Some W
  | Some W1, Some W2 => _
  end.
Next Obligation. inversion dis. inversion H0; subst. inversion H6. Defined.

Program Fixpoint mmerge (Γ1 Γ2 : Ctx) (dis : Γ1 ∥ Γ2) := 
  match Γ1, Γ2 with 
  | [], _ => Γ2
  | _, [] => Γ1
  | (o1 :: Γ1'), (o2 :: Γ2') => @mmerge_atom o1 o2 _ :: mmerge Γ1' Γ2' _
  end.
Next Obligation. destruct dis. inversion m; subst.
                 exists [o]. constructor; trivial. constructor. Defined.
Next Obligation. destruct dis. inversion m; subst.
                 exists g; assumption. Defined.

Notation "Γ1 ⋓ Γ2" := (mmerge Γ1 Γ2 _) (at level 30).

Lemma merge_atom_irrelevant : forall o1 o2 D1 D2, 
                                @mmerge_atom o1 o2 D1 = @mmerge_atom o1 o2 D2.
Proof.
  intros.
  inversion D1. inversion H0; subst. inversion H6; subst; reflexivity.
Qed.  

Lemma merge_irrelevant : forall Γ1 Γ2 D1 D2, mmerge Γ1 Γ2 D1 = mmerge Γ1 Γ2 D2.
Proof.
  induction Γ1. reflexivity.
  intros.
  destruct Γ2.
  simpl. reflexivity.
  simpl. 
  erewrite merge_atom_irrelevant.
  erewrite IHΓ1.
  reflexivity.
Qed.  

Lemma mmerge_atom_refl : forall o1 o2 (dis: [o1] ∥ [o2]), 
                        MergeOption o1 o2 (@mmerge_atom o1 o2 dis).
Proof.
  intros.
  destruct o1, o2; (try constructor).
  destruct dis.
  inversion m; subst.
  inversion H5.
Qed.

Lemma mmerge_refl : forall Γ1 Γ2 (dis: Γ1 ∥ Γ2), MergeCtx Γ1 Γ2 (@mmerge Γ1 Γ2 dis).
Proof.
  induction Γ1.
  intros. simpl. constructor.
  intros.
  destruct Γ2.
  simpl. constructor.
  simpl.
  constructor.
  apply mmerge_atom_refl.
  apply IHΓ1.
Qed.

Lemma mmerge_symm : forall Γ1 Γ2 (D: Γ1 ∥ Γ2), 
                      mmerge Γ1 Γ2 D = mmerge Γ2 Γ1 (disjoint_symm _ _ D). 
Proof.
  induction Γ1.
  intros. simpl. 
  destruct Γ2; reflexivity.
  intros.
  destruct Γ2.
  reflexivity.
  simpl.
  rewrite IHΓ1.
  destruct D.
  inversion m; subst.
  inversion H5; subst; simpl; erewrite merge_irrelevant; reflexivity.
Qed.  

(*
Lemma mmerge_assoc_r : forall Γ1 Γ2 Γ3 Γ4 D, MergeCtx (mmerge Γ1 Γ2 D) Γ3 Γ4 ->
                                        {D' : _ & MergeCtx Γ1 (mmerge Γ2 Γ3 D') Γ4}.
Proof.
  intros.
 *) 
  

Lemma mmerge_merge3 : forall Γ1 Γ2 Γ3 Γ4 D, MergeCtx (mmerge Γ1 Γ2 D) Γ3 Γ4 -> 
                                       merge3 Γ1 Γ2 Γ3 Γ4.
Proof.
  intros.
  unfold merge3.
  exists (mmerge Γ1 Γ2 D).
  split.
  apply mmerge_refl.
  assumption.
Qed.  

Lemma merge3_mmerge : forall Γ1 Γ2 Γ3 Γ4, merge3 Γ1 Γ2 Γ3 Γ4 -> 
                                     {D : _ & MergeCtx (mmerge Γ1 Γ2 D) Γ3 Γ4}.
Proof.
  intros.
  destruct H0 as [Γ [H1 H2]].
  assert (Γ1 ∥ Γ2) as D1. exists Γ. assumption.
  exists D1.
  specialize (mmerge_refl _ _ D1). intros.
  apply (merge_functional H1) in H0.
  subst.
  assumption.  
Qed.  


(*
Lemma mmerge_assoc : forall Γ1 Γ2 Γ3 Γ4 dis dis', MergeCtx (mmerge Γ1 Γ2 dis) Γ3 Γ4 ->
                                             MergeCtx Γ1 (mmerge Γ2 Γ3 dis') Γ4.
Proof.
*)  

(* Projecting out elements of tensors *)
Inductive sigT23 (A:Type) (P Q R : A -> A -> Type) : Type :=
    existT23 : forall (x y : A), P x y -> Q x y -> R x y -> sigT23 A P Q R.

(*
Notation "{ x, y : A & P & Q & R }" := (sigT23 A (fun x y => P) (fun x y => Q) (fun x y => R)).
*)

Arguments existT23 {A} {P Q R} x y p1 p2 M.

Program Definition wproj {Γ W1 W2} (p : Pat Γ (Tensor W1 W2)) : 
  sigT23 Ctx (fun x y => Pat x W1) (fun x y => Pat y W2) (fun x y => MergeCtx x y Γ) :=
(*  {Γ1 Γ2 : Ctx & Pat Γ1 W1 & Pat Γ2 W2 & MergeCtx Γ1 Γ2 Γ} *)
  match p with 
  | unit => _
  | qubit _ _ _ => _
  | bit _ _ _ => _
  | pair Γ1 Γ2 Γ W1 W2 M p1 p2 => 
    existT23 Γ1 Γ2 p1 p2 M  
  end.

Check wproj.

(*
Notation "⟨ w1 , w2 ⟩" := (pair _ _ _ _ _ _ w1 w2) (at level 11, left associativity) : circ_scope. *)
(*
Notation "w1 & w2" := (pair _ _ _ _ _ _ w1 w2) (at level 11, left associativity) : circ_scope. *)
Notation "w1 * w2" := (pair _ _ _ _ _ _ w1 w2) (at level 40, left associativity) : circ_scope.
Notation "(())" := unit : circ_scope.

Parameter Δ1 Δ2 Δ3 Δ4 Δ5 Δ6 Δ7: Ctx.

(* Getting contexts for input patterns *)

Open Scope circ_scope.

(*** Tactics ***)

(* Prevent compute from unfolding important fixpoints *)
Opaque wproj.
Opaque Ctx.

(*
Ltac type_check_circ_prev := 
  intros;
  compute in *;
  repeat match goal with 
  | [ |- Ctx ]                      => simpl (* do not try random ctx or permute goal *)
  | [ |- ?Γ = ?Γ ]                  => reflexivity
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ3 |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => exact H
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ3 |- MergeCtx ?Γ2 ?Γ1 ?Γ3 ] => apply (merge_symm H)
  | [ H : MergeCtx [] ?Γ1 ?Γ2 |- _] => apply merge_nil_l in H; subst 
  | [ H : MergeCtx ?Γ1 [] ?Γ2 |- _] => apply merge_nil_r in H; subst
  | [ p : Pat ?Γ One |- _ ]         => inversion p; subst; clear p
  | [ |- Pat [] One ]               => apply unit
  | [ |- SingletonCtx _ ?W (?C :: [])]  => apply SingletonHere
  | [ |- SingletonCtx _ ?W (None :: _)] => apply SingletonLater
  | [ |- MergeCtx [] _ _]           => apply MergeNilL
  | [ |- MergeCtx _ [] _]           => apply MergeNilR
  | [ |- MergeCtx _ _ []]           => apply MergeNilL (* Both work *)
  end.
*)

Ltac type_check_once := 
  intros;
  compute in *;
  repeat match goal with 
  | [ |- ?Γ = ?Γ ]                  => reflexivity
  | [ p : Pat _ One |- _ ]          => inversion p; subst; clear p
  | [ |- Pat _ One ]                => apply unit
  | [ p: Pat ?Γ ?W |- Pat ?Γ ?W ]   => exact p (* danger? *)
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ3 |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => exact H
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ3 |- MergeCtx ?Γ2 ?Γ1 ?Γ3 ] => apply (merge_symm H)
  | [ H : MergeCtx [] ?Γ1 ?Γ2 |- _] => apply merge_nil_l in H; subst 
  | [ H : MergeCtx ?Γ1 [] ?Γ2 |- _] => apply merge_nil_r in H; subst
  | [ |- MergeCtx _ ?Γ ?Γ ]         => apply MergeNilL 
  | [ |- MergeCtx ?Γ _ ?Γ ]         => apply MergeNilR 
  | [ |- MergeCtx [] _ _]           => apply MergeNilL
  | [ |- MergeCtx _ [] _]           => apply MergeNilR
  | [ |- MergeCtx _ _ []]           => apply MergeNilL (* Both work *)
(* the following may fail *)
  | [ H : MergeCtx _ ?Γ2 ?Γ3 |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => apply H 
  | [ H : MergeCtx ?Γ1 _ ?Γ3 |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => apply H
  | [ H : MergeCtx ?Γ1 ?Γ2 _ |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => apply H 
  | [ H : MergeCtx _ ?Γ2 ?Γ3 |- MergeCtx ?Γ2 _ ?Γ3 ] => apply (merge_symm H)
  | [ H : MergeCtx ?Γ1 _ ?Γ3 |- MergeCtx _ ?Γ1 ?Γ3 ] => apply (merge_symm H)
  | [ H : MergeCtx ?Γ1 ?Γ2 _ |- MergeCtx ?Γ2 ?Γ1 _ ] => apply (merge_symm H)
(* /may fail *)
(* For transitive merges *)
(* /transitive *)
  end.


(*  | [ H : MergeCtx _ ?Γ2 ?Γ3 |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => has_evar Γ1; exact H
  | [ H : MergeCtx ?Γ1 _ ?Γ3 |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => has_evar Γ2; exact H
  | [ H : MergeCtx ?Γ1 ?Γ2 _ |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => has_evar Γ3; exact H 
  | [ H : MergeCtx _ ?Γ2 ?Γ3 |- MergeCtx ?Γ2 ?Γ1 ?Γ3 ] => has_evar Γ1; 
                                                        apply (merge_symm H)
  | [ H : MergeCtx ?Γ1 _ ?Γ3 |- MergeCtx ?Γ2 ?Γ1 ?Γ3 ] => has_evar Γ2; 
                                                        apply (merge_symm H)
  | [ H : MergeCtx ?Γ1 ?Γ2 _ |- MergeCtx ?Γ2 ?Γ1 ?Γ3 ] => has_evar Γ3; 
                                                        apply (merge_symm H) *)

(* Useful for debugging *)
Ltac type_check_num := 
  let pre := numgoals in idtac "Goals before: " pre "";
  [> type_check_once..];
  let post := numgoals in idtac "Goals after: " post "";
  tryif (guard post < pre) then type_check_num else idtac.

Ltac type_check := let n := numgoals in do n [> type_check_once..].  

(*** Paper Examples ***)

Definition id_circ {W} :  Box W W. 
  refine (box (fun Γ p1 => output _ p1)); type_check.
Defined.

Definition hadamard_measure : Box Qubit Bit.
  refine (box (fun Γ p1 => 
   gate _ _ H p1 
  (fun Γ2 Γ2' M2 p2 => gate _ _ meas p2
  (fun Γ3 Γ3' M3 p3 => output _ p3)))); type_check.
Defined.

Definition inSeq {W1 W2 W3} (c1 : Box W1 W2) (c2 : Box W2 W3) : Box W1 W3. 
  refine (box (fun Γ1 p1 => compose (unbox c1 _ p1) _  
                                (fun Γ2 Γ2' M2 p2 => unbox c2 _ p2))); type_check.
Defined.

Definition inPar {W1 W2 W1' W2'} (c1 : Box W1 W1') (c2 : Box W2 W2') : 
  Box (W1⊗W2) (W1'⊗W2').
  refine (
  box (fun Γ12 p12 => 
   let 'existT23 Γ1 Γ2 p1 p2 M := wproj p12 in 
   compose (unbox c1 _ p1) _
           (fun Γ3 Γ3' M3 p1' => compose (unbox c2 _ p2) _
                                      (fun Γ4 Γ4' M4 p2' => (output _ (p1' * p2') ))))); 
   type_check.
Defined.
   
Definition init (b : bool) : Box One Qubit.
  refine (
  if b then (box (fun Γ p1 => gate _ _ init1 p1 (fun Γ2 Γ2' M2 p2 => output _ p2)))
       else (box (fun Γ p1 => gate _ _ init0 p1 (fun Γ2 Γ2' M2 p2 => output _ p2))));
  type_check. 
Defined.

Definition bell00 : Box One (Qubit ⊗ Qubit).
  refine (
  box (fun Γ p1 => 
  (gate _ _ init0 p1
  (fun Γ2 Γ2' M2 p2 => gate _ _ init0 (())
  (fun Γ3 Γ3' M3 p3 => gate _ _ (* Γ2'? *) H p2
  (fun Γ4 Γ4' M4 p4 => gate _ _ CNOT (p3 * p4) 
  (fun Γ5 Γ5' M5 p5 => output _ p5))))))); type_check.
Defined.

Definition alice : Box (Qubit⊗Qubit) (Bit⊗Bit).
refine (
  box (fun Γ qa => 
  (gate _ _ CNOT qa
  (fun Γ2 Γ2' M2 p2 => let 'existT23 Γq Γa q a M := wproj p2 in gate Γa _ H q
  (fun Γ3 Γ3' M3 p3 => gate _ _ meas p3
  (fun Γ4 Γ4' M4 p4 => gate _ _ meas a 
  (fun Γ5 Γ5' M5 p5 => output _ (p4 * p5)))))))); type_check. Defined.

(*
Lemma wrong : forall Γ1 Γ2, {Γ3 : Ctx & MergeCtx Γ1 Γ2 Γ3}.
Proof.
  intros.
  esplit. 
  apply merge_refl.
  Stupid shelf!
*)

Lemma merge_disjoint13 : forall Γ1 Γ2 Γ3 Γ Γ',
      MergeCtx Γ1 Γ2 Γ -> MergeCtx Γ Γ3 Γ' -> {Γ'' : Ctx & MergeCtx Γ1 Γ3 Γ''}.
Proof. apply merge_disjoint. Qed.

Lemma merge_disjoint23 : forall Γ1 Γ2 Γ3 Γ Γ',
      MergeCtx Γ1 Γ2 Γ -> MergeCtx Γ Γ3 Γ' -> {Γ'' : Ctx & MergeCtx Γ2 Γ3 Γ''}.
Proof. apply merge_disjoint. Qed.

Ltac check_this := 
match goal with
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ' , H': MergeCtx ?Γ' ?Γ3 ?Γ4 |- 
      MergeCtx ?Γ3 ?Γ2 ?Γ'' ] => has_evar Γ''; 
                                let Γ := fresh "Γ" in 
                                let M := fresh "M" in 
                                specialize (merge_disjoint _ _ _ _ _  H H');
                                intros [_ [Γ M]]; apply (merge_symm M)
end.


Ltac check_this' := 
match goal with
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ' , H': MergeCtx ?Γ' ?Γ3 ?Γ4 |- 
      MergeCtx ?Γ3 ?Γ2 ?Γ'' ] => has_evar Γ''; 
                         let d := fresh "d" in 
                         let Γ := fresh "Γ" in 
                         let M := fresh "M" in 
                         exact
                          ((fun H0 : Γ1 ∥ Γ3 * Γ2 ∥ Γ3 =>
                             (fun H1 : Γ2 ∥ Γ3 * Γ2 ∥ Γ3 =>
                                let (_, d) := H1 in let (Γ, M) := d in (merge_symm M)) H0)
                            (merge_disjoint _ _ _ _ _ H H'))              
end.

(*
((fun H0 : Γx ∥ Γb * Γy ∥ Γb =>
      (fun H1 : Γx ∥ Γb * Γy ∥ Γb =>
       let (_, d) := H1 in let (Γyb, _) := d in Γyb) H0)
       (merge_disjoint Γx Γy Γb Γxy Γxyb Mxy Mxyb))
*)

Definition bob' : Box (Bit⊗(Bit⊗Qubit)) Qubit. 
refine(
  box (fun Γxyb xyb =>
    let 'existT23 Γx Γyb x yb Mxyb := wproj xyb in
    gate _ _ (bit_control σx) yb
     (fun Γyb Γyb' Myb yb' =>
     let 'existT23 Γy' Γb' y' b' Myb := wproj yb' in
      gate _ _ (bit_control σz) (x * b') (* <? *)
       (fun Γxb Γxb' Mxb xb =>
        gate _ _ discard y' 
         (fun Γz1 Γz1 Mz1 z1 =>
          let 'existT23 Γx' Γb'' x' b'' Mxb := wproj xb in
          gate _ _ discard x'
           (fun Γz2 Γz2' Mz2 z2 => output _ b'')))))); type_check. 

Unshelve.

(*
(* doesn't work *)
(*
Focus 2.
exact ((fun H0 : Γy' ∥ Γx * Γb' ∥ Γx =>
      (fun H1 : Γy' ∥ Γx * Γb' ∥ Γx =>
       let (_, d) := H1 in let 'existT _ Γxb Mxb := d in (merge_symm Mxb)) H0)
       (merge_disjoint _ _ _ _ _ Myb Myb0)).
*)

(* works *)
Focus 2.
exact (let p := merge_disjoint Γy' Γb' Γx Γyb Γyb' Myb Myb0 in
           let
             (_, d0) as p0
              return
                (MergeCtx (let (_, d) := p0 in let (Γxb, _) := d in Γxb) Γy'
                   Γyb') := p in
           let
             (x0, m) as s
              return (MergeCtx (let (Γxb, _) := s in Γxb) Γy' Γyb') := d0 in
           merge_symm
             (merge_assoc Γb' Γy' Γx Γyb Γyb' x0 (merge_symm Myb) Myb0 m)).

(* works *)
(*
Focus 3.
exact ((fun H0 : Γy' ∥ Γx * Γb' ∥ Γx =>
      (fun H1 : Γy' ∥ Γx * Γb' ∥ Γx =>
       let (_, d) := H1 in let 'existT _ Γxb Mxb := d in Γxb) H0)
       (merge_disjoint _ _ _ _ _ Myb Myb0)).
*)
*)

Focus 3.
specialize (merge_disjoint _ _ _ _ _ Myb Myb0); intros [_ [Γxb _]]; exact Γxb.

simpl; repeat match goal with |- context[let (_,_) := ?x in _] => destruct x end.
rename x0 into Γxb.
apply merge_symm.
eapply merge_assoc.
3: apply m.
apply (merge_symm Myb).
assumption.

simpl; repeat match goal with |- context[let (_,_) := ?x in _] => destruct x end.
apply merge_symm; assumption.
Defined.

Print bob'.

Definition bob : Box (Bit⊗Bit⊗Qubit) Qubit. 
refine(
  box (fun Γxyb xyb =>
    let 'existT23 Γxy Γb xy b Mxyb := wproj xyb in
    let 'existT23 Γx Γy x y Mxy := wproj xy in
    gate _ _ (bit_control σx) (y * b) 
     (fun Γyb Γyb' Myb yb =>
     let 'existT23 Γy' Γb' y' b' Myb := wproj yb in
      gate _ _ (bit_control σz) (x * b') (* <? *)
       (fun Γxb Γxb' Mxb xb =>
        gate _ _ discard y' 
         (fun Γz1 Γz1 Mz1 z1 =>
          let 'existT23 Γx' Γb'' x' b'' Mxb := wproj xb in
          gate _ _ discard x'
           (fun Γz2 Γz2' Mz2 z2 => output _ b'')))))); type_check.

Unshelve.

Focus 6.
specialize (merge_disjoint _ _ _ _ _ Mxy Mxyb); intros [_ [Γyb Myb]].
exact Γyb.

Focus 2.
simpl; repeat match goal with |- context[let (_,_) := ?x in _] => destruct x end.
assumption.

simpl; repeat match goal with |- context[let (_,_) := ?x in _] => destruct x end.
rename x0 into Γyb.
apply merge_symm in Mxy.
specialize (merge3_assoc Γy Γx Γb Γxyb (existT _ Γxy (Datatypes.pair Mxy Mxyb))); intros.
destruct H0.
destruct p.
apply (merge_functional m0) in m; subst.
apply m1.

Focus 3.
specialize (merge_disjoint _ _ _ _ _ Myb Myb0); intros [_ [Γxb Mxb]].
exact Γxb.

simpl; repeat match goal with [ |- context[let (_,_) := ?x in _]] => destruct x 
                            | [ |- context[let _ := ?x in _]] => destruct x end.
clear - Myb Myb0 m.
apply merge_symm in Myb.
specialize (merge3_assoc Γb' Γy' Γx Γyb' (existT _ Γyb (Datatypes.pair Myb Myb0))); intros.
destruct H0 as [Γbx [Mbx Mbxy]].
apply (merge_functional m) in Mbx; subst.
assumption.

simpl; repeat match goal with |- context[let (_,_) := ?x in _] => destruct x end.
apply (merge_symm m).
Defined.

Definition teleport : Box Qubit Qubit.
  refine(
  box (fun Γq q =>
    compose (unbox bell00 _ unit) _
      (fun Γab Γab' Mab ab => 
       let 'existT23 Γa Γb a b Mab' := wproj ab in 
       compose (unbox alice _ (q * a)) _
               (fun Γxy Γxy' Mxy xy => unbox bob _ (xy * b)))
      )); type_check.

Unshelve.

Focus 3.
specialize (merge_disjoint _ _ _ _ _ Mab' Mab); intros [[Γaq Maq] [Γyb Myb]].
exact Γaq.

simpl; repeat match goal with |- context[let (_,_) := ?x in _] => destruct x end.
destruct (merge_disjoint _ _ _ _ _ _).
simpl; repeat match goal with |- context[let (_,_) := ?x in _] => destruct x end.
apply (merge_symm m).

simpl; repeat match goal with |- context[let (_,_) := ?x in _] => destruct x end.
destruct (merge_disjoint _ _ _ _ _ _).
simpl; repeat match goal with |- context[let (_,_) := ?x in _] => destruct x end.

specialize (merge3_assoc Γa Γb Γq Γab' (existT _ Γab (Datatypes.pair Mab' Mab))); intros.
destruct H0 as [Γaq [Maq Maqb]].
apply (merge_functional m) in Maq; subst.
assumption.
Defined.

(* *)