Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import TypedCircuits.
Import TC.
Import ListNotations.
Open Scope list_scope.

(** The merge function **)

Fixpoint merge_atom (W1 W2 : option WType) : option WType := 
  match W1, W2 with
  | None, W' => W'
  | W', None => W'
  | _, _     => None (* ERROR CASE *) 
  end.

Fixpoint merge (ctx1 ctx2 : Ctx) : Ctx :=
  match ctx1, ctx2 with 
  | [], _ => ctx2
  | _, [] => ctx1
  | (c1 :: ctx1'), (c2 :: ctx2') => 
    (merge_atom c1 c2) :: (merge ctx1' ctx2')
  end.

Infix "∪" := merge (at level 30). 

Lemma merge_eq : forall Γ1 Γ2 Γ3, MergeCtx Γ1 Γ2 Γ3 -> Γ1 ∪ Γ2 = Γ3.
Proof.
  intros.
  generalize dependent Γ1. 
  generalize dependent Γ2. 
  induction Γ3.
  + intros.
    inversion H0; subst; reflexivity.
  + intros.  
    inversion H0; subst.
    - reflexivity.
    - reflexivity.
    - simpl. 
      rewrite IHΓ3; trivial.
      inversion H5; reflexivity.
Qed. 

(* Have to rename to avoid conflicts *)
Lemma merge_trans_l : forall Γ1 Γ2 Γ3 Γ4 Γ',
  MergeCtx Γ1 Γ3 Γ' -> 
  MergeCtx Γ2 Γ' Γ4 ->
  MergeCtx (Γ1 ∪ Γ2) Γ3 Γ4.
Proof.
  intros Γ1 Γ2 Γ3 Γ4 Γ' H0 H1.
  generalize dependent Γ'.
  generalize dependent Γ4.
  generalize dependent Γ3.
  generalize dependent Γ1.
  induction Γ2.
  + intros Γ1 Γ3 Γ4 Γ' H0 H1. 
    apply merge_nil_l in H1.
    subst.
    destruct Γ1; assumption.
  + intros Γ1 Γ3 Γ4 Γ' H0 H1.
    destruct Γ1.     
    - simpl. 
      apply merge_nil_l in H0; subst.
      assumption.
    - simpl. 
      inversion H0; subst.
      * inversion H1; subst.
        apply merge_symm in H1.
        apply merge_eq in H1.
        simpl in H1. rewrite H1.
        constructor.
      * inversion H1; subst.
        destruct o, a, o2, o4; inversion H4; subst; inversion H9; subst; simpl in *;
        constructor; try constructor; eapply IHΓ2; try apply H7; try apply H10.
Qed.

Lemma merge_trans_r : forall Γ1 Γ2 Γ3 Γ4 Γ',
  MergeCtx Γ1 Γ2 Γ' -> 
  MergeCtx Γ3 Γ' Γ4 ->
  MergeCtx Γ1 (Γ2 ∪ Γ3) Γ4.
Proof.
  intros Γ1 Γ2 Γ3 Γ4 Γ' H0 H1.
  apply merge_symm.
  eapply merge_trans_l.
  apply (merge_symm H0).
  apply H1.
Qed.  

Lemma manual_merge_symm : forall Γ1 Γ2, Γ1 ∪ Γ2 = Γ2 ∪ Γ1.
Proof.
  intros Γ1. 
  induction Γ1; intros Γ2.
  destruct Γ2; reflexivity.  
  destruct Γ2; trivial.
  simpl. 
  rewrite IHΓ1.
  destruct a, o; reflexivity.
Qed.

Lemma manual_merge_assoc : forall Γ1 Γ2 Γ3, 
  Γ1 ∥ Γ2 ->
  Γ2 ∥ Γ3 ->
  (Γ1 ∪ Γ2) ∪ Γ3 = Γ1 ∪ (Γ2 ∪ Γ3).
Proof.
  intros Γ1 Γ2.
  generalize dependent Γ1.
  induction Γ2.
  + intros; simpl.
    destruct Γ1; reflexivity.
  + intros; simpl.
    destruct Γ1, Γ3; simpl; trivial.
    rewrite IHΓ2.
    - destruct o, a, o0; trivial.
      inversion H0.
      inversion H2; subst.
      inversion H8.    
    - inversion H0.
      inversion H2; subst.
      exists g. assumption.
    - inversion H1.
      inversion H2; subst.
      exists g. assumption.
Qed.

Lemma disjoint_merge : forall Γ1 Γ2, Γ1 ∥ Γ2 -> MergeCtx Γ1 Γ2 (Γ1 ∪ Γ2).
Proof.
  intros Γ1 Γ2 H0.
  unfold disjoint in H0.
  destruct H0.
  specialize (merge_eq _ _ _ m); intros; subst.
  assumption.
Qed.

Lemma pairwise_disjoint : forall Γ1 Γ2 Γ3, 
  Γ1 ∥ Γ2 -> Γ2 ∥ Γ3 -> Γ1 ∥ Γ3 -> (Γ1 ∪ Γ2) ∥ Γ3.
Proof.
  intros Γ1 Γ2. generalize dependent Γ1.
  induction Γ2; intros.
  + destruct Γ1; simpl; assumption. 
  + destruct Γ1, Γ3; simpl; trivial.
    - apply disjoint_nil_r.
    - apply disjoint_cons_inv in H0 as [D12 [o12 mo12]].
      apply disjoint_cons_inv in H1 as [D23 [o23 mo23]].
      apply disjoint_cons_inv in H2 as [D13 [o13 mo13]].
      apply disjoint_cons with (o := merge_atom o12 o0) .
      destruct o, a, o0; inversion mo12; inversion mo23; inversion mo13; subst;
      simpl; constructor.
      apply IHΓ2; assumption.
Qed.      
        
(* Projecting out elements of tensors *)
Program Definition wproj {Γ W1 W2} (p : Pat Γ (Tensor W1 W2)) : 
  {Γ1 : Ctx & Pat Γ1 W1 } * {Γ2 : Ctx & Pat Γ2 W2} :=
  match p with 
  | unit => _
  | qubit _ _ _ => _
  | bit _ _ _ => _
  | pair ctx1 ctx2 ctx w1 w2 M' p1 p2 => (existT _ ctx1 p1, existT _ ctx2 p2)  
  end.

(* Necessary associated lemma *)
Lemma wproj_merge : forall Γ Γ1 Γ2 W1 W2 p1 p2 (p : Pat Γ (Tensor W1 W2)),
  (existT (fun Γ1 : Ctx => Pat Γ1 W1) Γ1 p1, existT (fun Γ2 : Ctx => Pat Γ2 W2) Γ2 p2) 
   = wproj p -> 
  MergeCtx Γ1 Γ2 Γ.
Proof.
  intros Γ Γ1 Γ2 W1 W2 p1 p2 p H.
  dependent destruction p.
  inversion H0; subst.
  assumption.
Qed.

(* Dangerous to take this notation *)
Notation "a , b" := (Datatypes.pair a b) (at level 11, left associativity) : default_scope.
Notation "w1 , w2" := (pair _ _ _ _ _ _ w1 w2) (at level 11, left associativity) : circ_scope.
Notation "(())" := unit : circ_scope.

Parameter Δ1 Δ2 Δ3 Δ4 Δ5 Δ6 Δ7: Ctx.

(* Getting contexts for input patterns *)

Open Scope circ_scope.

(*** Tactics ***)

(* Prevent compute from unfolding important fixpoints *)
Opaque merge.
Opaque wproj.
Opaque Ctx.

Ltac type_check_circ := 
  intros;
  compute in *;
  repeat match goal with 
  | [ |- Ctx ]                      => simpl (* do not try random ctx or permute goal *)
  | [ |- ?Γ = ?Γ ]                  => reflexivity
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ3 |- MergeCtx ?Γ1 ?Γ2 ?Γ3 ] => exact H
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ3 |- MergeCtx ?Γ2 ?Γ1 ?Γ3 ] => apply (merge_symm H)
  | [ H : _  = wproj ?p |- _ ]      => apply wproj_merge in H
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


(*** Paper Examples ***)

Local Obligation Tactic := type_check_circ.

Program Definition id_circ {W} :  Box W W := 
  box (fun Γ p1 => output p1).

(*
Program Definition id_circ' : Circuit _ _ := 
  output (type_var q Qubit).
*)

Program Definition hadamard_measure : Box Qubit Bit :=
  box (fun Γ p1 => 
   gate [] _ H p1 
  (fun Γ2 Γ2' M2 p2 => gate [] _ meas p2
  (fun Γ3 Γ3' M3 p3 => output p3))).

Program Definition inSeq {W1 W2 W3} (c1 : Box W1 W2) (c2 : Box W2 W3) : Box W1 W3  := 
  box (fun Γ1 p1 => @compose Γ1 W2 (unbox c1 p1) [] Γ1 W3 _ 
                                (fun Γ2 Γ2' M2 p2 => unbox c2 p2)). 

Program Definition inPar {W1 W2 W1' W2'} (c1 : Box W1 W1') (c2 : Box W2 W2') : 
  Box (W1⊗W2) (W1'⊗W2') :=
  box (fun Γ12 p12 => 
   match wproj p12 with Datatypes.pair (existT _ Γ1 p1) (existT _ Γ2 p2) =>
   @compose Γ1 W1' (unbox c1 p1) Γ2 Γ12 (W1'⊗W2') _
                   (fun Γ3 Γ3' M3 p1' => @compose Γ2 W2' (unbox c2 p2) Γ3 Γ3' (W1'⊗W2')
                                       _ (fun Γ4 Γ4' M4 p2' => (output (p1',p2')))) 
   end).

Program Definition init (b : bool) : Box One Qubit :=
  if b then (box (fun Γ p1 => gate [] _ init1 p1 (fun Γ2 Γ2' M2 p2 => output p2)))
       else (box (fun Γ p1 => gate [] _ init0 p1 (fun Γ2 Γ2' M2 p2 => output p2))).

Program Definition bell00 : Box One (Qubit ⊗ Qubit) :=
(* I don't like this. Would be much simpler if I could force Γ = [] *)
  box (fun Γ p1 => 
  (gate [] _ init0 p1
  (fun Γ2 Γ2' M2 p2 => gate Γ2 _ init0 (())
  (fun Γ3 Γ3' M3 p3 => gate Γ3 _ (* Γ2'? *) H p2
  (fun Γ4 Γ4' M4 p4 => gate [] _ CNOT (p3,p4) 
  (fun Γ5 Γ5' M5 p5 => output p5)))))).
Next Obligation. apply Γ4'. Defined.

(* Work in progress *)
Notation "⟨ p1 , p2 , Γ1 , Γ2 ⟩ ↩ p $ exp" := match wproj p with 
  Datatypes.pair (existT _ Γ1 p1) (existT _ Γ2 p2) => exp end (at level 20).

Program Definition alice : Box (Qubit⊗Qubit) (Bit⊗Bit) :=
  box (fun Γ qa => 
  (gate [] _ CNOT qa
  (fun Γ2 Γ2' M2 p2 => match wproj p2 with Datatypes.pair (existT _ Γq q) (existT _ Γa a) =>
     gate Γa _ H q
  (fun Γ3 Γ3' M3 p3 => gate Γa _ meas p3
  (fun Γ4 Γ4' M4 p4 => gate Γ4 _ meas a 
  (fun Γ5 Γ5' M5 p5 => output (p4,p5)))) 
end))).

Program Definition bob : Box (Bit⊗Bit⊗Qubit) Qubit :=
  box (fun Γxyb xyb =>
    match wproj xyb with Datatypes.pair (existT _ Γxy xy) (existT _ Γb b) =>
    match wproj xy with Datatypes.pair (existT _ Γx x) (existT _ Γy y) =>
    gate Γx _ (bit_control σx) (y,b) 
     (fun Γyb Γyb' Myb yb =>
      match wproj yb with Datatypes.pair (existT _ Γy' y') (existT _ Γb' b') =>
      gate Γy' _ (bit_control σz) (x,b')
       (fun Γxb Γxb' Mxb xb =>
        gate Γxb _ discard y' 
         (fun Γz1 Γz1 Mz1 z1 =>
          match wproj xb with Datatypes.pair (existT _ Γx' x') (existT _ Γb'' b'') =>
          gate Γb'' _ discard x'
           (fun Γz2 Γz2' Mz2 z2 => output b'')
          end))
      end)
    end
    end).
Next Obligation. apply (merge Γy Γb). Defined.
Next Obligation. eapply merge_trans_l.
                 apply (merge_symm Heq_anonymous). 
                 apply (merge_symm Heq_anonymous0). Defined.
Next Obligation. specialize (merge_disjoint _ _ _ _ _ Heq_anonymous Heq_anonymous0). 
                 intros [D1 D2].
                 apply disjoint_merge.
                 assumption. Defined.
Next Obligation. apply (merge Γb' Γx). Defined.
Next Obligation. eapply merge_trans_l.
                 apply (merge_symm Heq_anonymous). 
                 apply (merge_symm Myb). Defined.
Next Obligation. apply merge_symm.
                 specialize (merge_disjoint _ _ _ _ _ Heq_anonymous Myb). 
                 intros [D1 D2].
                 apply disjoint_merge.
                 assumption. Defined.

Program Definition teleport : Box Qubit Qubit :=
  box (fun Γq q =>
    @compose [] (Qubit⊗Qubit) (unbox bell00 unit) Γq Γq Qubit _
      (fun Γab Γab' Mab ab => 
       match wproj ab with Datatypes.pair (existT _ Γa a) (existT _ Γb b) =>
       @compose (merge Γq Γa) (Bit⊗Bit) (unbox alice (q,a)) Γb (merge Γq Γab) Qubit _
         (fun Γxy Γxy' Mxy xy => unbox bob (xy,b))
       end)
      ).
Next Obligation. apply disjoint_merge.
                 apply disjoint_symm.
                 eapply merge_disjoint.
                 apply (merge_symm Heq_anonymous).
                 apply Mab. Defined.
Next Obligation. assert (Γa ∥ Γb) as Dab.
                   exists Γab. assumption.
                 specialize (merge_disjoint _ _ _ _ _ Heq_anonymous Mab).
                 intros [Daq Dbq].
                 apply merge_eq in Heq_anonymous.
                 subst.                 
                 apply disjoint_symm in Daq.
                 apply disjoint_symm in Dbq.
                 rewrite <- manual_merge_assoc; trivial.
                 apply disjoint_merge; trivial.
                 apply pairwise_disjoint; assumption. Defined.
Next Obligation. apply merge_eq. apply (merge_symm Mab). Defined.

(* *)