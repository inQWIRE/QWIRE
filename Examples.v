Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import TypedCircuits.
Import TC.
Import ListNotations.
Open Scope list_scope.

(* Untyped patterns *)
Inductive UPat := uvar : Var -> UPat | uunit | upair : UPat -> UPat -> UPat.

(* Untyped to typed *)
Fixpoint make_singleton (v : Var) (W : WType) : Ctx := 
  match v with
  | O => [Some W]
  | (S v') => None :: make_singleton v' W
  end.

Fixpoint make_SingletonCtx (v : Var) (W : WType) : 
  SingletonCtx v W (make_singleton v W) :=
  match v with
  | O => SingletonHere W
  | (S v') => SingletonLater _ _ _ (make_SingletonCtx v' W)
  end.

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

Fixpoint make_context (p : UPat) (W : WType) : Ctx :=
  match p with
  | uvar v => make_singleton v W
  | uunit => []
  | upair p1 p2 => match W with 
               | W1 ⊗ W2 => merge (make_context p1 W1) (make_context p2 W2)
               | _ => [] (* Fails *)
               end
  end.

Lemma merge_eq : forall Γ1 Γ2 Γ3, MergeCtx Γ1 Γ2 Γ3 -> merge Γ1 Γ2 = Γ3.
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

(* Can turn into a function that returns an Option?
Program Fixpoint type_pat (p : UPat) (W : WType) : (Pat (make_context p W) W) :=
  match p with
  | uvar v => var _ _ _ (make_SingletonCtx v W)
  | uunit => unit 
  | upair p1 p2 => match W with 
                  | W1 ⊗ W2 => pair _ _ _ _ _ _ (type_pat p1 W1) (type_pat p2 W2)
                  | _ => unit (* Really Fails *)
                  end
  end. 
Next Obligation. 
*)

(* Alternatives for simple patterns *)

(*
Definition type_var (v : Var) (W : WType) : Pat (make_singleton v W) W :=
  var _ _ _ (make_SingletonCtx v W).


Search (_ <> _) bool.

Program Definition type_pair (v1 v2 : Var) (W1 W2 : WType) {pf : (v1 =? v2) = false}: 
  Pat (make_context (upair (uvar v1) (uvar v2)) (W1 ⊗ W2)) (W1 ⊗ W2) :=
  pair _ _ _ _ _ _ (type_var v1 W1) (type_var v2 W2).
Obligation 1. 
  apply Nat.eqb_neq in pf. 
  generalize dependent v2.
  induction v1; intros.
  destruct v2. tauto.
  simpl; apply MergeCons; constructor.
  simpl.
  destruct v2.
  simpl. apply MergeCons. constructor.
  destruct (make_singleton v1 W1); simpl; constructor.
  simpl.
  constructor.
  constructor.
  apply IHv1.
  intros Eq; subst; tauto.
Defined.
*)

(* Projecting out elements of tensors *)
Program Definition wproj {Γ W1 W2} (p : Pat Γ (Tensor W1 W2)) : 
  {Γ1 : Ctx & Pat Γ1 W1 } * {Γ2 : Ctx & Pat Γ2 W2} :=
  match p with 
  | unit => _
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
(*
Notation "w1 , w2" := (upair w1 w2) (at level 11, left associativity) : circ_scope.
*)

Notation "w1 , w2" := (pair _ _ _ _ _ _ w1 w2) (at level 11, left associativity) : circ_scope.

Notation "(())" := unit : circ_scope.


(* Some wire patterns *)
Definition q : Var := 0.
Definition w : Var  := 1.
Definition w': Var  := 2.
Definition a : Var  := 3.
Definition b : Var  := 4.
Definition x : Var  := 5.
Definition y : Var  := 6.
Definition w1 : Var := 7.
Definition w1': Var := 8.
Definition w2 : Var := 9.
Definition w2': Var := 10.

Check q.
Check w1.
 
(* Getting contexts for input patterns *)

Open Scope circ_scope.

(*** Tactics ***)

Lemma merge_l_eq : forall Γ1 Γ2, MergeCtx [] Γ1 Γ2 -> Γ1 = Γ2.
Proof. intros Γ1 Γ2 H. inversion H; subst; reflexivity. Qed.

Lemma merge_r_eq : forall Γ1 Γ2, MergeCtx Γ1 [] Γ2 -> Γ1 = Γ2.
Proof. intros Γ1 Γ2 H. inversion H; subst; reflexivity. Qed.

Ltac find_pat := 
  repeat match goal with 
  | [ H : ?P |- ?P ] => exact H
  | [ H : MergeCtx [] ?Γ1 ?Γ2 |- _] => apply merge_l_eq in H; subst
  | [ H : MergeCtx ?Γ1 [] ?Γ2 |- _] => apply merge_r_eq in H; subst
  end.

Ltac type_check_circ := 
  intros;
  compute;
  (* Compute in hyps will screw things up here *)
  repeat match goal with 
  | [ H : _  = wproj ?p |- _ ]      => apply wproj_merge in H
  end;
  compute in *;
  repeat match goal with 
  | [ |- ?Γ = ?Γ ]                  => reflexivity
  (* from find_pat *)
  | [ H : ?P |- ?P ]                => exact H
  | [ H : MergeCtx [] ?Γ1 ?Γ2 |- _] => apply merge_l_eq in H; subst 
  | [ H : MergeCtx ?Γ1 [] ?Γ2 |- _] => apply merge_r_eq in H; subst
  | [ H : MergeCtx ?Γ1 ?Γ2 ?Γ3 |- MergeCtx ?Γ2 ?Γ1 ?Γ3 ] => apply (mergeSymm H)
  | [ |- Pat [] One ]               => apply unit
  | [ |- SingletonCtx _ ?W (?C :: [])]  => apply SingletonHere
  | [ |- SingletonCtx _ ?W (None :: _)] => apply SingletonLater
  (* From context checking *)
  | [ |- MergeCtx [] _ _]           => apply MergeNilL
  | [ |- MergeCtx _ [] _]           => apply MergeNilR
  | [ |- MergeCtx _ _ []]           => apply MergeNilL (* Both work *)
  end.

(* Should be element of, but company coq is annoying *)
(* Infix " ⊂ " := get_context (at level 50). *)

(*
Notation "'Box' w ⊂ W => C" := (box (make_context w W) w C _ _) (at level 60) 
                               : circ_scope.
*)

(*
Definition out (v : Var) (W : WType ) := output (type_var v W).
*)

(*** Paper Examples ***)

(* Local Obligation Tactic := type_check_circ. *)

(* I don't like having to specify these at all. 
   It basically means no more variables. *)

(* Program Definition id_circ : Circuit [Some Qubit] Qubit := output _.
Next Obligation. type_check_circ. Defined. *)

Program Definition id_circ {W} :  Box W W := 
  box (fun Γ p1 => output p1).


(*
Program Definition id_circ' : Circuit _ _ := 
  output (type_var q Qubit).
*)

(*
Program Definition id_circ : Circuit _ _ := out w Qubit. 
*)

Check id_circ.
Print id_circ.
Eval simpl in id_circ.
Eval compute in id_circ.

(*
Eval compute in id_circ'.
*)

(*
Program Definition hadamard_c : Circuit [Some Qubit] Qubit :=
  gate [] H (type_var q Qubit) (fun Γ2 Γ2' M2 p2 => output p2) _ .
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined.
(*
Next Obligation. apply merge_r_eq in H1. subst. assumption. Defined.
Next Obligation. apply MergeNilR. Defined.
*)

(* Doesn't work. Why not?
Program Definition hadamard_c : Circuit [Some Qubit] Qubit :=
  gate [] H (make_pattern q Qubit) (fun _ _ _ _ => output (make_pattern q Qubit)) _ .
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined. *)

Program Definition hadamard_measure_c : Circuit [Some Qubit] Bit :=
  gate [] H (type_var q Qubit) 
  (fun Γ2 Γ2' M2 p2 => gate [] meas p2
  (fun Γ3 Γ3' M3 p3 => output p3) _) _ .
Next Obligation. type_check_circ. Defined.

Check box.
*)

Program Definition hadamard_measure : Box Qubit Bit :=
  box (fun Γ p1 => 
   gate [] _ H p1 
  (fun Γ2 Γ2' M2 p2 => gate [] _ meas p2
  (fun Γ3 Γ3' M3 p3 => output p3))).
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined.
  
(* This - correctly - fails to type check!*)
(*
Program Definition absurd_circ : Boxed_Circ Qubit (Bit ⊗ Qubit) := 
  Box w ⊂ Qubit =>
    (gate meas w x 
    (gate H w w'
    (output (x,w')))).
Obligation 2. Abort. 
*)

(*
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
*)

Program Definition init : Box One Qubit :=
  if b then (box (fun Γ p1 => gate [] _ init1 p1 (fun Γ2 Γ2' M2 p2 => output p2)))
       else (box (fun Γ p1 => gate [] _ init0 p1 (fun Γ2 Γ2' M2 p2 => output p2))).
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined.

(*
Program Definition init (b : bool) : Boxed_Circ One Qubit := 
  if b then (Box unit ⊂ One => (gate init1 unit w (output w)))
       else (Box unit ⊂ One => (gate init0 unit w (output w))).
*)

Parameter Δ1 Δ2 Δ3 Δ4 Δ5 : Ctx.

Program Definition bell00 : Box One (Qubit ⊗ Qubit) :=
(* I don't like this. Would be much simpler if I could force Γ = [] *)
  box (fun Γ p1 => 
  (gate [] _ init0 p1
  (fun Γ2 Γ2' M2 p2 => gate Γ2 _ init0 (())
  (fun Γ3 Γ3' M3 p3 => gate Γ3 _ (* Γ2'? *) H p2
  (fun Γ4 Γ4' M4 p4 => gate [] _ CNOT (p3,p4) 
  (fun Γ5 Γ5' M5 p5 => output p5)))))).
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined.

(*
Program Definition bell00' : Box One (Qubit ⊗ Qubit) :=
(* I don't like this. Would be much simpler if I could force Γ = [] *)
  box (fun Γ p1 => 
  (gate Γ init0 (())
  (fun Γ2 Γ2' M2 p2 => gate (merge Γ2 Γ) init0 (())
  (fun Γ3 Γ3' M3 p3 => gate (merge Γ3 Γ) (* Γ2'? *) H p2
  (fun Γ4 Γ4' M4 p4 => gate Δ4 CNOT (p3,p4) 
  (fun Γ5 Γ5' M5 p5 => output p5) _ ) _) _) _)).
Obligation 7. type_check_circ. Defined.
Obligation 6. erewrite merge_eq. constructor. assumption. Defined.
Obligation 5. type_check_circ.
*)  

(*
Program Definition bell00 : Boxed_Circ One (Qubit ⊗ Qubit) :=
  Box unit ⊂ One =>
    (gate init0 unit a
    (gate init0 unit b
    (gate H a a
    (gate CNot (a,b) (a,b)
    (output (a,b)))))).
*)

(* Work in progress *)
Notation "⟨ p1 , p2 , Γ1 , Γ2 ⟩ ↩ p $ exp" := match wproj p with 
  Datatypes.pair (existT _ Γ1 p1) (existT _ Γ2 p2) => exp end (at level 20).

Program Definition alice : Box (Qubit⊗Qubit) (Bit⊗Bit) :=
  box (fun Γ qa => 
  (gate [] _ CNOT qa
  (fun Γ2 Γ2' M2 p2 => match wproj p2 with Datatypes.pair (existT _ Γq q) (existT _ Γa a) =>
  (*  let ((existT _ Γ1'' q), (existT _ Γ2'' a)) := wproj p2 in *)
     gate Γa _ H q
  (fun Γ3 Γ3' M3 p3 => gate Γa _ meas p3
  (fun Γ4 Γ4' M4 p4 => gate Γ4 _ meas a 
  (fun Γ5 Γ5' M5 p5 => output (p4,p5)))) 
end))).
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined.
Next Obligation. type_check_circ. Defined.

(*
Program Definition alice : Boxed_Circ (Qubit⊗Qubit) (Bit⊗Bit) :=
  Box (q,a) ⊂ Qubit⊗Qubit =>
    (gate CNot (q,a) (q,a)
    (gate H q q
    (gate meas q x
    (gate meas a y
    (output (x,y)))))).
*)

(* Have to rename to avoid conflicts *)
Lemma merge_trans_l : forall Γ1 Γ2 Γ3 Γ4 Γ',
  MergeCtx Γ1 Γ3 Γ' -> 
  MergeCtx Γ2 Γ' Γ4 ->
  MergeCtx (merge Γ1 Γ2) Γ3 Γ4.
Proof.
  intros Γ1 Γ2 Γ3 Γ4 Γ' H0 H1.
  generalize dependent Γ'.
  generalize dependent Γ4.
  generalize dependent Γ3.
  generalize dependent Γ1.
  induction Γ2.
  + intros Γ1 Γ3 Γ4 Γ' H0 H1. 
    apply merge_l_eq in H1.
    subst.
    destruct Γ1; assumption.
  + intros Γ1 Γ3 Γ4 Γ' H0 H1.
    destruct Γ1.     
    - simpl. 
      apply merge_l_eq in H0; subst.
      assumption.
    - simpl. 
      inversion H0; subst.
      * inversion H1; subst.
        apply mergeSymm in H1.
        apply merge_eq in H1.
        simpl in H1. rewrite H1.
        constructor.
      * inversion H1; subst.
        destruct o, a0, o2, o4; inversion H4; subst; inversion H9; subst; simpl in *;
        constructor; try constructor; eapply IHΓ2; try apply H7; try apply H10.
Qed.

Lemma merge_trans_r : forall Γ1 Γ2 Γ3 Γ4 Γ',
  MergeCtx Γ1 Γ2 Γ' -> 
  MergeCtx Γ3 Γ' Γ4 ->
  MergeCtx Γ1 (merge Γ2 Γ3) Γ4.
Proof.
  intros Γ1 Γ2 Γ3 Γ4 Γ' H0 H1.
  apply mergeSymm.
  eapply merge_trans_l.
  apply (mergeSymm H0).
  apply H1.
Qed.  

Lemma manual_merge_symm : forall Γ1 Γ2, merge Γ1 Γ2 = merge Γ2 Γ1.
Proof.
  intros Γ1. 
  induction Γ1; intros Γ2.
  destruct Γ2; reflexivity.  
  destruct Γ2; trivial.
  simpl. 
  rewrite IHΓ1.
  destruct a0, o; reflexivity.
Qed.

Program Definition bob : Box (Bit⊗Bit⊗Qubit) Qubit :=
  box (fun Γxyb xyb =>
    match wproj xyb with Datatypes.pair (existT _ Γx x) (existT _ Γyb yb) =>
    gate Δ1 _ (bit_control σx) yb 
     (fun Γyb Γyb' Myb yb =>
      match wproj yb with Datatypes.pair (existT _ Γy y) (existT _ Γb b) =>
      gate Δ2 _ (bit_control σz) (x,b)
       (fun Γxb Γxb' Mxb xb =>
        match wproj xb with Datatypes.pair (existT _ Γx x) (existT _ Γb b) =>
        gate Δ3 _ discard y 
         (fun Γz1 Γz1 Mz1 z1 =>
          gate Δ4 _ discard x
          (fun Γz2 Γz2' Mz2 z2 => output b))
        end)
      end)
    end).




Program Definition bob : Box (Bit⊗Bit⊗Qubit) Qubit :=
  box (fun Γxyb xyb =>
    match wproj xyb with Datatypes.pair (existT _ Γx x) (existT _ Γyb yb) =>
    gate Γx _ (bit_control σx) yb 
     (fun Γyb Γyb' Myb yb =>
      match wproj yb with Datatypes.pair (existT _ Γy y) (existT _ Γb b) =>
      gate (merge Γx Γy) _ (bit_control σz) (x,b)
       (fun Γ2 Γ2' M2 p2 =>
        match wproj p2 with Datatypes.pair (existT _ Γx x) (existT _ Γb b) =>
        gate Δ3 _ discard y 
         (fun Γ3 Γ3' M3 p3 =>
          gate Δ4 _ discard x
          (fun Γ4 Γ4' M4 p4 => output b))
        end)
      end)
    end).
Next Obligation. type_check_circ. Defined.
Next Obligation. unfold bob_obligation_2. 
                 apply wproj_merge in Heq_anonymous.
                 apply wproj_merge in Heq_anonymous0.
                 clear - Heq_anonymous Heq_anonymous0 Myb.
                 rewrite manual_merge_symm.
                 eapply merge_trans_r.
                 apply (mergeSymm Heq_anonymous).
                 apply (mergeSymm Myb). Defined.                 
Next Obligation. type_check_circ.
                 clear - Heq_anonymous Heq_anonymous0 Myb.
                 



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

Parameter run2 : Boxed_Circ One Bit -> bool.

Program Definition flip : bool := 
  run 
  (gate init0 unit q
  (gate H q q
  (gate meas q b
  (output b)))).


Program Definition flip2 : bool := 
  run2 
  (Box unit ⊂ One => 
  (gate init0 unit q
  (gate H q q
  (gate meas q b
  (output b))))).


(* *)