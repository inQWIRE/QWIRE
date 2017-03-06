Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import TypedCircuits.
Import TC.
Import ListNotations.
Open Scope list_scope.

(* Projecting out elements of tensors *)
Inductive sigT23 (A:Type) (P Q R : A -> A -> Type) : Type :=
    existT23 : forall (x y : A), P x y -> Q x y -> R x y -> sigT23 A P Q R.

(*
Notation "{ x, y : A & P & Q & R }" := (sigT23 A (fun x y => P) (fun x y => Q) (fun x y => R)).
*)

Arguments existT23 {A} {P Q R} x y p1 p2 M.

Program Definition wproj {Γ W1 W2} (p : Pat Γ (Tensor W1 W2)) : 
  sigT23 OCtx (fun x y => Pat x W1) (fun x y => Pat y W2) (fun x y => Γ = x ⋓ y) :=
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
Opaque merge.
Opaque wproj.
Opaque Ctx.

Ltac type_check_once := 
  intros;
  compute in *;
  subst;
  repeat match goal with 
  | [ p : Pat _ One |- _ ]          => inversion p; subst; clear p
  | [ |- ?Γ = ?Γ ]                  => reflexivity 
  | [ |- context[?Γ ⋓ ∅] ]          => rewrite (merge_nil_r Γ)
  | [ |- context[∅ ⋓ ?Γ] ]          => rewrite (merge_nil_l Γ)
  | [ |- ?Γ ⋓ _ = ?Γ  ]             => apply merge_nil_r
  | [ |- _ ⋓ ?Γ = ?Γ ]              => apply merge_nil_l
  | [ |- ?Γ = ?Γ ⋓ _ ]              => rewrite merge_nil_r; reflexivity
  | [ |- ?Γ = _ ⋓ ?Γ ]              => rewrite merge_nil_l; reflexivity
  | [ |- ?Γ ⋓ _ = ?Γ ⋓ _ ]          => apply merge_cancel_l
  | [ |- ?Γ ⋓ _ = ?Γ' ⋓ ?Γ ⋓ _ ]    => rewrite (merge_comm Γ' Γ)
  (* These are too precise, will make general rules *)
  | [ |- ?Γ ⋓ ?Γ1 ⋓ _ = ?Γ ⋓ ?Γ2 ⋓ _ ] => rewrite (merge_assoc Γ Γ1), 
                                        (merge_assoc Γ Γ2); idtac "assoc right 0"
  | [ |- ?Γ1 ⋓ ?Γ ⋓ _ = ?Γ2 ⋓ ?Γ ⋓ _ ] => rewrite (merge_comm Γ1 Γ), (merge_comm Γ2 Γ);
                                       rewrite (merge_assoc Γ Γ1), (merge_assoc Γ Γ2);
                                       idtac "assoc right 1"
  | [ |- ?Γ ⋓ ?Γ1 ⋓ _ = ?Γ2 ⋓ ?Γ ⋓ _ ] => rewrite (merge_comm Γ2 Γ); 
                                       rewrite (merge_assoc Γ Γ1), (merge_assoc Γ Γ2);
                                       idtac "assoc right 2"
  | [ |- ?Γ1 ⋓ ?Γ ⋓ _ = ?Γ ⋓ ?Γ2 ⋓ _ ] => rewrite (merge_comm Γ1 Γ);
                                       rewrite (merge_assoc Γ Γ1), (merge_assoc Γ Γ2);
                                       idtac "assoc right 3"
  | [ |- ?Γ ⋓ _ = _ ⋓ ?Γ ]          => apply merge_comm (* danger? *)
  | [ |- _ ⋓ ?Γ = ?Γ ⋓ _ ]          => apply merge_comm (* danger? *)
  | [ |- ?Γ1 = ?Γ2 ]                => is_evar Γ1; reflexivity
  | [ |- ?Γ1 = ?Γ2 ]                => is_evar Γ2; reflexivity
  | [ |- ?Γ1 ⋓ (?Γ2 ⋓ ?Γ3) = _ ]    => rewrite <- (merge_assoc Γ1 Γ2 Γ3); 
                                     idtac "rassoc lhs"
  | [ |- _ = ?Γ1 ⋓ (?Γ2 ⋓ ?Γ3) ]    => rewrite <- (merge_assoc Γ1 Γ2 Γ3); 
                                     idtac "rassoc rhs"
  end.

(* No subst
Ltac type_check_once := 
  intros;
  compute in *;
  repeat match goal with 
  | [ |- ?Γ = ?Γ ]                  => reflexivity
  | [ |- ?Γ = ?Γ ⋓ _ ]              => rewrite merge_nil_r; reflexivity
  | [ |- ?Γ = _ ⋓ ?Γ ]              => rewrite merge_nil_l; reflexivity
  | [ H: ?Γ1 = ?Γ2 |- ?Γ1 = ?Γ2 ]   => apply H 
  end.
*)

(* Useful for debugging *)
Ltac type_check_num := 
  let pre := numgoals in idtac "Goals before: " pre "";
  [> type_check_once..];
  let post := numgoals in idtac "Goals after: " post "";
  tryif (guard post < pre) then type_check_num else idtac.

(* Easiest solution *)
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

Definition bob' : Box (Bit⊗(Bit⊗Qubit)) Qubit. 
refine(
  box (fun Γxyb xyb =>
    let 'existT23 Γx Γyb x yb Mxyb := wproj xyb in
    gate _ _ (bit_control σx) yb
     (fun Γyb Γyb' Myb yb' =>
     let 'existT23 Γy' Γb' y' b' Myb' := wproj yb' in
      gate _ _ (bit_control σz) (x * b') (* <? *)
       (fun Γxb Γxb' Mxb xb =>
        gate _ _ discard y' 
         (fun Γz1 Γz1 Mz1 z1 =>
          let 'existT23 Γx' Γb'' x' b'' Mxb := wproj xb in
          gate _ _ discard x'
           (fun Γz2 Γz2' Mz2 z2 => output _ b'')))))); type_check.
Defined.

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
Defined.

(*
Definition teleport' : Box Qubit Qubit.
  refine(
  box (fun Γq q =>
    compose (unbox bell00 _ unit) _
      (fun Γab Γab' Mab ab => 
       let 'existT23 Γa Γb a b Mab' := wproj ab in 
       compose (unbox alice _ (q * a)) _
               (fun Γxy Γxy' Mxy xy => 
                  let 'existT23 Γx Γy x y Mxy := wproj xy in 
                  unbox bob' _ (x * (y * b))))
      )); type_check.
Defined.
*)

Definition teleport : Box Qubit Qubit.
  refine(
  box (fun _ q =>
    compose (unbox bell00 _ unit) _
      (fun _ _ _ ab => 
       let 'existT23 _ _ a b _ := wproj ab in 
       compose (unbox alice _ (q * a)) _
               (fun _ _ _ qa => unbox bob _ (qa * b)))
      )); type_check.
Defined.


(* Right associative Tensor *)
Fixpoint Tensor (n : nat) (W : WType) := 
  match n with 
  | 0 => One
  | 1 => W
  | S n' =>  W ⊗ (Tensor n' W)
  end.

Infix "⨂" := Tensor (at level 30). 
(* Transparent Tensor. *)
Opaque Tensor.

Fixpoint inSeqMany {W} (n :nat) (c : Box W W) : Box W W := 
  match n with
  | 0 => id_circ
  | 1 => c
  | S n' => inSeq c (inSeqMany n' c)
  end.

Print inSeqMany.

(* Zero-indexed variant. I don't know why this is necessary *)
(* This will be fairly common *)
Fixpoint inParManyZ {W1 W2} (n : nat) (c : Box W1 W2) {struct n} : 
  Box (S n ⨂ W1) (S n ⨂ W2) :=
  match n with 
  | 0 => c
  | S n' => inPar c (inParManyZ n' c)
  end. 

Definition inParMany {W1 W2} (n : nat) (c : Box W1 W2) : Box (n ⨂ W1) (n ⨂ W2) := 
  match n with 
  | 0 => id_circ
  | S n' => inParManyZ n' c 
  end.

Eval compute in inParMany 4 hadamard_measure.

Parameter RGate : nat -> Unitary Qubit.

Local Obligation Tactic := type_check.

Fixpoint rotationsZ (m : nat) (n : nat) : Box (S (S n) ⨂ Qubit) (S (S n) ⨂ Qubit).
refine (
  match n as n0 return n = n0 -> Box (S (S n0) ⨂ Qubit) (S (S n0) ⨂ Qubit) with
  | 0 => fun eq => id_circ 
  | S n' => fun eq => box (fun Γ w =>
    let 'existT23 Γc Γqqs c qqs Mcqqs := wproj w in 
    let 'existT23 Γq Γqs q qs Mqqs := wproj qqs in 
    compose (unbox (rotationsZ m n') _ (c * qs)) _
            (fun Γcqs Γcqs' Mcqs cqs =>  
               let 'existT23 Γc' Γqs' c' qs' Mcqs' := wproj cqs in 
               gate _ _ (control (RGate (1 + m - n'))) (c' * q)
               (fun Γcq Γcq' Mcq cq => 
               let 'existT23 Γc'' Γq'' c'' q'' Mcq' := wproj cq in 
               output _ (c'' * (q'' * qs')))))
   end (eq_refl n)); type_check.
Defined.

Definition rotations (m : nat) (n : nat) : Box (S n ⨂ Qubit) (S n ⨂ Qubit) :=
  match n with 
  | 0 => id_circ
  | S n' => rotationsZ m n' 
  end.

Fixpoint qftZ (n : nat) : Box (S n ⨂ Qubit) (S n ⨂ Qubit).
refine(
  match n as n0 return n = n0 -> Box (S n0 ⨂ Qubit) (S n0 ⨂ Qubit) with 
  | 0 => fun eq => (box (fun Γ p1 =>  gate _ _ H p1 (fun Γ2 Γ2' M2 p2 => output _ p2)))
  | S n' => fun eq => box (fun Γqw qw =>
             let 'existT23 Γq Γw q w Mqw := wproj qw in
             compose (unbox (qftZ n') _ w) _
                     (fun Γw' Γw'' Mw' w' => (unbox (rotationsZ (S n') n') _ (q * w'))))
  end (eq_refl n)); type_check.
Defined.

Definition qft (n : nat) : Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  match n with 
  | 0 => id_circ
  | S n' => qftZ n'
  end.


(* *)