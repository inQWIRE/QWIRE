Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import Contexts.
Require Import TypedCircuits.
(* Import TC. *)
Import ListNotations.
Open Scope list_scope.

(** Projecting out elements of tensors **)

Inductive sigT23 (A:Type) (P Q R : A -> A -> Type) : Type :=
    existT23 : forall (x y : A), P x y -> Q x y -> R x y -> sigT23 A P Q R.

Arguments existT23 {A} {P Q R} x y p1 p2 M.

Program Definition wproj {Γ W1 W2} (p : Pat Γ (Tensor W1 W2)) : 
  sigT23 Ctx (fun x y => Pat x W1) (fun x y => Pat y W2) (fun x y => Valid Γ = x ⋓ y) :=
  match p with 
  | unit => _
  | qubit _ _ _ => _
  | bit _ _ _ => _
  | pair Γ1 Γ2 Γ W1 W2 M p1 p2 => existT23 Γ1 Γ2 p1 p2 M  
  end.

(*** Typechecking Tactic ***)

Open Scope circ_scope.

(* Prevent compute from unfolding important fixpoints *)
Opaque merge.
Opaque wproj.
Opaque Ctx.

(* Local check for multiple evars *)
Ltac has_evars term := 
  match term with
    | ?L = ?R        => has_evar L; has_evar R
    | ?L = ?R        => has_evars L
    | ?L = ?R        => has_evars R
    | ?Γ1 ⋓ ?Γ2      => has_evar Γ1; has_evar Γ2
    | ?Γ1 ⋓ ?Γ2      => has_evars Γ1
    | ?Γ1 ⋓ ?Γ2      => has_evars Γ2
  end.

Ltac strict_rewrite Γ Eq :=
  match goal with
  | [H : context[Valid Γ ⋓ _] |- _ ] => rewrite Eq in H
  | [H : context[_ ⋓ Valid Γ] |- _ ] => rewrite Eq in H
  | [H : context[_ = Valid Γ] |- _ ] => rewrite Eq in H
  | [|- context[Valid Γ]]        => rewrite Eq  
  end.

Ltac osubst :=
  repeat match goal with
  | [ Eq : Valid ?Γ = ?Γ' |- _] => strict_rewrite Γ Eq (* ; clear Eq *)
  end.


(* Rewrite only in goal
Ltac osubst :=
  repeat match goal with
  | [ Eq : Valid ?Γ = ?Γ' |- context[Valid ?Γ]] => rewrite Eq (* ; clear Eq *)
  end.
*)

(*
Ltac osubst :=
  repeat match goal with
  | [ Eq : Valid ?Γ = ?Γ' |- _] => rewrite Eq in *
  end.
*)

(*
Ltac osubst :=
  repeat match goal with
  | [ H : Valid ?Γ = _ ⋓ _ |- _] => let Γ' := fresh "Γ" in
                                  let eq := fresh "eq" in
                                  remember (Valid Γ) as Γ' eqn:eq; clear eq; subst
  end.
*)


Lemma test_osubst : forall Γ1 Γ, Valid Γ1 = Γ -> Γ = Valid Γ1.
Proof.
  intros Γ1 Γ H.
  osubst.
  reflexivity.
Qed.

Ltac type_check_once := 
  intros;
  compute in *; 
  try (apply -> ctx_octx);
  subst; osubst;
  repeat match goal with 
  | [ p : Pat _ One |- _ ]         => inversion p; subst; clear p
  (* new and quite possibly dangerous *)  
  | [ H : ?Γ = _  |- ?Γ = _ ]  => exact H 
  | [ H : _ = ?Γ  |- _ = ?Γ ]  => exact H 
  | [ H : ?Γ = _  |- _ = ?Γ ]  => symmetry; exact H  
  | [ H : _ = ?Γ  |- ?Γ = _ ]  => symmetry; exact H  
  end; 
  (* Runs monoid iff a single evar appears in context *)
  match goal with
  | [|- ?G ] => tryif (has_evars G) then idtac else monoid
  end.

(* Useful for debugging *)
Ltac type_check_num := 
  let pre := numgoals in idtac "Goals before: " pre "";
  [> type_check_once..];
  let post := numgoals in idtac "Goals after: " post "";
  tryif (guard post < pre) then type_check_num else idtac.

(* Easiest solution *)

Ltac type_check := let n := numgoals in do n [> type_check_once..].


(*** Paper Examples ***)

Set Printing Coercions.

Tactic Notation (at level 0) "make_circ" uconstr(C) := refine C; type_check.
Tactic Notation (at level 0) "box'" uconstr(C) := refine (box (fun _ => C)); type_check.

Notation "w1 ⊕ w2" := (pair _ _ _ _ _ _ w1 w2) (at level 10) : circ_scope.
Notation "(())" := unit : circ_scope.

Notation output' p := (output _ p). 
Notation gate' g p1 p2 c := (gate _ _ g p1 (fun _ _ _ p2 => c)).
Notation comp' p c1 c2 := (compose c1 _ (fun _ _ _ p => c2)).
Notation unbox' c p := (unbox c _ p).
Notation bind' p1 p2 p C := (let 'existT23 _ _ p1 p2 _ := wproj p in C). 

Notation "p1 & p2 <-- p ;; C" := (bind' p1 p2 p C) (at level 10). 

(* Future work:
Notation gate' g p1 p2 c := (gate _ _ g p1 (fun _ _ _ z => match z (* w2? *) with
                                                        | p2 => c
                                                        end)). *)

Definition id_circ {W} : Box W W. 
  box' (fun p1 => output' p1).
Defined.

Definition hadamard_measure : Box Qubit Bit.
  box' (fun q => 
   gate' H q q
  (gate' meas q b
  (output' b))).
Defined.

Definition inSeq {W1 W2 W3} (c1 : Box W1 W2) (c2 : Box W2 W3) : Box W1 W3. 
  box' (fun p1 => comp' p2 (unbox' c1 p1) (unbox' c2 p2)).
Defined.

Definition inPar {W1 W2 W1' W2'} (c1 : Box W1 W1') (c2 : Box W2 W2') : 
  Box (W1⊗W2) (W1'⊗W2').
  box' (fun p12 => 
   p1 & p2 <-- p12 ;; 
   (comp' p1' (unbox' c1 p1)
              (comp' p2' (unbox' c2 p2) (output' (p1'⊕p2'))))).
Defined.

Definition init (b : bool) : Box One Qubit.
  make_circ (if b then (box (fun Γ p1 => gate' init1 p1 p2 (output' p2)))
                  else (box (fun Γ p1 => gate' init0 p1 p2 (output' p2)))).
Defined.

Definition bell00 : Box One (Qubit ⊗ Qubit).
  box' (fun p1 => 
  (gate' init0 (()) a
  (gate' init0 (()) b
  (gate' H a a
  (gate' CNOT (a ⊕ b) ab
  (output' ab)))))).

(*
  (* inversion p1. subst. rewrite merge_nil_l. reflexivity. *)
  type_check_once.
  
(*  rewrite merge_nil_l. reflexivity. *)
  type_check_once.

(*  osubst. monoid. *)
  type_check_once.

  Focus 3. type_check_once.

  monoid. (* using osubst will make this unsolvable *)

  type_check_once.
*)

Defined.

Definition alice : Box (Qubit⊗Qubit) (Bit⊗Bit).
  box' (fun qa => 
  (gate' CNOT qa qa
  (q&a <-- qa ;; (gate' H q q
  (gate' meas q x
  (gate' meas a y
  (output' (x ⊕ y)))))))). 
Defined.

Definition bob' : Box (Bit⊗(Bit⊗Qubit)) Qubit.
  box' (fun xyb =>
  (x&yb <-- xyb ;; (gate' (bit_control σx) yb yb
  (y&b <-- yb ;; (gate' (bit_control σz) (x⊕b) xb
  (gate' discard y u   
  (x&b <-- xb ;; (gate' discard x u'
  (output' b))))))))).

(*
symmetry in e0.
rewrite <- merge_assoc in e0.
apply merge_valid in e0 as [_ [Γ]].
apply e0.


Check projT1 (snd (merge_valid _ _ _ e0)).
instantiate (1 := projT1 (snd (merge_valid _ _ _ e0))).

instantiate (1 := let x := c in x).

instantiate (1 := (let Γ := projT1 (snd (merge_valid _ _ _ e0)) in Γ)).

apply (projT2 (snd (merge_valid _ _ _ e0))).
*)

Defined.

Definition bob : Box (Bit⊗Bit⊗Qubit) Qubit.
  box' (fun xyb =>
  (xy&b <-- xyb ;; (x&y <-- xy ;; (gate' (bit_control σx) (y⊕b) yb
  (y&b <-- yb ;; (gate' (bit_control σz) (x⊕b) xb
  (gate' discard y u   
  (x&b <-- xb ;; (gate' discard x u'
  (output' b)))))))))).
Defined.

Definition teleport' : Box Qubit Qubit.
  box' (fun q =>
  (comp' ab (unbox' bell00 (()))
             (a&b <-- ab ;; (comp' xy (unbox' alice (q⊕a))
                           (x&y <-- xy ;; (unbox' bob' (x⊕(y⊕b)))))))).
Defined.

Definition teleport : Box Qubit Qubit.
  box' (fun q =>
  (comp' ab (unbox' bell00 (()))
             (a&b <-- ab ;; (comp' xy (unbox' alice (q⊕a))
                           (x&y <-- xy ;; (unbox' bob (x⊕y⊕b))))))).
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


(** Quantum Fourier Transform **)

Parameter RGate : nat -> Unitary Qubit.

Fixpoint rotationsZ (m : nat) (n : nat) : Box (S (S n) ⨂ Qubit) (S (S n) ⨂ Qubit).
make_circ (
  match n as n0 return n = n0 -> Box (S (S n0) ⨂ Qubit) (S (S n0) ⨂ Qubit) with
  | 0 => fun eq => id_circ 
  | S n' => fun eq => box (fun Γ w =>
    c & qqs <-- w ;; (q & qs <-- qqs ;;  
    (comp' cqs (unbox' (rotationsZ m n') (c ⊕ qs))
               (c & qs <-- cqs ;; (gate' (control (RGate (1 + m - n'))) (c ⊕ q) cq
               (c & q <-- cq ;; (output' (c ⊕ (q ⊕ qs)))))))))
   end (eq_refl n)).
Defined.

Definition rotations (m : nat) (n : nat) : Box (S n ⨂ Qubit) (S n ⨂ Qubit) :=
  match n with 
  | 0 => id_circ
  | S n' => rotationsZ m n' 
  end.

Fixpoint qftZ (n : nat) : Box (S n ⨂ Qubit) (S n ⨂ Qubit).
make_circ (
  match n as n0 return n = n0 -> Box (S n0 ⨂ Qubit) (S n0 ⨂ Qubit) with 
  | 0 => fun eq => box (fun Γ p1 =>  gate' H p1 p2 (output' p2))
  | S n' => fun eq => box (fun Γqw qw =>
             q & w <-- qw ;; 
             (comp' w (unbox' (qftZ n') w) 
                         (unbox' (rotationsZ (S n') n') (q ⊕ w))))
  end (eq_refl n)).
Defined.

Definition qft (n : nat) : Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  match n with 
  | 0 => id_circ
  | S n' => qftZ n'
  end.

(* *)