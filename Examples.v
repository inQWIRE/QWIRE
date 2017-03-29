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
  sigT23 OCtx (fun x y => Pat x W1) (fun x y => Pat y W2) (fun x y => Γ = x ⋓ y) :=
  match p with 
  | unit => _
  | qubit _ _ _ => _
  | bit _ _ _ => _
  | pair Γ1 Γ2 Γ W1 W2 v M p1 p2 => existT23 Γ1 Γ2 p1 p2 M  
  end.
Program Definition elim_unit {Γ} (p : Pat Γ One) : Γ = ∅ :=
  match p with
  | unit => _
  | qubit _ _ _ => _
  | bit _ _ _ => _
  | pair Γ1 Γ2 Γ W1 W2 v M p1 p2 => _
  end.
  

(** More Validity Lemmas **)

Lemma valid_empty : is_valid ∅. Proof. unfold is_valid; eauto. Qed.

Lemma pat_ctx_valid : forall Γ W, Pat Γ W -> is_valid Γ.
Proof. intros Γ W p. unfold is_valid. inversion p; eauto. Qed.
 
(*** Typechecking Tactic ***)

Open Scope circ_scope.

(* Prevent compute from unfolding important fixpoints *)
Opaque merge.
Opaque wproj.
Opaque Ctx.
Opaque is_valid.

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

Ltac validate :=
  repeat match goal with
  | [p : Pat ?Γ ?W |- _ ]       => apply pat_ctx_valid in p
  | [|- is_valid ∅ ]               => apply valid_empty
  | [H : is_valid ?Γ |- is_valid ?Γ ] => exact H
  | [H: is_valid (?Γ1 ⋓ ?Γ2) |- is_valid (?Γ2 ⋓ ?Γ1) ] => rewrite merge_comm;
                                                   exact H
  (* Reduce hypothesis to binary disjointness *)
  | [H: is_valid (?Γ1 ⋓ (?Γ2 ⋓ ?Γ3)) |- _ ] => rewrite merge_assoc in H
  | [H: is_valid (?Γ1 ⋓ ?Γ2 ⋓ ?Γ3) |- _ ]   => apply valid_split in H as [? [? ?]]
  (* Reduce goal to binary disjointness *)
  | [|- is_valid (?Γ1 ⋓ (?Γ2 ⋓ ?Γ3)) ] => rewrite merge_assoc
  | [|- is_valid (?Γ1 ⋓ ?Γ2 ⋓ ?Γ3) ]   => apply valid_join; validate
  end.  

Ltac type_check_once := 
  intros;
  compute in *; 
  subst; 
  repeat match goal with 
  | [ p : Pat _ One |- _ ]         => inversion p; subst; clear p
  end; 
  (* Runs monoid iff a single evar appears in context *)
  match goal with
  | [|- ?A = ?B ] => tryif (has_evars (A = B)) then idtac else monoid
  | [|- is_valid ?Γ] => tryif (has_evar Γ) then idtac else validate
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

Notation "w1 ⊕ w2" := (pair _ _ _ _ _ _ _ w1 w2) (at level 10) : circ_scope.
Notation "(())" := unit : circ_scope.

Notation output' p := (output _ p). 
Notation gate' g p1 p2 c := (gate _ _ _ g p1 (fun _ _ _ _ p2 => c)).
Notation comp' p c1 c2 := (compose c1 _ _ (fun _ _ _ _ p => c2)).
Notation unbox' c p := (unbox c _ p).
Notation bind' p1 p2 p C := (let 'existT23 _ _ p1 p2 _ := wproj p in C). 

Notation "p1 & p2 <-- p ;; C" := (bind' p1 p2 p C) (at level 10). 
Notation "() <-- p ;; C" := (let pf := elim_unit p in C) (at level 10).

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

(* TODO: Deutch algorithm *)

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