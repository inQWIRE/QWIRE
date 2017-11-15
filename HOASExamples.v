Require Import Prelim.
Require Import Datatypes.

Require Import TypeChecking.
Import ListNotations.
Open Scope list_scope.

Open Scope circ_scope.

(* Strange. numgoals doesn't seem to work when used as an Obligation Tactic. *)

(*
Ltac type_check' := 
  match goal with
  | [n : nat |- _] => induction n; do 100 [> type_check_once..]; fail
  | [b : bool |- _] => destruct b; do 100 [> type_check_once..]; fail
  | _           => do 100 [> type_check_once..]
  end.
*)

Ltac type_check' := 
  intros;
  repeat match goal with
  | [b : Typed_Box _ _ |- _] => destruct b 
  | [H : WT_Box _ |- _]      => unfold WT_Box in H
  end;
  match goal with
  | [n : nat |- _] => induction n; do 100 [> type_check_once..]; fail
  | [b : bool |- _] => destruct b; do 100 [> type_check_once..]; fail
  | _           => do 100 [> type_check_once..]
  end.

Local Obligation Tactic := type_check'.

Program Definition id_circ {W} : Typed_Box W W :=
  box_ p ⇒ (output p).

Program Definition boxed_gate {W1 W2} (g : Gate W1 W2) : Typed_Box W1 W2 := 
  box_ p ⇒   
    gate_ p2 ← g @p;
    output p2.

Program Definition new_discard : Typed_Box One One := 
  box_ () ⇒ 
    gate_ b ← new0 @();
    gate_ () ← discard @b;
    output (). 

Program Definition init_discard : Typed_Box One One:= 
  box_ () ⇒ 
    gate_ q ← init0 @();
    gate_ b ← meas @q;
    gate_ () ← discard @b;
    output (). 

Program Definition hadamard_measure : Typed_Box Qubit Bit :=
  box_ q ⇒ 
    gate_ q ← H @q;
    gate_ b ← meas @q;
    output b.

Program Definition deutsch (U_f : Unitary (Qubit ⊗ Qubit)) : Typed_Box One Bit :=
  box_ () ⇒ 
    gate_ x ← init0 @();
    gate_ x ← H @x;
    gate_ y ← init1 @();
    gate_ y ← H @y;
    gate_ (x,y) ← U_f @(x,y);
    gate_ x ← H @x; (* found through verification! *)
    gate_ y ← meas @y;
    gate_ () ← discard @y;
    gate_ x ← meas @x;
    output x.

Program Definition lift_deutsch (U_f : Typed_Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)) : 
  Typed_Box One Bit :=
  box_ () ⇒
    gate_ x    ← init0 @();
    gate_ x    ← H @x;
    gate_ y    ← init1 @();
    gate_ y    ← H @y;
    let_ (x,y) ← unbox U_f (x,y);
    gate_ y    ← meas @y;
    gate_ x ← H @x;
    lift_ _    ← y;
    gate_ x ← meas @x;
    output x.

Definition init (b : bool) : Typed_Box One Qubit :=
  if b then boxed_gate init1 else boxed_gate init0.

Program Definition inSeq {w1 w2 w3} (c1 : Typed_Box w1 w2) (c2 : Typed_Box w2 w3) 
  : Typed_Box w1 w3 :=
  box_ p1 ⇒ 
    let_ p2 ← unbox c1 p1;
    unbox c2 p2.

Program Definition inPar {w1 w2 w1' w2'} (c1 : Typed_Box w1 w2) 
        (c2 : Typed_Box w1' w2') : Typed_Box (w1 ⊗ w1') (w2 ⊗ w2'):=
  box_ p12 ⇒ 
    let_ (p1,p2) ← output p12; 
    let_ p1'     ← unbox c1 p1;
    let_ p2'     ← unbox c2 p2; 
    output (p1',p2').

(** Teleport **)

Program Definition bell00 : Typed_Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒  
    gate_ a ← init0 @();
    gate_ b ← init0 @();
    gate_ a ← H @a;
    gate_ z ← CNOT @(a,b);
    output z.

Program Definition alice : Typed_Box (Qubit ⊗ Qubit) (Bit ⊗ Bit) :=
  box_ qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← H @q;
    gate_ x     ← meas @q;
    gate_ y     ← meas @a;
    output (x,y).

Program Definition bob : Typed_Box (Bit ⊗ Bit ⊗ Qubit) Qubit:=
  box_ xyb ⇒ 
    let_ ((x,y),b) ← output xyb ; 
    gate_ (y,b)  ← bit_ctrl X @(y,b);
    gate_ (x,b)  ← bit_ctrl Z @(x,b);
    gate_ ()     ← discard @y ;   
    gate_ ()     ← discard @x ;
    output b.

Program Definition teleport : Typed_Box Qubit Qubit :=
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    unbox bob (x,y,b).

(* Now simplification is quick! *)
(* Note, however, that there are still hidden "compose"s in teleport,
   since our pairs all use let bindings and composition. 
   Sometimes, having let and compose will be unavoidable, since we name the 
   output of a multi-qubit unitary "x" *)
Lemma eteleport : exists x, teleport = x.
Proof.
  unfold teleport.
  unfold bell00, alice, bob.
  simpl.
(* compute. *)
  eauto.
Qed.

Parameter id_gate: Gate Qubit Qubit.

Program Definition bob_lift : Typed_Box (Bit ⊗ Bit ⊗ Qubit) Qubit :=
  box_ xyb ⇒
    let_ (xy, b) ← output xyb; 
    lift_ (u,v)  ← xy;
    gate_ b      ← (if v then X else id_gate) @b;
    gate_ b      ← (if u then Z else id_gate) @b;
    output b.

Program Definition bob_lift' : Typed_Box (Bit ⊗ Bit ⊗ Qubit) Qubit := 
  box_ xyb ⇒
    let_ (xy, b) ← output xyb; 
    lift_ (u,v)  ← xy;
    match u,v with
    | true,  true  => gate_ b ← X @b; gate_ b ← Z @b; output b
    | true,  false => gate_ b ← Z @b; output b
    | false, true  => gate_ b ← X @b; output b
    | false, false => output b
    end.
Next Obligation. destruct b, b0; type_check'. Defined.

Program Definition teleport_lift : Typed_Box Qubit Qubit :=
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    unbox bob_lift (x,y,b).

(* teleport lift outside of bob *)
Program Definition bob_distant (u v : bool) : Typed_Box Qubit Qubit :=
  box_ b ⇒
    gate_ b      ← (if v then X else id_gate) @b;
    gate_ b      ← (if u then Z else id_gate) @b;
    output b.

Program Definition teleport_distant : Typed_Box Qubit Qubit :=
  box_ q ⇒
    let_ (a,b)  ← unbox bell00 () ;
    let_ (x,y)  ← unbox alice (q,a) ;
    lift_ (u,v) ← (x,y) ;
    unbox (bob_distant u v) b.

Program Definition teleport_direct : Typed_Box Qubit Qubit :=
  box_ q ⇒  
  (* bell00 *)
    gate_ a     ← init0 @();
    gate_ b     ← init0 @();
    gate_ a     ← H @a;
    gate_ (a,b) ← CNOT @(a,b);

  (* alice *)
    gate_ (q,a) ← CNOT @(q,a);
    gate_ q     ← H @q;
    gate_ x     ← meas @q;
    gate_ y     ← meas @a;

  (* bob *)
    gate_ (y,b)  ← bit_ctrl X @(y,b);
    gate_ (x,b)  ← bit_ctrl Z @(x,b);
    gate_ ()     ← discard @y;   
    gate_ ()     ← discard @x;
    output b.
  
Lemma teleport_eq : projT1 teleport = projT1 teleport_direct.
Proof.
  unfold teleport, teleport_direct.
  simpl.
  repeat (f_equal; apply functional_extensionality; intros).
  invert_patterns.
  assert (H : wproj (qubit v3, qubit v4) = Datatypes.pair (qubit v3) (qubit v4))
    by reflexivity.
  rewrite H. clear H.
  repeat (f_equal; apply functional_extensionality; intros). 
  invert_patterns. 
  assert (H : wproj (qubit v5, qubit v6) = Datatypes.pair (qubit v5) (qubit v6))
    by reflexivity.
  rewrite H; clear H.
  simpl. reflexivity.
Qed.

(* Right associative Tensor. Right associative with a trailing One  *)
Fixpoint NTensor (n : nat) (W : WType) := 
  match n with 
  | 0    => One
  | S n' => W ⊗ NTensor n' W
  end.

Infix "⨂" := NTensor (at level 30). 
(* Transparent Tensor. *)
(* Opaque NTensor. *)

Program Fixpoint inSeqMany (n : nat) {W} (c : Typed_Box W W) : Typed_Box W W:= 
  match n with
  | 0 => id_circ
  | S n' => inSeq c (inSeqMany n' c)
  end.

Program Fixpoint inParMany (n : nat) {W W'} (c : Typed_Box W W') : Typed_Box (n ⨂ W) (n ⨂ W') := 
  match n with 
  | 0    => id_circ
  | S n' => inPar c (inParMany n' c)
  end.

(** Quantum Fourier Transform **)

Parameter RGate : nat -> Unitary Qubit.

(* Check against Quipper implementation *)
(* n + 2 = number of qubits, m = additional argument *)
Fixpoint urotations (n m : nat) {struct n}
                 : Box ((S (S n) ⨂ Qubit)) ((S (S n) ⨂ Qubit)) :=
  match n with
  | 0    => id_circ
  | S n' => match n' with
            | 0 => id_circ
            | S _ => 
               box (fun w =>
               let_ (c,(q,qs))  ← output w;  
               let_ (c,qs)      ← unbox (urotations n' m) (c,qs);
               gate_ (c,q)      ← ctrl (RGate (m + 2 - n')) @(c,q);
               output (c,(q,qs)))
            end
   end.

Lemma rotations_WT : forall n m, WT_Box (urotations n m).
Proof. 
  induction n as [ | [ | n]]; type_check.
   apply IHn. 
  type_check.
Qed. 

Definition rotations (n m : nat) : Typed_Box ((S (S n) ⨂ Qubit)) ((S (S n) ⨂ Qubit)) := existT _ (urotations n m) (rotations_WT n m).

(*
Lemma rotations_WT : forall n m, Typed_Box (rotations n m).
(* not sure why this used to be easier: induction n; [|destruct n]; type_check.  *)
Proof. 
  induction n as [ | [ | n]]; type_check.
   apply IHn. 
  type_check.
Qed. 
*)


Opaque rotations.

Program Fixpoint uqft (n : nat) : Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  match n with 
  | 0    => id_circ
  | S n' => match n' with
           | 0 =>     box (fun qu =>
                     let_ (q,u) ← output qu; 
                     gate_ q    ← H @q;
                     output (q,u))
           | S n'' => box (fun qqs =>
                     let_ (q,qs) ← output qqs; 
                       let_ qs     ← unbox (uqft n') qs; 
                       let_ (q,qs) ← unbox (urotations n'' n') (q,qs);
                       gate_ q     ← H @q;
                       output (q,qs))
           end
  end.
Next Obligation. reflexivity. Defined.

Lemma qft_WT : forall n, WT_Box  (uqft n).
Proof. induction n as [ | [ | n]]; type_check.
       apply rotations_WT; type_check.
Qed. (* This has become disturbingly slow *)

Definition qft (n : nat) : Typed_Box (n ⨂ Qubit) (n ⨂ Qubit) := 
  existT _ (uqft n) (qft_WT n).

(************************)
(** Coin Flip Circuits **)
(************************)

Program Definition coin_flip : Typed_Box One Bit :=
  box_ () ⇒
    gate_ q  ← init0 @();
    gate_ q  ← H @q;
    gate_ b  ← meas @q;
    output b.

Fixpoint ucoin_flips (n : nat) : Box One Bit :=
  box (fun _ =>
  match n with
  | 0    => gate_ x ← new1 @(); output x
  | S n' => let_  c      ← unbox (ucoin_flips n') ();
            gate_ q     ← init0 @();
            gate_ (c,q) ← bit_ctrl H @(c,q);
            gate_ ()    ← discard @c;
            gate_ b     ← meas @q;
            output b
  end).

(*
Program Fixpoint coin_flips (n : nat) : Typed_Box One Bit :=
  box_ () ⇒
  match n with
  | 0    => gate_ x ← new1 @(); output x
  | S n' => let_  c      ← unbox (coin_flips n') ();
            gate_ q     ← init0 @();
            gate_ (c,q) ← bit_ctrl H @(c,q);
            gate_ ()    ← discard @c;
            gate_ b     ← meas @q;
            output b
  end.
Next Obligation. induction n as [|n' IHn]; type_check.                 
                 destruct (coin_flips n') as [c WT].
                 simpl.
                 apply WT.
                 constructor.
Defined. GAH! *)

Lemma coin_flips_WT : forall n, WT_Box (ucoin_flips n).
Proof. intros. induction n; type_check. Qed.

Definition coin_flips (n : nat) : Typed_Box One Bit := 
  existT _ (ucoin_flips n) (coin_flips_WT n).

Fixpoint coin_flips_lift (n : nat) : Box One Bit := 
  box (fun _ => 
  match n with
  | 0    => gate_ q ← new1 @(); output q
  | S n' => let_ q  ← unbox (coin_flips_lift n') ();
           lift_ x ← q;
           if x then unbox coin_flip ()
                else gate_ q ← new0 @(); output q
  end).
Lemma coin_flips_lift_WT : forall n, WT_Box (coin_flips_lift n).
Proof. intros. induction n; type_check. Qed.

Definition n_coins (n : nat) : Typed_Box (n ⨂ One) (n ⨂ Bit) := (inParMany n coin_flip).

Fixpoint units (n : nat) : Pat (n ⨂ One) := 
  match n with
  | O => ()
  | S n' => ((), units n')
  end.

Lemma types_unit_empty : forall Γ n (p : Pat (n ⨂ One)), Types_Pat Γ p -> Γ = ∅.
Proof.
  intros Γ n p H.
  induction n; type_check.
  rewrite merge_nil_l in IHn.
  eapply IHn.
  apply H0.
Qed.    

Lemma empty_types_unit : forall n, Types_Pat ∅ (units n).
Proof.
  intros n.
  induction n; type_check.
Qed.    


Program Definition n_coins' (n : nat) : Typed_Box (n ⨂ One) (n ⨂ Bit) := 
  box_ () ⇒ (unbox (inParMany n coin_flip) (units n)).
Next Obligation. apply (projT2 (inParMany _ _ )).
                 apply types_unit_empty in H; subst.
                 apply empty_types_unit.
Defined.

(** Unitary Transpose **)

Program Definition unitary_transpose {W} (U : Unitary W) : Typed_Box W W := 
  box_ p ⇒
    gate_ p ← U @p;
    gate_ p ← transpose U @p;
    output p.

(* Produces qubits *)
Program Fixpoint prepare_basis (li : list bool) : Typed_Box One (length li ⨂ Qubit) :=
  match li with
  | []       => id_circ
  | b :: bs  => box_ () ⇒ 
                 let_ p1 ← unbox (init b) (); 
                 let_ p2 ← unbox (prepare_basis bs) ();
                 output (p1, p2)
  end.
Next Obligation. rewrite merge_nil_r. reflexivity. 
                 apply (projT2 (init b)).
                 all: type_check.
                 destruct (prepare_basis bs) as [c WT].
                 apply WT.
                 assumption.
Defined.

Program Definition lift_eta : Typed_Box Bit Qubit :=
  box_ q ⇒ 
    lift_ x ← q;
    unbox (init x) ().
Next Obligation. type_check. Defined.

Program Definition lift_meas : Typed_Box Bit Bit :=
  box_ q ⇒
    lift_ x ← q;
    gate_ p ← (if x then new1 else new0) @();
    output p.

(** Classical Gates **)

(* NOT already exists *)

Program Definition AND : Typed_Box (Qubit ⊗ Qubit) Qubit :=
  box_ ab ⇒
    let_ (a,b)      ← output ab;
    gate_ z         ← init0 @();
    gate_ (a,(b,z)) ← CCNOT @(a,(b,z));
    gate_ a         ← meas @a;
    gate_ b         ← meas @b;
    gate_ ()        ← discard @a;   
    gate_ ()        ← discard @b;   
    output z.

Program Definition OR : Typed_Box (Qubit ⊗ Qubit) Qubit :=
  box_ ab ⇒ 
    let_ (a,b)       ← output ab;
    gate_ a'         ← X @a;
    gate_ b'         ← X @b;
    let_ z           ← unbox AND (a',b');
    gate_ z'         ← X @z;
    output z'.

(** Invalid Circuits **)
(*
Program Definition absurd_circ : Typed_Box Qubit (Bit ⊗ Qubit) :=
  box_ w ⇒ 
    gate_ x  ← meas @w ;
    gate_ w' ← H @w ;
    output (x,w').
Next Obligation. Abort.

Program Definition unmeasure : Typed_Box Qubit Qubit :=
  box_ q ⇒ 
    gate_ q ← H @q ;
    gate_ b ← meas @q ;
    output q.
Next Obligation. Abort.

Program Definition unused_qubit : Typed_Box Qubit One :=
  box_ w ⇒ 
   gate_ w ← H @w ;
   output ().
Next Obligation. Abort.

Program Definition clone : Typed_Box Qubit (Qubit ⊗ Qubit) := box_ p ⇒ (output (p,p)).
Next Obligation. Abort.

Program Definition split_qubit : Typed_Box Qubit (Qubit ⊗ Qubit) :=
  box_ w ⇒ 
    let_ (w1,w2)  ← output w ;
    gate_ w2'     ← H @w2 ; 
    output (w1,w2').
Next Obligation. Abort.
*)

Close Scope circ_scope.
(* *)