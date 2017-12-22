Require Import Prelim.
Require Import Datatypes.

Require Import TypeChecking.
Import ListNotations.
Open Scope list_scope.

Open Scope circ_scope.


Definition apply_box {w1 w2} (b : Box w1 w2) (c : Circuit w1) : Circuit w2 :=
  let_ x ← c;
  unbox b x.
Notation "b $ c" := (apply_box b c)  (left associativity, at level 11).
Coercion output : Pat >-> Circuit.


Definition id_circ {W} : Box W W :=
  box_ p ⇒ (output p).
Lemma id_circ_WT : forall W, Typed_Box (@id_circ W).
Proof. type_check. Qed.

Definition boxed_gate {W1 W2} (g : Gate W1 W2) : Box W1 W2 := 
  box_ p ⇒   
    gate_ p2 ← g @p;
    output p2.
Coercion boxed_gate : Gate >-> Box.

Lemma boxed_gate_WT {W1 W2} (g : Gate W1 W2) : Typed_Box (boxed_gate g).
Proof. type_check. Qed.

(***********************)
(* Structural circuits *)
(***********************)

Definition init (b : bool) : Box One Qubit :=
  if b then boxed_gate init1 else boxed_gate init0.
Lemma init_WT : forall b, Typed_Box (init b).
Proof. destruct b; type_check. Defined.

Definition inSeq {w1 w2 w3} (c1 : Box w1 w2) (c2 : Box w2 w3): Box w1 w3 :=
  box_ p1 ⇒ 
    let_ p2 ← unbox c1 p1;
    unbox c2 p2.
Notation "b' · b" := (inSeq b b') (right associativity, at level 10) : circ_scope.
Lemma inSeq_WT : forall W1 W2 W3 (c1 : Box W1 W2) (c2 : Box W2 W3), 
                 Typed_Box c1 -> Typed_Box c2 -> Typed_Box (c2 · c1).
Proof. type_check. Qed.

Definition inPar {w1 w2 w1' w2'} 
                 (c1 : Box w1 w2) (c2 : Box w1' w2') : Box (w1 ⊗ w1') (w2 ⊗ w2'):=
  box_ p12 ⇒ 
    let_ (p1,p2) ← output p12; 
    let_ p1'     ← unbox c1 p1;
    let_ p2'     ← unbox c2 p2; 
    output (p1',p2').
Notation "b1 || b2" := (inPar b1 b2).
Lemma inPar_WT : forall W1 W1' W2 W2' (c1 : Box W1 W2) (c2 : Box W1' W2'), 
  Typed_Box c1 -> Typed_Box c2 ->
  Typed_Box (c1 || c2).
Proof. type_check. Qed.

(* Right associative Tensor. Right associative with a trailing One  *)
Fixpoint NTensor (n : nat) (W : WType) := 
  match n with 
  | 0    => One
  | S n' => W ⊗ NTensor n' W
  end.

Infix "⨂" := NTensor (at level 30). 
(* Transparent Tensor. *)
(* Opaque NTensor. *)

Fixpoint units (n : nat) : Pat (n ⨂ One) := 
  match n with
  | O => unit
  | S n' => (unit, units n')
  end. 
Lemma types_units : forall n, Types_Pat ∅ (units n).
Proof. induction n; type_check. Qed.
Notation "(())" := (units _) (at level 8).

(* Can also just use (init b) #n $ (()) *)
Fixpoint initMany (b : bool) (n : nat) : Box One (n ⨂ Qubit):= 
  match n with 
  | 0    => id_circ
  | S n' => box_ () ⇒ 
           let_ q  ← unbox (init b) ();
           let_ qs ← unbox (initMany b n') ();
           output (q, qs)
  end.
Lemma initMany_WT : forall b n, Typed_Box (initMany b n).
Proof. induction n; type_check. apply init_WT. assumption. Qed.

Fixpoint inSeqMany (n : nat) {W} (c : Box W W) : Box W W:= 
  match n with
  | 0 => id_circ
  | S n' => inSeq c (inSeqMany n' c)
  end.
Lemma inSeqMany_WT : forall n W (c : Box W W), 
      Typed_Box c -> Typed_Box (inSeqMany n c).
Proof. intros. induction n as [ | n']; type_check. Qed.

Fixpoint inParMany (n : nat) {W W'} (c : Box W W') : Box (n ⨂ W) (n ⨂ W') := 
  match n with 
  | 0    => id_circ
  | S n' => inPar c (inParMany n' c)
  end.
Lemma inParMany_WT : forall n W W' (c : Box W W'), Typed_Box c  -> 
                                 Typed_Box (inParMany n c).
Proof. intros. induction n as [ | n']; type_check. Qed.       

Notation "g # n" := (inParMany n g) (at level 8).

(* Example circuits *)

Definition new_discard : Box One One := 
  box_ () ⇒ 
    gate_ b ← new0 @();
    gate_ () ← discard @b;
    output (). 
Lemma new_discard_WT : Typed_Box new_discard.
Proof. type_check. Qed.

Definition init_discard : Box One One:= 
  box_ () ⇒ 
    gate_ q ← init0 @();
    gate_ b ← meas @q;
    gate_ () ← discard @b;
    output (). 
Lemma init_discard_WT : Typed_Box init_discard.
Proof. type_check. Qed.

Definition hadamard_measure : Box Qubit Bit :=
  box_ q ⇒ 
    gate_ q ← H @q;
    gate_ b ← meas @q;
    output b.
Lemma hadamard_measure_WT : Typed_Box hadamard_measure.
Proof. type_check. Qed.

(* Variations on deutsch's algorithm *)

Definition U_deutsch (U__f : Unitary (Qubit ⊗ Qubit)) : Box One Bit :=
  box_ () ⇒ 
    gate_ x ← init0 @();
    gate_ x ← H @x;
    gate_ y ← init1 @();
    gate_ y ← H @y;
    gate_ (x,y) ← U__f @(x,y);
    gate_ x ← H @x; (* found through verification! *)
    gate_ y ← meas @y;
    gate_ () ← discard @y;
    gate_ x ← meas @x;
    output x.
Lemma U_deutsch_WT : forall U__f, Typed_Box (U_deutsch U__f).
Proof. type_check. Qed.

Definition lift_deutsch (U__f : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)) : Box One Bit :=
  box_ () ⇒
    gate_ x    ← init0 @();
    gate_ x    ← H @x;
    gate_ y    ← init1 @();
    gate_ y    ← H @y;
    let_ (x,y) ← unbox U__f (x,y);
    gate_ y    ← meas @y;
    gate_ x ← H @x;
    lift_ _    ← y;
    gate_ x ← meas @x;
    output x.
Lemma lift_deutsch_WT : forall U__f, Typed_Box U__f ->
                               Typed_Box (lift_deutsch U__f).
Proof. type_check. Qed.

Definition deutsch (U__f : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)) : Box One Bit :=
  box_ () ⇒ 
    let_ x     ← H · init0 $ ();
    let_ y     ← H · init1 $ ();
    let_ (x,y) ← U__f $ (x,y);
    let_ _     ← discard · meas $ y;
    meas $ x.
Lemma deutsch_WF : forall U__f, Typed_Box U__f -> Typed_Box (deutsch U__f).
Proof. type_check. Qed.

Definition Deutsch_Jozsa (n : nat) (U__f : Box (S n ⨂ Qubit) (S n ⨂ Qubit)) : 
  Box One (n ⨂ Bit) := 
  box_ () ⇒
  let_ q      ← H · init1 $ (); 
  let_ qs     ← (H· init0) #n $ (());
  let_ (q,qs) ← U__f $ (q,qs);   
  let_ qs     ← (meas · H) #n $ qs;
  let_ ()     ← discard · meas $q; 
  output qs. 
Lemma Deutsch_Jozsa_WT : forall n U__f, Typed_Box U__f -> Typed_Box (Deutsch_Jozsa n U__f).
Proof.
  intros n U__f U_WT.
  induction n.
  + type_check.
  + specialize (inParMany_WT) as WT_Par.
    specialize types_units as WT_units.
    type_check.
    4: apply WT_Par. 
    20: apply WT_Par. 
    all: type_check.
    apply types_units.
Qed.    

(*******************)
(** Teleportation **)
(*******************)

Definition bell00 : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒  
    let_ a ← H · init0 $();
    let_ b ← init0 $();
    CNOT $(a,b).

Lemma bell00_WT : Typed_Box bell00.
Proof. type_check. Qed.

Definition alice : Box (Qubit ⊗ Qubit) (Bit ⊗ Bit) :=
  box_ qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← H @q;
    gate_ x     ← meas @q;
    gate_ y     ← meas @a;
    output (x,y).
Lemma alice_WT : Typed_Box alice.
Proof. type_check. Qed.

Definition bob : Box (Bit ⊗ Bit ⊗ Qubit) Qubit :=
  box_ xyb ⇒ 
    let_ ((x,y),b) ← output xyb ; 
    gate_ (y,b)  ← bit_ctrl X @(y,b);
    gate_ (x,b)  ← bit_ctrl Z @(x,b);
    gate_ ()     ← discard @y ;   
    gate_ ()     ← discard @x ;
    output b.
Lemma bob_WT : Typed_Box bob.
Proof. type_check. Qed.

Definition teleport :=
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    unbox bob (x,y,b).

Lemma teleport_WT : Typed_Box teleport.
Proof. type_check. Defined.

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

Definition bob_lift : Box (Bit ⊗ Bit ⊗ Qubit) Qubit :=
  box_ xyb ⇒
    let_ (xy, b) ← output xyb; 
    lift_ (u,v)  ← xy;
    gate_ b      ← (if v then X else id_gate) @b;
    gate_ b      ← (if u then Z else id_gate) @b;
    output b.
Lemma bob_lift_WT : Typed_Box bob_lift.
Proof. type_check. Defined.

Definition bob_lift' := 
  box_ xyb ⇒
    let_ (xy, b) ← output xyb; 
    lift_ (u,v)  ← xy;
    match u,v with
    | true,  true  => gate_ b ← X @b; gate_ b ← Z @b; output b
    | true,  false => gate_ b ← Z @b; output b
    | false, true  => gate_ b ← X @b; output b
    | false, false => output b
    end.
Lemma bob_lift_WT' : Typed_Box bob_lift'.
Proof. type_check. Defined.

Definition teleport_lift : Box Qubit Qubit :=
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    unbox bob_lift (x,y,b).
Lemma teleport_lift_WT : Typed_Box teleport_lift.
Proof. type_check. Defined.


(* teleport lift outside of bob *)
Definition bob_distant (u v : bool) : Box Qubit Qubit :=
  box_ b ⇒
    let_ b ← unbox (if v then boxed_gate X else id_circ) b;
    let_ b ← unbox (if u then boxed_gate Z else id_circ) b;
    output b.
Lemma bob_distant_WT : forall b1 b2, Typed_Box (bob_distant b1 b2).
Proof. destruct b1,b2; type_check. Defined.

Definition teleport_distant : Box Qubit Qubit :=
  box_ q ⇒
    let_ (a,b)  ← unbox bell00 () ;
    let_ (x,y)  ← unbox alice (q,a) ;
    lift_ (u,v) ← (x,y) ;
    unbox (bob_distant u v) b.
Lemma teleport_distant_WT : Typed_Box teleport_distant.
Proof. type_check. all: try destruct b; try destruct b0; type_check. Qed.

Definition teleport_direct :=
  box_ q ⇒  
  (* bell00 *)
    gate_ a     ← init0 @();
    gate_ a     ← H @a;
    gate_ b     ← init0 @();
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
Lemma teleport_direct_WT : Typed_Box teleport_direct.
Proof. type_check. Qed.

Lemma teleport_eq : teleport = teleport_direct.
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

(*******************************)
(** Quantum Fourier Transform **)
(*******************************)

Parameter RGate : nat -> Unitary Qubit.

(* Check against Quipper implementation *)
(* n + 2 = number of qubits, m = additional argument *)
Fixpoint rotations (n m : nat) {struct n}
                 : Box ((S (S n) ⨂ Qubit)) ((S (S n) ⨂ Qubit)) :=
  match n with
  | 0    => id_circ
  | S n' => match n' with
            | 0 => id_circ
            | S _ => 
               box_ w ⇒
               let_ (c,(q,qs))  ← output w;  
               let_ (c,qs)      ← unbox (rotations n' m) (c,qs);
               gate_ (c,q)      ← ctrl (RGate (m + 2 - n')) @(c,q);
               output (c,(q,qs))
            end
   end.
Lemma rotations_WT : forall n m, Typed_Box (rotations n m).
(* not sure why this used to be easier: induction n; [|destruct n]; type_check.  *)
Proof. 
  induction n as [ | [ | n]]; type_check.
   apply IHn. 
  type_check.
Qed. 


Opaque rotations.

Program Fixpoint qft (n : nat) : Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  match n with 
  | 0    => id_circ
  | S n' => match n' with
           | 0 =>     box_ qu ⇒ 
                     let_ (q,u) ← output qu; 
                     gate_ q    ← H @q;
                     output (q,u)
           | S n'' => box_ qqs ⇒
                     let_ (q,qs) ← output qqs; 
                       let_ qs     ← unbox (qft n') qs; 
                       let_ (q,qs) ← unbox (rotations n'' n') (q,qs);
                       gate_ q     ← H @q;
                       output (q,qs)
           end
  end.

Lemma qft_WT : forall n, Typed_Box  (qft n).
Proof. induction n as [ | [ | n]]; type_check.
       apply rotations_WT; type_check.
Qed.

(************************)
(** Coin Flip Circuits **)
(************************)

Definition coin_flip : Box One Bit :=
  box_ () ⇒
    gate_ q  ← init0 @();
    gate_ q  ← H @q;
    gate_ b  ← meas @q;
    output b.
Lemma coin_flip_WT : Typed_Box coin_flip.
Proof. type_check. Qed.

Fixpoint coin_flips (n : nat) : Box One Bit :=
  box_ () ⇒
  match n with
  | 0    => gate_ x ← new1 @(); output x
  | S n' => let_  c     ← unbox (coin_flips n') ();
            gate_ q     ← init0 @();
            gate_ (c,q) ← bit_ctrl H @(c,q);
            gate_ ()    ← discard @c;
            gate_ b     ← meas @q;
            output b
  end.
Lemma coin_flips_WT : forall n, Typed_Box (coin_flips n).
Proof. intros. induction n; type_check. Qed.

Fixpoint coin_flips_lift (n : nat) : Box One Bit := 
  box_ () ⇒ 
  match n with
  | 0    => gate_ q ← new1 @(); output q
  | S n' => let_ q  ← unbox (coin_flips_lift n') ();
           lift_ x ← q;
           if x then unbox coin_flip ()
                else gate_ q ← new0 @(); output q
  end.
Lemma coin_flips_lift_WT : forall n, Typed_Box (coin_flips_lift n).
Proof. intros. induction n; type_check. Qed.

Definition n_coins (n : nat) : Box (n ⨂ One) (n ⨂ Bit) := (inParMany n coin_flip).

Fixpoint units (n : nat) : Pat (n ⨂ One) := 
  match n with
  | O => ()
  | S n' => ((), units n')
  end.

Definition n_coins' (n : nat) : Box (n ⨂ One) (n ⨂ Bit) := 
  box_ () ⇒ (unbox (inParMany n coin_flip) (units n)).

(** Unitary Transpose **)

Definition unitary_transpose {W} (U : Unitary W) : Box W W := 
  box_ p ⇒
    gate_ p ← U @p;
    gate_ p ← transpose U @p;
    output p.
Lemma unitary_transpose_WT : forall W (U : Unitary W), Typed_Box (unitary_transpose U).
Proof. type_check. Qed.

(* Produces qubits *)
Fixpoint prepare_basis (li : list bool) : Box One (length li ⨂ Qubit) :=
  match li with
  | []       => id_circ
  | b :: bs  => box_ () ⇒ 
                 let_ p1 ← unbox (init b) (); 
                 let_ p2 ← unbox (prepare_basis bs) ();
                 output (p1, p2)
  end.
Lemma prepare_basis_WT : forall li, Typed_Box (prepare_basis li).
Proof. induction li; type_check. apply init_WT; assumption. Qed.


Fixpoint share n : Box Qubit (S n ⨂ Qubit) :=
  match n with
  | 0    => box (fun q => output (q,()))
  | S n' => box_ q ⇒ 
              let_ q' ← init0 $();
              let_ (q,q') ← CNOT $(q,q');
              let_ qs ← share n' $q';
              output (q,qs)
  end.
Lemma share_WT : forall n, Typed_Box (share n).
Proof. induction n; type_check. Qed.

Definition lift_eta : Box Bit Qubit :=
  box_ q ⇒ 
    lift_ x ← q;
    unbox (init x) ().
Lemma lift_eta_bit_WT : Typed_Box lift_eta.
Proof. type_check. apply init_WT. type_check. Qed.

Definition lift_meas : Box Bit Bit :=
  box_ q ⇒
    lift_ x ← q;
    gate_ p ← (if x then new1 else new0) @();
    output p.
Lemma lift_meas_WT : Typed_Box lift_meas.
Proof. type_check. Qed.

(*********************)
(** Classical Gates **)
(*********************)

(* NOT already exists *)

(* AND uses a Taffoli gate with one ancilla *)
Definition AND : Box (Qubit ⊗ Qubit) Qubit :=
  box_ ab ⇒
    let_ (a,b)      ← output ab;
    gate_ z         ← init0 @();
    gate_ (a,(b,z)) ← CCNOT @(a,(b,z));
    gate_ a         ← meas @a;
    gate_ b         ← meas @b;
    gate_ ()        ← discard @a;   
    gate_ ()        ← discard @b;   
    output z.
Lemma AND_WT : Typed_Box AND.
Proof. type_check. Qed.

(* XOR just wraps a CNOT *)
Definition XOR : Box (Qubit ⊗ Qubit) Qubit := 
  box_ ab ⇒ 
    let_ (a,b)   ← output ab;
    gate_ (a, b) ← CNOT @(a,b);
    gate_ a      ← meas @a;
    gate_ ()     ← discard @a;
    output b.

Lemma XOR_WT : Typed_Box XOR.
Proof. type_check. Qed.

(* OR defined by way of (A ∨ B) = ¬ (¬ A ∧ ¬ B) *)
Definition OR : Box (Qubit ⊗ Qubit) Qubit :=
  box_ ab ⇒ 
    let_ (a,b)       ← output ab;
    gate_ a'         ← X @a;
    gate_ b'         ← X @b;
    let_ z           ← unbox AND (a',b');
    gate_ z'         ← X @z;
    output z'.
Lemma OR_WT : Typed_Box OR.
Proof. type_check. Qed.

(** Invalid Circuits **)
Definition absurd_circ : Box Qubit (Bit ⊗ Qubit) :=
  box_ w ⇒ 
    gate_ x  ← meas @w ;
    gate_ w' ← H @w ;
    output (x,w').
Definition absurd_fail : Typed_Box absurd_circ.
Proof. type_check. Abort.

Definition unmeasure : Box Qubit Qubit :=
  box_ q ⇒ 
    gate_ q ← H @q ;
    gate_ b ← meas @q ;
    output q.
Lemma unmeasure_fail : Typed_Box unmeasure.
Proof. type_check. (* not a very useful end state; it's not clear that it's failing *)
Abort.

Definition unused_qubit : Box Qubit One :=
  box_ w ⇒ 
   gate_ w ← H @w ;
   output ().
Lemma unused_qubit_fail : Typed_Box unused_qubit.
Proof. type_check. Abort.

Definition clone : Box Qubit (Qubit ⊗ Qubit) := box_ p ⇒ (output (p,p)).
Lemma clone_WT : Typed_Box clone.
Proof. type_check. Abort.

(*
Program Definition split_qubit : Box Qubit (Qubit ⊗ Qubit) :=
  box_ w ⇒ 
    let_ (w1,w2)  ← output w ;
    gate_ w2'     ← H @w2 ; 
    output (w1,w2').
Next Obligation. Abort.
*)

Close Scope circ_scope.
(* *)