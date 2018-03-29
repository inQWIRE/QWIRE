Require Import Datatypes.
Require Export TypeChecking.
Require Export HOASLib.
Import ListNotations.
Open Scope list_scope.

Open Scope circ_scope.

(* Example circuits *)

Definition new_discard : Box One One := 
  box_ () ⇒ 
    let_ b ← new0 $();
    discard_ b;
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
  let_ _      ← discard · meas $q; 
  output qs. 
Lemma Deutsch_Jozsa_WT : forall n U__f, Typed_Box U__f -> Typed_Box (Deutsch_Jozsa n U__f).
Proof.
  intros n U__f U_WT.
  induction n.
  + type_check.
  + specialize (inParMany_WT) as WT_Par.
    specialize types_units as WT_units.
    type_check.
    apply WT_Par. 
    all: try apply WT_Par. 
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
    let_ (q,a) ← CNOT $qa;
    let_ x     ← meas · H $q;
    let_ y     ← meas $a;
    output (x,y).
Lemma alice_WT : Typed_Box alice.
Proof. type_check. Qed.

Definition bob : Box (Bit ⊗ Bit ⊗ Qubit) Qubit :=
  box_ xyb ⇒ 
    let_ (x,y,b)   ← id_circ $ xyb ; 
    let_ (y,b)     ← bit_ctrl X $ (y,b);
    let_ (x,b)     ← bit_ctrl Z $ (x,b);
    discard_ (x,y) ;  
    output b.
Lemma bob_WT : Typed_Box bob.
Proof. type_check. Qed.

Definition teleport :=
  box_ q ⇒
    let_ (a,b) ← bell00 $ () ;
    let_ (x,y) ← alice  $ (q,a) ;
    unbox bob (x,y,b).
Lemma teleport_WT : Typed_Box teleport.
Proof. type_check. Defined.

(* Now simplification is quick! *)
Eval cbv in teleport.
Eval cbn in teleport.
Eval simpl in teleport.

Definition bob_lift : Box (Bit ⊗ Bit ⊗ Qubit) Qubit :=
  box_ xyb ⇒
    let_ (x,y,b) ← id_circ $ xyb; 
    lift_ (u,v)  ← (x,y);
    let_ b       ← (if v then X else id_circ) $b;
    let_ b       ← (if u then Z else id_circ) $b;
    output b.
Lemma bob_lift_WT : Typed_Box bob_lift.
Proof. type_check. all: try destruct b0; try destruct b; type_check. Defined. 

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
Proof. type_check. Defined.

Definition teleport_distant : Box Qubit Qubit :=
  box_ q ⇒
    let_ (a,b)  ← unbox bell00 () ;
    let_ (x,y)  ← unbox alice (q,a) ;
    lift_ (u,v) ← (x,y) ;
    unbox (bob_distant u v) b.
Lemma teleport_distant_WT : Typed_Box teleport_distant.
Proof. type_check. Qed.

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
Lemma n_coins_WT : forall n, Typed_Box (n_coins n).
Proof. intros. apply inParMany_WT. apply coin_flip_WT. Qed.

Definition n_coins' (n : nat) : Box One (n ⨂ Bit) := 
  box_ () ⇒ (unbox (inParMany n coin_flip) (units n)).
Lemma n_coins_WT' : forall n, Typed_Box (n_coins' n).
Proof. type_check. apply inParMany_WT. apply coin_flip_WT. apply types_units. Qed.

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
Proof. induction li; type_check. Qed.

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
Proof. type_check. Qed.

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

(* These can't be used in oracles since they're not reversible. *)

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


(***********************)
(** Reversible Gates  **)
(***********************)

(* Apply the f(x,z) = g(x) ⊕ z construction, where g is the classical function 
   and z is an extra target qubit *)

(* This has a more efficient construction where we simply negate z
Definition R_TRUE : Box Qubit Qubit :=
  box_ z ⇒ 
    gate_ x     ← init1 @();
    gate_ (x,z) ← CNOT @(x,z);
    gate_ ()    ← assert1 @x;
    output z.
*)
Definition R_TRUE : Box Qubit Qubit := X.
Lemma R_TRUE_WT : Typed_Box R_TRUE.
Proof. type_check. Qed.

(* This has a more efficient construction: the identity
Definition R_FALSE : Box Qubit Qubit :=
  box_ z ⇒ 
    gate_ x     ← init0 @();
    gate_ (x,z) ← CNOT @(x,z);
    gate_ ()    ← assert0 @x;
    output z.
*)
Definition R_FALSE : Box Qubit Qubit := id_circ.
Lemma R_FALSE_WT : Typed_Box R_FALSE.
Proof. type_check. Qed.

Definition R_NOT : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ xz ⇒ 
    let_ (x,z)      ← output xz;
    gate_ x         ← X @x;
    gate_ (x,z)     ← CNOT @(x,z);
    gate_ x         ← X @x;
    output (x,z).
Lemma R_NOT_WT : Typed_Box R_NOT.
Proof. type_check. Qed.

(* This is with moving onto ancillae - not part of the core R_AND
Definition R_AND : Box (Qubit ⊗ Qubit ⊗ Qubit) (Qubit ⊗ Qubit ⊗ Qubit) :=
  box_ xyz ⇒
    let_ (x,y,z)    ← output xyz;
    gate_ i         ← init0 @();
    gate_ j         ← init0 @();
    gate_ (x,i)     ← CNOT @(x,i);
    gate_ (y,j)     ← CNOT @(y,j);
    gate_ (i,(j,z)) ← CCNOT @(i,(j,z));
    gate_ (y,j)     ← CNOT @(y,j);
    gate_ (x,i)     ← CNOT @(x,i);
    gate_ ()        ← assert0 @j;   
    gate_ ()        ← assert0 @i;   
    output (x,y,z).
Lemma R_AND_WT : Typed_Box R_AND.
Proof. type_check. Qed.
*)

Definition R_AND : Box (Qubit ⊗ Qubit ⊗ Qubit) (Qubit ⊗ Qubit ⊗ Qubit) :=
  box_ xyz ⇒
    let_ (x,y,z)    ← output xyz;
    gate_ (x,(y,z)) ← CCNOT @(x,(y,z));
    output (x,y,z).    
Lemma R_AND_WT : Typed_Box R_AND.
Proof. type_check. Qed.

Definition R_XOR : Box (Qubit ⊗ Qubit ⊗ Qubit) (Qubit ⊗ Qubit ⊗ Qubit) := 
  box_ xyz ⇒
    let_ (x,y,z)    ← output xyz;
    gate_ (x,z)     ← CNOT @(x,z);
    gate_ (y,z)     ← CNOT @(y,z);
    output (x,y,z).
Lemma R_XOR_WT : Typed_Box R_XOR.
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