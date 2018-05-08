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
    (). 
Lemma new_discard_WT : Typed_Box new_discard.
Proof. type_check. Qed.

Definition init_discard : Box One One:= 
  box_ () ⇒ discard $ meas $ init0 $ ().
Lemma init_discard_WT : Typed_Box init_discard.
Proof. type_check. Qed.

Definition hadamard_measure : Box Qubit Bit :=
  box_ q ⇒ meas $ H $ q.
Lemma hadamard_measure_WT : Typed_Box hadamard_measure.
Proof. type_check. Qed.



(*************************************)
(* Variations on Deutsch's Algorithm *)
(*************************************)

Definition U_deutsch (U__f : Unitary (Qubit ⊗ Qubit)) : Box One Bit :=
  box_ () ⇒ 
    let_ x ← init0 $();
    let_ x ← H $x;
    let_ y ← init1 $();
    let_ y ← H $y;
    let_ (x,y) ← U__f $(x,y);
    let_ x ← H $x; (* found through verification! *)
    let_ y ← meas $y;
    let_ () ← discard $y;
    meas $x.

Lemma U_deutsch_WT : forall U__f, Typed_Box (U_deutsch U__f).
Proof. type_check. Qed.

Definition lift_deutsch (U__f : Square_Box (Qubit ⊗ Qubit)) : Box One Bit :=
  box_ () ⇒
    let_ x    ← init0 $();
    let_ x    ← H $x;
    let_ y    ← init1 $();
    let_ y    ← H $y;
    let_ (x,y) ← U__f $ (x,y);
    let_ y    ← meas $y;
    let_ x ← H $x;
    lift_ _    ← y;
    meas $x.
    
Lemma lift_deutsch_WT : forall U__f, Typed_Box U__f -> Typed_Box (lift_deutsch U__f).
Proof. type_check. Qed.

Definition deutsch (U__f : Square_Box (Qubit ⊗ Qubit)) : Box One Bit :=
  box_ () ⇒ 
    let_ x     ← H $ init0 $ ();
    let_ y     ← H $ init1 $ ();
    let_ (x,y) ← U__f $ (x,y);
    let_ _     ← discard $ meas $ y;
    unbox meas x.
Lemma deutsch_WF : forall U__f, Typed_Box U__f -> Typed_Box (deutsch U__f).
Proof. type_check. Qed.

Definition Deutsch_Jozsa (n : nat) (U__f : Square_Box (S n ⨂ Qubit)) : 
  Box One (n ⨂ Bit) := 
  box_ () ⇒
  let_ q      ← H $ init1 $ (); 
  let_ qs     ← ((H · init0) #n) $ (());
  let_ (q,qs) ← U__f $ (q,qs);   
  let_ qs     ← ((meas · H) #n) $ qs;
  let_ _      ← discard $ meas $q; 
  qs. 
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
    let_ a ← H $ init0 $();
    let_ b ← init0 $();
    CNOT $ (a,b).
Lemma bell00_WT : Typed_Box bell00.
Proof. type_check. Qed.

Definition alice : Box (Qubit ⊗ Qubit) (Bit ⊗ Bit) :=
  box_ qa ⇒ 
    let_ (q,a) ← CNOT $qa;
    let_ x     ← meas $ H $q;
    let_ y     ← meas $a;
    (x,y).
Lemma alice_WT : Typed_Box alice.
Proof. type_check. Qed.

Definition bob : Box (Bit ⊗ Bit ⊗ Qubit) Qubit :=
  box_ (x,y,b) ⇒ 
    let_ (y,b)     ← bit_ctrl X $ (y,b);
    let_ (x,b)     ← bit_ctrl Z $ (x,b);
    discard_ (x,y) ;  
    b.
Lemma bob_WT : Typed_Box bob.
Proof. type_check. Qed.

Definition teleport :=
  box_ q ⇒
    let_ (a,b) ← bell00 $ () ;
    let_ (x,y) ← alice  $ (q,a) ;
    bob $ (x,y,b).
Lemma teleport_WT : Typed_Box teleport.
Proof. type_check. Defined.

(* Now simplification is quick! *)
Eval cbv in teleport.
Eval cbn in teleport.
Eval simpl in teleport.


Definition bob_lift : Box (Bit ⊗ Bit ⊗ Qubit) Qubit :=
  box_ (x,y,b) ⇒
    lift_ (u,v)  ← (x,y);
    let_ b       ← (if v then X else id_circ) $b;
    let_ b       ← (if u then Z else id_circ) $b;
    b.
Lemma bob_lift_WT : Typed_Box bob_lift.
Proof. type_check. all: try destruct b0; try destruct b; type_check. Defined. 

Definition bob_lift' := 
  box_ (xy,b) ⇒
    lift_ (u,v)  ← xy;
    match u,v with
    | true,  true  => let_ b ← X $ b; Z $ b
    | true,  false => Z $ b
    | false, true  => X $ b
    | false, false => b
    end.
Lemma bob_lift_WT' : Typed_Box bob_lift'.
Proof. type_check. Defined.

Definition teleport_lift : Box Qubit Qubit :=
  box_ q ⇒
    let_ (a,b) ← bell00 $ () ;
    let_ (x,y) ← alice $ (q,a) ;
    bob_lift $ (x,y,b).
Lemma teleport_lift_WT : Typed_Box teleport_lift.
Proof. type_check. Defined. 

(* teleport lift outside of bob *)
Definition bob_distant (u v : bool) : Box Qubit Qubit :=
  box_ b ⇒
    let_ b ← (if v then X else id_circ) $ b;
    let_ b ← (if u then Z else id_circ) $ b;
    output b.
Lemma bob_distant_WT : forall b1 b2, Typed_Box (bob_distant b1 b2).
Proof. type_check. Defined.

Definition teleport_distant : Box Qubit Qubit :=
  box_ q ⇒
    let_ (a,b)  ← bell00 $ () ;
    let_ (x,y)  ← alice $ (q,a) ;
    lift_ (u,v) ← (x,y) ;
    bob_distant u v $ b.
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
               box_ (c,(q,qs)) ⇒
               let_ (c,qs) ← rotations n' m $ (c,qs);
               let_ (c,q)  ← ctrl (RGate (m + 2 - n')) $ (c,q);
               (c,(q,qs))
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
           | 0 => box_ (q,u) ⇒ (H $ q, u)
           | S n'' => box_ (q,qs) ⇒
                        let_ qs     ← qft n' $ output qs; 
                        let_ (q,qs) ← rotations n'' n' $ (q,qs);
                        (H $ q,qs)
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
  box_ () ⇒ meas $ H $ init0 $ ().
Lemma coin_flip_WT : Typed_Box coin_flip.
Proof. type_check. Qed.

Fixpoint coin_flips (n : nat) : Box One Bit :=
  box_ () ⇒
  match n with
  | 0    => new1 $ ()
  | S n' => let_ c      ← coin_flips n' $ ();
            let_ q      ← init0 $ ();
            let_ (c,q)  ← bit_ctrl H $ (c,q);
            let_ ()     ← discard $ c;
            meas $ q
  end.
Lemma coin_flips_WT : forall n, Typed_Box (coin_flips n).
Proof. intros. induction n; type_check. Qed.

Fixpoint coin_flips_lift (n : nat) : Box One Bit := 
  box_ () ⇒ 
  match n with
  | 0    => new1 $ ()
  | S n' => let_ q  ← coin_flips_lift n' $ ();
            lift_ x ← q;
            if x then coin_flip $ ()
                 else new0 $ ()
  end.
Lemma coin_flips_lift_WT : forall n, Typed_Box (coin_flips_lift n).
Proof. intros. induction n; type_check. Qed.

Definition n_coins (n : nat) : Box (n ⨂ One) (n ⨂ Bit) := inParMany n coin_flip.
Lemma n_coins_WT : forall n, Typed_Box (n_coins n).
Proof. intros. apply inParMany_WT. apply coin_flip_WT. Qed.

Definition n_coins' (n : nat) : Box One (n ⨂ Bit) := 
  box_ () ⇒ inParMany n coin_flip $ (units n).
Lemma n_coins_WT' : forall n, Typed_Box (n_coins' n).
Proof. intros. type_check; try apply types_units; type_check.
  apply inParMany_WT. apply coin_flip_WT. auto.
Qed.


(** Unitary Transpose **)

Definition unitary_transpose {W} (U : Unitary W) : Box W W := 
  box_ p ⇒ transpose U $ U $ p.
Lemma unitary_transpose_WT : forall W (U : Unitary W), Typed_Box (unitary_transpose U).
Proof. type_check. Qed.

(* Produces qubits *)
Fixpoint prepare_basis (li : list bool) : Box One (length li ⨂ Qubit) :=
  match li with
  | []       => id_circ
  | b :: bs  => box_ () ⇒ 
                 let_ p1 ← init b $ (); 
                 let_ p2 ← prepare_basis bs $ ();
                 (p1, p2)
  end.
Lemma prepare_basis_WT : forall li, Typed_Box (prepare_basis li).
Proof. induction li; type_check. Qed.

Fixpoint share n : Box Qubit (S n ⨂ Qubit) :=
  match n with
  | 0    => box (fun q => (q,()))
  | S n' => box_ q ⇒ 
              let_ q'     ← init0 $();
              let_ (q,q') ← CNOT $ (q,q');
              let_ qs     ← share n' $q';
              (q,qs)
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
    if x then new1 $ () else new0 $ ().
Lemma lift_meas_WT : Typed_Box lift_meas.
Proof. type_check. Qed.


(*********************)
(** Classical Gates **)
(*********************)

(* These can't be used in oracles since they're not reversible. *)

(* NOT already exists *)

(* AND uses a Taffoli gate with one ancilla *)
Definition AND : Box (Qubit ⊗ Qubit) Qubit :=
  box_ (a,b) ⇒
    let_ z         ← init0 $ ();
    let_ (a,(b,z)) ← CCNOT $ (a,(b,z));
    let_ a         ← meas $ a;
    let_ b         ← meas $ b;
    let_ ()        ← discard $ a;   
    let_ ()        ← discard $ b;   
    z.
Lemma AND_WT : Typed_Box AND.
Proof. type_check. Qed.

(* XOR just wraps a CNOT *)
Definition XOR : Box (Qubit ⊗ Qubit) Qubit := 
  box_ (a,b) ⇒ 
    let_ (a, b) ← CNOT $(a,b);
    let_ a      ← meas $a;
    let_ ()     ← discard $a;
    b.

Lemma XOR_WT : Typed_Box XOR.
Proof. type_check. Qed.

(* OR defined by way of (A ∨ B) = ¬ (¬ A ∧ ¬ B) *)
Definition OR : Box (Qubit ⊗ Qubit) Qubit :=
  box_ (a,b) ⇒ X $ AND $ (X $ a,X $ b).
Lemma OR_WT : Typed_Box OR.
Proof. type_check. Qed.


(***********************)
(** Reversible Gates  **)
(***********************)



(** Invalid Circuits **)
Definition absurd_circ : Box Qubit (Bit ⊗ Qubit) :=
  box_ w ⇒ 
    let_ x  ← meas $w ;
    let_ w' ← H $w ;
    (x,w').
Definition absurd_fail : Typed_Box absurd_circ.
Proof. type_check. Abort.

Definition unmeasure : Box Qubit Qubit :=
  box_ q ⇒ 
    let_ q ← H $q ;
    let_ b ← meas $q ;
    q.
Lemma unmeasure_fail : Typed_Box unmeasure.
Proof. type_check. (* not a very useful end state; it's not clear that it's failing *)
Abort.

Definition unused_qubit : Box Qubit One :=
  box_ w ⇒ 
   let_ w ← H $w ;
   ().
Lemma unused_qubit_fail : Typed_Box unused_qubit.
Proof. type_check. Abort.

Definition clone : Box Qubit (Qubit ⊗ Qubit) := box_ p ⇒ (p,p).
Lemma clone_WT : Typed_Box clone.
Proof. type_check. Abort.

(*
Program Definition split_qubit : Box Qubit (Qubit ⊗ Qubit) :=
  box_ w ⇒ 
    let_ (w1,w2)  ← output w ;
    let_ w2'     ← H $w2 ; 
    output (w1,w2').
Next Obligation. Abort.
*)

Close Scope circ_scope.

(* *)