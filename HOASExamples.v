Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import Contexts.
Require Import HOASCircuits.
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
(*
Program Definition elim_unit {Γ} (p : Pat Γ One) : Γ = ∅ :=
  match p with
  | unit => _
  | qubit _ _ _ => _
  | bit _ _ _ => _
  | pair Γ1 Γ2 Γ W1 W2 v M p1 p2 => _
  end.
*)


(*** Typechecking Tactic ***)

(* Prevent compute from unfolding important fixpoints *)
Open Scope circ_scope.
Opaque wproj.
Opaque merge.
Opaque Ctx.
Opaque is_valid.



(*** Notations ***)

Set Printing Coercions.

(* These tactics construct circuits by calling out to type_check *)


Tactic Notation (at level 0) "make_circ" uconstr(C) := refine C; type_check.

(* Definition I_am_one : nat := ltac:(let x := constr:(2 - 1) in exact x). *)

(* Notation "'bbox' p => C" := ltac:(refine (box (fun Γ p => C)); type_check) (at level 8). *)

Tactic Notation (at level 0) "box_" uconstr(C) := (refine(C); type_check).

Notation letpair p1 p2 p c := (let 'existT23 _ _ p1 p2 _ := wproj p in c).

Notation "p ⇒ C" := (box (fun _ p => C)) (at level 8).
Notation "() ⇒ C" := (box (fun _ _ => C)) (at level 8).
(*Notation "( x , y ) ⇒ C" := (box (fun _ z => letpair x y z C)) (at level 8).*)


(*
Tactic Notation (at level 0) "box_" ident(p) "=>" uconstr(C) := 
    refine (fun p => box C); type_check.
*)

(*
Tactic Notation (at level 0) "box_" uconstr(C) := 
    refine (box (fun _ => C)); type_check.
*)

(* Notations for patterns *)
Notation "()" := unit : circ_scope.
Notation "( x , y , .. , z )" := (pair _ _ _ _ _ _ _ .. (pair _ _ _ _ _ _ _ x y) .. z) (at level 0) : circ_scope.


(* Notations for circuits *)
Notation comp p c1 c2 := (compose c1 (fun _ _ _ _ p => c2)).
Notation "'let_' p ← c1 ; c2" := (comp p c1 c2)
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' () ← c1 ; c2" := 
    (compose c1 (fun _ _ _ _ _ => c2)) 
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( p1 , p2 ) ← c1 ; c2" := 
    (compose c1 (fun _ _ _ _ x => letpair p1 p2 x c2)) 
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( p1 , p2 , p3 ) ← c1 ; c2" :=
    (compose c1 (fun _ _ _ _ x => let 'existT23 _ _ y  p3 _ := wproj x in
                              let 'existT23 _ _ p1 p2 _ := wproj y in
                              c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( ( p1 , p2 ) , p3 ) ← c1 ; c2" := 
    (compose c1 (fun _ _ _ _ x => let 'existT23 _ _ y  p3 _ := wproj x in
                                  let 'existT23 _ _ p1 p2 _ := wproj y in
                                  c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( p1 , ( p2 , p3 ) ) ← c1 ; c2" :=
    (compose c1 (fun _ _ _ _ x => let 'existT23 _ _ p1 y  _ := wproj x in
                                  let 'existT23 _ _ p2 p3 _ := wproj y in
                                  c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( ( p1 , p2 ) , ( p3 , p4 ) ) ← c1 ; c2" :=
    (compose c1 (fun _ _ _ _ x => let 'existT23 _ _ y  z  _ := wproj x in
                                  let 'existT23 _ _ p1 p2 _ := wproj y in
                                  let 'existT23 _ _ p3 p4 _ := wproj z in
                                  c2))
                            (at level 12, right associativity) : circ_scope.


Notation "'gate_' p2 ← g @ p ; c2" := (gate g p (fun _ _ _ _ p2 => c2))
         (at level 12, right associativity).
Notation "'gate_' () ← g @ p ; c2" := (gate g p (fun _ _ _ _ _ => c2))
         (at level 12, right associativity).
Notation "'gate_' ( p1 , p2 ) ← g @ p ; c2" := 
    (gate g p (fun _ _ _ _ x => letpair p1 p2 x c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'gate_' ( p1 , p2 , p3 ) ← g @ p ; c2" :=
    (gate g p (fun _ _ _ _ x => let 'existT23 _ _ y  p3 _ := wproj x in
                                let 'existT23 _ _ p1 p2 _ := wproj y in
                                c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'gate_' ( ( p1 , p2 ) , p3 ) ← g @ p ; c2" := 
    (gate g p (fun _ _ _ _ x => let 'existT23 _ _ y  p3 _ := wproj x in
                                let 'existT23 _ _ p1 p2 _ := wproj y in
                                c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'gate_' ( p1 , ( p2 , p3 ) ) ← g @ p ; c2" :=
    (gate g p (fun _ _ _ _ x => let 'existT23 _ _ p1 y  _ := wproj x in
                                let 'existT23 _ _ p2 p3 _ := wproj y in
                                c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'gate_' ( ( p1 , p2 ) , ( p3 , p4 ) ) ← g @ p ; c2" :=
    (gate g p (fun _ _ _ _ x => let 'existT23 _ _ y  z  _ := wproj x in
                                let 'existT23 _ _ p1 p2 _ := wproj y in
                                let 'existT23 _ _ p3 p4 _ := wproj z in
                                c2))
                            (at level 12, right associativity) : circ_scope.


Notation lift_pat x p c := (lift p (fun x => c)).
Notation "'lift_' x ← c1 ; c2" := (lift_pat x c1 c2) 
         (at level 12, right associativity) : circ_scope.


Definition id_circ {W} : Box W W.
  box_ p ⇒ (output p).
Defined.

Definition boxed_gate {W1 W2} (g : Gate W1 W2) : Box W1 W2.
  box_ p ⇒   
    gate_ p2 ← g @p;
    output p2.
Defined.

Definition new_discard : Box One One.
  box_ () ⇒ 
    gate_ b ← new0 @();
    gate_ () ← discard @b;
    output (). 
Defined.

Definition init_discard : Box One One.
  box_ () ⇒ 
    gate_ q ← init0 @();
    gate_ b ← meas @q;
    gate_ () ← discard @b;
    output (). 
Defined.

Definition hadamard_measure : Box Qubit Bit.
  box_ q ⇒ 
    gate_ q ← H @q;
    gate_ b ← meas @q;
    output b.
Defined.

Definition deutsch (U_f : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)) : Box One Qubit.
  box_ () ⇒ 
    gate_ x ← init0 @();
    gate_ x ← H @x;
    gate_ y ← init1 @();
    gate_ y ← H @y;
    let_ (x,y) ← unbox U_f (x,y);
    gate_ x ← meas @x;
    gate_ x ← discard @x;
    output y.
Defined.

Definition lift_deutsch (U_f : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)) : Box One Qubit.
  box_ () ⇒
    gate_ x    ← init0 @();
    gate_ x    ← H @x;
    gate_ y    ← init1 @();
    gate_ y    ← H @y;
    let_ (x,y) ← unbox U_f (x,y);
    lift_ _    ← x;
    output y.
Defined.



Definition init (b : bool) : Box One Qubit :=
  if b then boxed_gate init1 else boxed_gate init0.

Definition inSeq {W1 W2 W3} (c1 : Box W1 W2) (c2 : Box W2 W3) : Box W1 W3. 
  box_ p1 ⇒ 
    let_ p2 ← unbox c1 p1;
    unbox c2 p2.
Defined.

Definition inPar {W1 W2 W1' W2'} (c1 : Box W1 W1') (c2 : Box W2 W2') 
                                 : Box (W1⊗W2) (W1'⊗W2').
  box_ p12 ⇒ 
    let_ (p1,p2) ← output p12; 
    let_ p1'     ← unbox c1 p1;
    let_ p2'     ← unbox c2 p2; 
    output (p1',p2').
Defined. 

(** Teleport **)

Definition bell00 : Box One (Qubit ⊗ Qubit).
  box_ () ⇒  
    gate_ a ← init0 @();
    gate_ b ← init0 @();
    gate_ a ← H @a;
    gate_ z ← CNOT @(a,b);
    output z.
Defined.

Definition alice : Box (Qubit⊗Qubit) (Bit⊗Bit).
  box_ qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← H @q;
    gate_ x     ← meas @q;
    gate_ y     ← meas @a;
    output (x,y).
Defined.

Definition bob' : Box (Bit ⊗ (Bit ⊗ Qubit)) Qubit.
  box_ (xyb ⇒
    let_  (x,yb)  ← output xyb;
    gate_ (y,b)   ← bit_ctrl σx @yb;
    gate_ (x,b)   ← bit_ctrl σx @(x,b);
    gate_ ()      ← discard @y;
    gate_ ()      ← discard @x;
    output b).
Defined.

Definition bob : Box (Bit⊗Bit⊗Qubit) Qubit.
  box_ xyb ⇒ 
    let_ ((x,y),b) ← output xyb ; 
    gate_ (y,b)  ← bit_ctrl σx @(y,b);
    gate_ (x,b)  ← bit_ctrl σz @(x,b);
    gate_ ()     ← discard @y ;   
    gate_ ()     ← discard @x ;
    output b.
Defined.

Definition teleport' : Box Qubit Qubit.
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    unbox bob' (x,(y,b)).
Defined.

Definition teleport : Box Qubit Qubit.
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    unbox bob (x,y,b).
Defined.

Parameter id_gate: Gate Qubit Qubit.

Definition bob_lift : Box (Bit⊗Bit⊗Qubit) Qubit.
  make_circ ( 
  box (fun _ (xyb : Pat _ (Bit⊗Bit⊗Qubit)) =>
    let_ (xy, b) ← output xyb; 
    lift_ z      ← xy ;
    gate_ b      ← (if snd z then σx else id_gate) @b;
    gate_ b      ← (if fst z then σz else id_gate) @b;
    output b)).
Defined.

Definition bob_lift' : Box (Bit⊗Bit⊗Qubit) Qubit.
  make_circ ( 
  box (fun _ (xyb : Pat _ (Bit⊗Bit⊗Qubit)) =>
    let_ (xy, b) ← output xyb; 
    lift_ z      ← xy ;
    match fst z, snd z with
    | true,  true  => gate_ b ← σx @b; gate_ b ← σz @b; output b
    | true,  false => gate_ b ← σz @b; output b
    | false, true  => gate_ b ← σx @b; output b
    | false, false => output b
    end)).
Defined.

Definition teleport_lift : Box Qubit Qubit.
  box_ q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    unbox bob_lift (x,y,b).
Defined.


(* Right associative Tensor *)
Fixpoint NTensor (n : nat) (W : WType) := 
  match n with 
  | 0    => One
  | 1    => W
  | S n' => W ⊗ NTensor n' W
  end.

Infix "⨂" := NTensor (at level 30). 
(* Transparent Tensor. *)
Opaque NTensor.

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
  | 0    => fun _ => id_circ 
  | S n' => fun _ => box (fun _ w =>
      let_ (c, (q,qs)) ← output w;  
      let_ (c,qs)      ← unbox (rotationsZ m n') (c,qs) ;
      gate_ (c,q)      ← ctrl (RGate (1 + m - n')) @(c,q);
      output (c,(q,qs)))
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
  | 0    => fun _ => boxed_gate H
  | S n' => fun _ => box (fun _ qw =>
             let_ (q,w) ← output qw; 
             let_ w ← unbox (qftZ n') w; 
             unbox (rotationsZ (S n') n') (q,w))
  end (eq_refl n)).
Defined.

Definition qft (n : nat) : Box (n ⨂ Qubit) (n ⨂ Qubit) :=
  match n with 
  | 0 => id_circ
  | S n' => qftZ n'
  end.


(** Coin flip **)

Definition coin_flip : Box One Bit.
  box_ () ⇒
    gate_ q  ← init0 @();
    gate_ q  ← H @q;
    gate_ b  ← meas @q;
    output b.
Defined.


Fixpoint coin_flips (n : nat) : Box One Bit.
  box_ () ⇒
  match n with
  | 0    => gate_ x ← new1 @(); output x
  | S n' => let_  c     ← unbox (coin_flips n') ();
           gate_ q     ← init1 @();
           gate_ (c,q) ← bit_ctrl H @(c,q);
           gate_ ()    ← discard @c;
           gate_ b     ← meas @q;
           output b
  end.
Defined.


Fixpoint coin_flips_lift (n : nat) : Box One Bit. 
  box_ () ⇒ 
  match n with
  | 0    => gate_ q ← new1 @(); output q
  | S n' => let_ q  ← unbox (coin_flips_lift n') ();
           lift_ x ← q;
           if x then unbox coin_flip ()
                else gate_ q ← new0 @(); output q
  end.
Defined.

Definition unitary_transpose {W} (U : Unitary W) : Box W W.
  box_ p ⇒
    gate_ p ← U @p;
    gate_ p ← transpose U @p;
    output p
  .
Defined.

Definition prepare_basis {W} (x : interpret W) : Box One W.
Proof.
  induction W.
  - exact (boxed_gate (if x then init0 else init1)).
  - exact (boxed_gate (if x then new0 else new1)).
  - exact id_circ.
  - box_ (_ ⇒
          let (x1,x2) := x in
          let_ p1 ← unbox (IHW1 x1) ();
          let_ p2 ← unbox (IHW2 x2) ();
          output (p1,p2)).
Defined.

Definition lift_eta W : Box W W.
  box_ q ⇒ 
    lift_ x ← q;
    unbox (prepare_basis x) ().
Defined.

(*
Definition lift_meas : Box Qubit Bit.
  box_ (q ⇒
    lift_ x ← q; _).
  make_circ (
    gate_ p ← (if x then new1 else new0) @();
    output p
  ).
Defined.
*)

(* 
  box_ (q ⇒
    lift_ x ← q;
    gate_ p ← (if x then new1 else new0) @();
    output p
  ).
*)

Definition lift_meas : Box Qubit Bit.
  make_circ (
  box (fun _ (q : Pat _ Qubit) =>
    lift_ x ← q;
    gate_ p ← (if x then new1 else new0) @();
    output p)).
Defined.


(** Classical Gates **)

(* NOT already exists *)

Definition AND : Box (Qubit ⊗ Qubit) (Qubit).
  box_ ab ⇒
    let_ (a,b)      ← output ab;
    gate_ z         ← init0 @();
    gate_ (a,(b,z)) ← T @(a,(b,z));
    gate_ a         ← meas @a;
    gate_ b         ← meas @b;
    gate_ ()        ← discard @a;   
    gate_ ()        ← discard @b;   
    output z.
Defined.

Definition OR : Box (Qubit ⊗ Qubit) (Qubit).
  box_ ab ⇒ 
    let_ (a,b)       ← output ab;
    gate_ a'         ← NOT @a;
    gate_ b'         ← NOT @b;
    let_ z           ← unbox AND (a',b');
    gate_ z'         ← NOT @z;
    output z'.
Defined.

(** Invalid Circuits **)

Definition absurd_circ : Box Qubit (Bit ⊗ Qubit).
  box_ w ⇒ 
    gate_ x  ← meas @w ;
    gate_ w' ← H @w ;
    output (x,w').
Abort.

Definition unused_qubit : Box Qubit One.
  box_ w ⇒ 
   gate_ w ← H @w ;
   output ().
Abort.

Definition clone W : Box W (W ⊗ W).
  box_ p ⇒ (output (p,p)).
Abort.


(* Caught by Coq's typechecker
Definition split_qubit : Box Qubit (Qubit ⊗ Qubit).
  box_ (w ⇒ 
    let_ (w1,w2)  ← output w ;
    gate_ w2'     ← H @w2 ; 
    output (w1,w2')). *)

Close Scope circ_scope.
(* *)
