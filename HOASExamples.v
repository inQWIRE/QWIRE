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

Definition wproj (p : Pat) : Pat * Pat :=
  match p with
  | unit => (unit, unit)
  | qubit n => (unit, unit)
  | bit n => (unit, unit)
  | pair p1 p2 => (p1, p2)  
  end.

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

Tactic Notation (at level 0) "box_" uconstr(C) := refine(C); type_check.

Notation letpair p1 p2 p c := (let (p1,p2) := wproj p in c).

Notation "p ⇒ C" := (box (fun p => C)) (at level 8).
Notation "() ⇒ C" := (box (fun _ => C)) (at level 8).
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
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) (at level 0) : circ_scope.


(* Notations for circuits *)
Notation comp p c1 c2 := (compose c1 (fun p => c2)).
Notation "'let_' p ← c1 ; c2" := (comp p c1 c2)
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' () ← c1 ; c2" := 
    (compose c1 (fun _ => c2)) 
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( p1 , p2 ) ← c1 ; c2" := 
    (compose c1 (fun x => letpair p1 p2 x c2)) 
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( p1 , p2 , p3 ) ← c1 ; c2" :=
    (compose c1 (fun x => let (y,p3) := wproj x in
                       let (p1,p2) := wproj y in c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( ( p1 , p2 ) , p3 ) ← c1 ; c2" := 
    (compose c1 (fun x => let (y,p3) := wproj x in
                       let (p1,p2) := wproj y in c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( p1 , ( p2 , p3 ) ) ← c1 ; c2" :=
    (compose c1 (fun x => let (p1,y) := wproj x in
                       let (p2,p3) := wproj y in c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'let_' ( ( p1 , p2 ) , ( p3 , p4 ) ) ← c1 ; c2" :=
    (compose c1 (fun x => let (y,z) := wproj x in
                       let (p1, p2) := wproj y in
                       let (p3, p4) := wproj z in c2))
                            (at level 12, right associativity) : circ_scope.


Notation "'gate_' p2 ← g @ p ; c2" := (gate g p (fun p2 => c2))
         (at level 12, right associativity).
Notation "'gate_' () ← g @ p ; c2" := (gate g p (fun _ => c2))
         (at level 12, right associativity).
Notation "'gate_' ( p1 , p2 ) ← g @ p ; c2" := 
    (gate g p (fun x => letpair p1 p2 x c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'gate_' ( p1 , p2 , p3 ) ← g @ p ; c2" :=
    (gate g p (fun x => let (y, p3) := wproj x in
                     let (p1, p2) := wproj y in c2))
                           (at level 12, right associativity) : circ_scope.
Notation "'gate_' ( ( p1 , p2 ) , p3 ) ← g @ p ; c2" := 
    (gate g p (fun x => let (y, p3) := wproj x in
                     let (p1, p2) := wproj y in c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'gate_' ( p1 , ( p2 , p3 ) ) ← g @ p ; c2" :=
    (gate g p (fun x => let (p1, y) := wproj x in
                     let (p2, p3) := wproj y in c2))
                            (at level 12, right associativity) : circ_scope.
Notation "'gate_' ( ( p1 , p2 ) , ( p3 , p4 ) ) ← g @ p ; c2" :=
    (gate g p (fun x => let (y, z) := wproj x in
                     let (p1, p2) := wproj y in
                     let (p3, p4) := wproj z in c2))
                            (at level 12, right associativity) : circ_scope.

Notation lift_pat x p c := (lift p (fun x => c)).
Notation "'lift_' x ← c1 ; c2" := (lift_pat x c1 c2) 
         (at level 12, right associativity) : circ_scope.


(* Alt def. of WellTypedness
Definition WT (b : Box) (W1 W2 : WType) :=
*)   

Definition id_circ : Box :=
  p ⇒ (output p).

Definition id_circ_t : forall W, Typed_Box id_circ W W.
  unfold Typed_Box, id_circ.
  simpl.
  intros.
  econstructor; trivial.
Defined.

Definition boxed_gate {W1 W2} (g : Gate W1 W2) : Box := 
  p ⇒   
    gate_ p2 ← g @p;
    output p2.

Definition boxed_gate_t {W1 W2} (g : Gate W1 W2) : Typed_Box (boxed_gate g) W1 W2.
  unfold Typed_Box, boxed_gate; simpl; intros.
  econstructor; trivial.
  eapply pat_ctx_valid.
  apply H.
  2: apply H.
  rewrite merge_nil_r; reflexivity.
  intros.
  econstructor.
  reflexivity.
  subst.
  rewrite merge_nil_r. 
  assumption.
Defined.

Definition new_discard : Box := 
  () ⇒ 
    gate_ b ← new0 @();
    gate_ () ← discard @b;
    output (). 

Definition new_discard_t : Typed_Box new_discard One One.
  unfold Typed_Box, boxed_gate; simpl; intros.
  inversion H; subst.
  econstructor.
  apply valid_empty.
  rewrite merge_nil_l. reflexivity.
  assumption.
  intros.
  econstructor.
  assumption.
  2: apply H0.
  apply m2.
  intros.
  econstructor.
  reflexivity.
  inversion H1; subst.
  constructor.
Defined.

Definition init_discard : Box := 
  () ⇒ 
    gate_ q ← init0 @();
    gate_ b ← meas @q;
    gate_ () ← discard @b;
    output (). 

Definition hadamard_measure : Box :=
  q ⇒ 
    gate_ q ← H @q;
    gate_ b ← meas @q;
    output b.

Definition deutsch (U_f : Box) : Box :=
  () ⇒ 
    gate_ x ← init0 @();
    gate_ x ← H @x;
    gate_ y ← init1 @();
    gate_ y ← H @y;
    let_ (x,y) ← unbox U_f (x,y);
    gate_ x ← meas @x;
    gate_ x ← discard @x;
    output y.

Definition lift_deutsch (U_f : Box) : Box :=
  () ⇒
    gate_ x    ← init0 @();
    gate_ x    ← H @x;
    gate_ y    ← init1 @();
    gate_ y    ← H @y;
    let_ (x,y) ← unbox U_f (x,y);
    lift_ _    ← x;
    output y.

Definition init (b : bool) : Box :=
  if b then boxed_gate init1 else boxed_gate init0.

Definition inSeq (c1 c2 : Box) : Box :=
  p1 ⇒ 
    let_ p2 ← unbox c1 p1;
    unbox c2 p2.

Definition inPar (c1 c2 : Box) : Box :=
  p12 ⇒ 
    let_ (p1,p2) ← output p12; 
    let_ p1'     ← unbox c1 p1;
    let_ p2'     ← unbox c2 p2; 
    output (p1',p2').

(** Teleport **)

Definition bell00 : Box :=
  () ⇒  
    gate_ a ← init0 @();
    gate_ b ← init0 @();
    gate_ a ← H @a;
    gate_ z ← CNOT @(a,b);
    output z.

Definition alice : Box :=
  qa ⇒ 
    gate_ (q,a) ← CNOT @qa;
    gate_ q     ← H @q;
    gate_ x     ← meas @q;
    gate_ y     ← meas @a;
    output (x,y).

Definition bob' : Box :=
  xyb ⇒
    let_  (x,yb)  ← output xyb;
    gate_ (y,b)   ← bit_ctrl σx @yb;
    gate_ (x,b)   ← bit_ctrl σx @(x,b);
    gate_ ()      ← discard @y;
    gate_ ()      ← discard @x;
    output b.

Definition bob : Box :=
  xyb ⇒ 
    let_ ((x,y),b) ← output xyb ; 
    gate_ (y,b)  ← bit_ctrl σx @(y,b);
    gate_ (x,b)  ← bit_ctrl σz @(x,b);
    gate_ ()     ← discard @y ;   
    gate_ ()     ← discard @x ;
    output b.

Definition teleport' :=
  q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    unbox bob' (x,(y,b)).

Definition teleport :=
  q ⇒
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
(*  compute. *)
  eauto.
Qed.

Parameter id_gate: Gate Qubit Qubit.

(* Hmmm... now this becomes tricky since untyped z should be a boolean pair... 
   Unsafe coercion time! *)
Definition toBoolPair (b : bools) : bool * bool :=
  match b with
  | TT (BT l) (BT r) => Datatypes.pair l r
  | _                => Datatypes.pair false false
  end.

Definition bob_lift : Box :=
  xyb ⇒
    let_ (xy, b) ← output xyb; 
    lift_ z      ← xy ;
    gate_ b      ← (if snd (toBoolPair z) then σx else id_gate) @b;
    gate_ b      ← (if fst (toBoolPair z) then σz else id_gate) @b;
    output b.

Definition bob_lift' := 
  xyb ⇒
    let_ (xy, b) ← output xyb; 
    lift_ z      ← xy ;
    let z := toBoolPair z in 
    match fst z, snd z with
    | true,  true  => gate_ b ← σx @b; gate_ b ← σz @b; output b
    | true,  false => gate_ b ← σz @b; output b
    | false, true  => gate_ b ← σx @b; output b
    | false, false => output b
    end.

Definition teleport_lift : Box :=
  q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    unbox bob_lift (x,y,b).

(* teleport lift outside of bob *)
Definition bob_distant (z : bool * bool) : Box :=
  b ⇒
    gate_ b      ← (if snd z then σx else id_gate) @b;
    gate_ b      ← (if fst z then σz else id_gate) @b;
    output b.

Definition teleport_distant : Box :=
  q ⇒
    let_ (a,b) ← unbox bell00 () ;
    let_ (x,y) ← unbox alice (q,a) ;
    lift_ xy ← (x,y) ;
    (let z := toBoolPair xy in unbox (bob_distant z) () ).

Definition teleport_direct :=
  q ⇒  
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
    gate_ (y,b)  ← bit_ctrl σx @(y,b);
    gate_ (x,b)  ← bit_ctrl σz @(x,b);
    gate_ ()     ← discard @y;   
    gate_ ()     ← discard @x;
    output b.

Lemma teleport_eq : teleport = teleport_direct.
Proof.
  unfold teleport, teleport_direct.
  simpl.
  repeat (f_equal; apply functional_extensionality; intros).
  destruct x3; simpl.
Admitted.  

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

Fixpoint inSeqMany (n :nat) (c : Box) : Box := 
  match n with
  | 0 => id_circ
  | 1 => c
  | S n' => inSeq c (inSeqMany n' c)
  end.

(* Zero-indexed variant. I don't know why this is necessary *)
(* This will be fairly common *)
Fixpoint inParManyZ (n : nat) (c : Box) {struct n} : Box :=
  match n with 
  | 0 => c
  | S n' => inPar c (inParManyZ n' c)
  end. 

Definition inParMany (n : nat) (c : Box) : Box := 
  match n with 
  | 0 => id_circ
  | S n' => inParManyZ n' c 
  end.


(** Quantum Fourier Transform **)

Parameter RGate : nat -> Unitary Qubit.

Fixpoint rotationsZ (m n : nat) : Box :=
  match n with 
  | 0    => id_circ 
  | S n' => w ⇒
             let_ (c, (q,qs)) ← output w;  
             let_ (c,qs)      ← unbox (rotationsZ m n') (c,qs) ;
             gate_ (c,q)      ← ctrl (RGate (1 + m - n')) @(c,q);
             output (c,(q,qs))
   end.

Definition rotations (m n : nat) : Box :=
  match n with 
  | 0 => id_circ
  | S n' => rotationsZ m n' 
  end.

Fixpoint qftZ (n : nat) : Box :=
  match n with 
  | 0    => boxed_gate H
  | S n' => qw ⇒
             let_ (q,w) ← output qw; 
             let_ w ← unbox (qftZ n') w; 
             unbox (rotationsZ (S n') n') (q,w)
  end.

Definition qft (n : nat) : Box :=
  match n with 
  | 0 => id_circ
  | S n' => qftZ n'
  end.


(** Coin flip **)

Definition coin_flip : Box :=
  () ⇒
    gate_ q  ← init0 @();
    gate_ q  ← H @q;
    gate_ b  ← meas @q;
    output b.

Fixpoint coin_flips (n : nat) : Box :=
  () ⇒
  match n with
  | 0    => gate_ x ← new1 @(); output x
  | S n' => let_  c     ← unbox (coin_flips n') ();
           gate_ q     ← init1 @();
           gate_ (c,q) ← bit_ctrl H @(c,q);
           gate_ ()    ← discard @c;
           gate_ b     ← meas @q;
           output b
  end.

Definition toBool (b : bools) : bool :=
  match b with
  | BT b => b
  | _    => false
  end.

Fixpoint coin_flips_lift (n : nat) : Box := 
  () ⇒ 
  match n with
  | 0    => gate_ q ← new1 @(); output q
  | S n' => let_ q  ← unbox (coin_flips_lift n') ();
           lift_ x ← q;
           if toBool x then unbox coin_flip ()
                else gate_ q ← new0 @(); output q
  end.

Definition unitary_transpose {W} (U : Unitary W) : Box := 
  p ⇒
    gate_ p ← U @p;
    gate_ p ← transpose U @p;
    output p
  .

(* Produces qubits *)
Fixpoint prepare_basis (x : bools) : Box :=
  match x with
  | UT => id_circ
  | BT b => init b
  | TT x1 x2 => () ⇒
                  let_ p1 ← unbox (prepare_basis x1) ();
                  let_ p2 ← unbox (prepare_basis x2) (); 
                  output (p1, p2)
  end.

Definition lift_eta : Box :=
  q ⇒ 
    lift_ x ← q;
    unbox (prepare_basis x) ().

Definition lift_meas : Box :=
  q ⇒
    lift_ x ← q;
    gate_ p ← (if toBool x then new1 else new0) @();
    output p.


(** Classical Gates **)

(* NOT already exists *)

Definition AND : Box :=
  ab ⇒
    let_ (a,b)      ← output ab;
    gate_ z         ← init0 @();
    gate_ (a,(b,z)) ← T @(a,(b,z));
    gate_ a         ← meas @a;
    gate_ b         ← meas @b;
    gate_ ()        ← discard @a;   
    gate_ ()        ← discard @b;   
    output z.

Definition OR : Box :=
  ab ⇒ 
    let_ (a,b)       ← output ab;
    gate_ a'         ← NOT @a;
    gate_ b'         ← NOT @b;
    let_ z           ← unbox AND (a',b');
    gate_ z'         ← NOT @z;
    output z'.


(** Invalid Circuits **)
(* Now can be defined but won't typecheck *)
Definition absurd_circ : Box :=
  w ⇒ 
    gate_ x  ← meas @w ;
    gate_ w' ← H @w ;
    output (x,w').

Definition unmeasure : Box :=
  q ⇒ 
    gate_ q  ← H @q ;
    gate_ b ← meas @q ;
    output q.

Definition unused_qubit : Box :=
  w ⇒ 
   gate_ w ← H @w ;
   output ().

Definition clone : Box := p ⇒ (output (p,p)).

Definition split_qubit : Box :=
  w ⇒ 
    let_ (w1,w2)  ← output w ;
    gate_ w2'     ← H @w2 ; 
    output (w1,w2').

Close Scope circ_scope.
(* *)