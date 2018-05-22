Require Import Datatypes.
Require Export TypeChecking.
Import ListNotations.
Open Scope list_scope.
Open Scope circ_scope.
 
(** Projecting out elements of tensors **)

Open Scope circ_scope.
Definition wproj {W1 W2} (p : Pat (W1 ⊗ W2)) : Pat W1 * Pat W2 :=
  match p with
  | pair p1 p2 => (p1, p2)  
  end.

Definition boxed_gate {W1 W2} (g : Gate W1 W2) : Box W1 W2 := 
  box_ p ⇒ 
    gate_ p2 ← g @ p;
    output p2.
Lemma boxed_gate_WT {W1 W2} (g : Gate W1 W2) : Typed_Box (boxed_gate g).
Proof. type_check. Qed.
Coercion boxed_gate : Gate >-> Box.

Definition apply_box {w1 w2} (b : Box w1 w2) (c : Circuit w1) : Circuit w2 :=
  let_ x ← c;
  unbox b x.
Notation "b $ c" := (apply_box b c)  (right associativity, at level 10) : circ_scope.
Coercion output : Pat >-> Circuit.

Fixpoint lift_circ {W W' : WType} (c0 : Circuit W) (c : interpret W -> Circuit W') {struct W} : Circuit W'. 
  induction W.
  + exact (compose (meas $ c0) (fun p => lift p c)).
  + exact (compose c0 (fun p => lift p c)).
  + exact (compose c0 (fun _ => c tt)). 
  + simpl in c.
    pose (c' := (curry c)).
    exact (compose c0 (fun p => letpair p1 p2 p 
                     (lift_circ W1 W' p1 (fun x1 => lift_circ W2 W' p2 (c' x1))))).
Defined.

(* One bit/qubit version that the Coq typechecker can deal with *)
Program Definition lift_wire {W W' : WType} (c0 : Circuit W) (c : bool -> Circuit W')
  : Circuit W' :=
  match W with 
  | Bit   => compose c0 (fun p => lift p c)
  | Qubit => compose (meas $ c0) (fun p => lift p c)
  | One   => c true (* invalid case *)
  | Tensor W1 W2 => c true  (* invalid case *)
  end.

(*** Notations ***)

Set Printing Coercions.

Notation letpair p1 p2 p c := (let (p1,p2) := wproj p in c).

Notation "'box_' p ⇒ C" := (box (fun p => C)) 
    (at level 11) : circ_scope.
Notation "'box_' () ⇒ C" := (box (fun _ => C)) 
    (at level 11) : circ_scope.
Notation "'box_' ( p1 , p2 ) ⇒ C" := (box (fun p => letpair p1 p2 p C)) 
    (at level 11) : circ_scope.
Notation "'box_' ( p1 , p2 , p3 ) ⇒ C" := (box (fun p =>
    let (y,p3) := wproj p in
    let (p1,p2) := wproj y in C)) 
    (at level 11) : circ_scope.
Notation "'box_' ( p1 , ( p2 , p3 ) ) ⇒ C" := (box (fun x =>
    let (p1,y) := wproj x in
    let (p2,p3) := wproj y in C)) 
    (at level 11) : circ_scope.
Notation "'box_' ( ( p1 , p2 ) , ( p3 , p4 ) ) ⇒ C" := (box (fun x =>
    let (y,z) := wproj x in
    let (p1,p2) := wproj y in
    let (p3,p4) := wproj z in
    C)) 
    (at level 11) : circ_scope.

(* Notations for patterns *)
Notation "()" := unit : circ_scope.
(*Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) (at level 0) : circ_scope.*)


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
Notation "'let_' ( p1 , ( p2 , ( p3 , ( p4 , ( p5 , p6 ) ) ) ) ) ← c1 ; c2" :=
    (compose c1 (fun x => let (p1,y) := wproj x in
                       let (p2,z) := wproj y in
                       let (p3,a) := wproj z in
                       let (p4,b) := wproj a in
                       let (p5,p6) := wproj b in c2))
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
Notation "'gate_' ( p1 , ( p2 , ( p3 , ( p4 , ( p5 , p6 ) ) ) ) ) ← g @ p ; c2" :=
    (gate g p (fun x => let (p1,y) := wproj x in
                       let (p2,z) := wproj y in
                       let (p3,a) := wproj z in
                       let (p4,b) := wproj a in
                       let (p5,p6) := wproj b in c2))
                            (at level 12, right associativity) : circ_scope.

Notation "'discard_' p ; c" := (gate discard p (fun _ => c))
         (at level 12, right associativity) : circ_scope.
Notation "'discard_' ( p1 , p2 ) ; c" := (gate discard p1 (fun _ => gate discard p2 
                                                                      (fun _ => c)))
         (at level 12, right associativity) : circ_scope.
Notation "'discard_' ( p1 , p2 , p3 ) ; c" := (gate discard p1 
                                                 (fun _ => gate discard p2 
                                                   (fun _ => gate discard p3 
                                                     (fun _ => c))))
         (at level 12, right associativity) : circ_scope.
Notation "'discard_' ( ( p1 , p2 ) , p3 ) ; c" := (gate discard p1 
                                                 (fun _ => gate discard p2 
                                                   (fun _ => gate discard p3 
                                                     (fun _ => c))))
         (at level 12, right associativity) : circ_scope.
Notation "'discard_' ( p1 , ( p2 , p3 ) ) ; c" := (gate discard p1 
                                                 (fun _ => gate discard p2 
                                                   (fun _ => gate discard p3 
                                                     (fun _ => c))))
         (at level 12, right associativity) : circ_scope.
Notation "'discard_' ( ( p1 , p2 ) , ( p3 , p4 ) ) ; c" :=
  (gate discard p1 
        (fun _ => gate discard p2 
                    (fun _ => gate discard p3 
                                (fun _ => gate discard p4 
                                            (fun _ => c)))))
         (at level 12, right associativity) : circ_scope.
Notation "'discard_' ( p1 , ( p2 , ( p3 , ( p4 , ( p5 , p6 ) ) ) ) ) ; c" :=
    (gate discard p1 (fun _ => gate discard p2 
                      (fun _ => gate discard p3
                      (fun _ => gate discard p4
                      (fun _ => gate discard p5
                      (fun _ => gate discard p6))))))
                            (at level 12, right associativity) : circ_scope.


Notation "'lift_' x ← c0 ; c" := (lift_wire c0 (fun x => c))
         (at level 12, right associativity) : circ_scope.

Notation "'lift_' ( x , y ) ← c0 ; c" := (compose c0 (fun p => 
            letpair p1 p2 p (lift_wire p1 (fun x => lift_wire p2 (fun y => c)))))
         (at level 12, right associativity) : circ_scope.

(* 
Notation "'lift_' x ← c0 ; c" := (lift_circ c0 (fun x => c))
         (at level 12, right associativity) : circ_scope.

Notation "'lift_' ( x , y ) ← c0 ; c" := (lift_circ c0 (fun p => let (x,y) := p in c))
         (at level 12, right associativity) : circ_scope.
*)


(***********************)
(* Structural circuits *)
(***********************)


Definition id_circ {W} : Box W W :=
  box_ p ⇒ (output p).
Lemma id_circ_WT : forall W, Typed_Box (@id_circ W).
Proof. type_check. Qed.


Definition SWAP : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) := 
  box_ p ⇒ let_ (p1,p2) ← p; (p2,p1).
Lemma WT_SWAP : Typed_Box SWAP. Proof. type_check. Qed.


Definition new (b : bool) : Box One Bit := if b then new1 else new0.
Lemma new_WT : forall b, Typed_Box (new b).
Proof. destruct b; type_check. Defined.

Definition init (b : bool) : Box One Qubit := if b then init1 else init0.
Lemma init_WT : forall b, Typed_Box (init b).
Proof. destruct b; type_check. Defined.

Definition assert (b : bool) : Box Qubit One := if b then assert1 else assert0.
Lemma assert_WT : forall b, Typed_Box (assert b). Proof. type_check. Qed.

Definition inSeq {w1 w2 w3} (c1 : Box w1 w2) (c2 : Box w2 w3): Box w1 w3 :=
  box_ p1 ⇒ 
    let_ p2 ← unbox c1 p1;
    unbox c2 p2.

Lemma inSeq_WT : forall W1 W2 W3 (c1 : Box W1 W2) (c2 : Box W2 W3), 
                 Typed_Box c1 -> Typed_Box c2 -> Typed_Box (inSeq c1 c2).
Proof. type_check. Qed.

Definition inPar {w1 w2 w1' w2'} 
                 (c1 : Box w1 w2) (c2 : Box w1' w2') : Box (w1 ⊗ w1') (w2 ⊗ w2'):=
  box_ p12 ⇒ 
    let_ (p1,p2) ← output p12; 
    let_ p1'     ← unbox c1 p1;
    let_ p2'     ← unbox c2 p2; 
    (p1',p2').

Lemma inPar_WT : forall W1 W1' W2 W2' (c1 : Box W1 W2) (c2 : Box W1' W2'), 
  Typed_Box c1 -> Typed_Box c2 ->
  Typed_Box (inPar c1 c2).
Proof. type_check. Qed.

Fixpoint units (n : nat) : Pat (n ⨂ One) := 
  match n with
  | O => unit
  | S n' => pair unit (units n')
  end. 
Lemma types_units : forall n, Types_Pat ∅ (units n).
Proof. induction n; type_check. Qed.

(* Can also just use (init b) #n $ (()) *)
Fixpoint initMany (b : bool) (n : nat) : Box One (n ⨂ Qubit):= 
  match n with 
  | 0    => id_circ
  | S n' => box_ () ⇒ 
           let_ q  ← unbox (init b) ();
           let_ qs ← unbox (initMany b n') ();
           (q, qs)
  end.
Lemma initMany_WT : forall b n, Typed_Box (initMany b n).
Proof. induction n; type_check. Qed.

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

(* Parallel binds more closely than sequence *)
Notation "b1 ∥ b2" := (inPar b1 b2) (at level 52, right associativity) : circ_scope.
Notation "b' · b" := (inSeq b b') (at level 60, right associativity) : circ_scope.
Notation "c1 ;; c2" := (inSeq c1 c2) (at level 60, right associativity) : circ_scope.

Notation "(())" := (units _) (at level 0) : circ_scope.
Notation "g # n" := (inParMany n g) (at level 40) : circ_scope.

Hint Resolve types_units id_circ_WT boxed_gate_WT init_WT inSeq_WT inPar_WT 
     initMany_WT inSeqMany_WT inParMany_WT : typed_db.

(*********************)
(** Classical Gates **)
(*********************)

(* These can't be used in oracles since they're not reversible. *)

(* NOT already exists *)

Definition CL_AND : Box (Qubit ⊗ Qubit) Qubit :=
  box_ ab ⇒
    let_ (a,b)      ← output ab;
    let_ z         ← init0 $ ();
    let_ (a,(b,z)) ← CCNOT $ (a,(b,z));
    let_ a         ← meas $ a;
    let_ b         ← meas $ b;
    let_ ()        ← discard $ a;   
    let_ ()        ← discard $ b;   
    z.
Lemma CL_AND_WT : Typed_Box CL_AND.
Proof. type_check. Qed.

Definition CL_XOR : Box (Qubit ⊗ Qubit) Qubit := 
  box_ (a,b) ⇒ 
    let_ (a, b) ← CNOT $ (a,b);
    let_ a      ← meas $ a;
    let_ ()     ← discard $ a;
    b.
Lemma CL_XOR_WT : Typed_Box CL_XOR.
Proof. type_check. Qed.

Definition CL_OR : Box (Qubit ⊗ Qubit) Qubit :=
  box_ (a,b) ⇒ 
    let_ a'         ← X $a;
    let_ b'         ← X $b;
    let_ z          ← CL_AND $ (a',b');
    X $z.
Lemma CL_OR_WT : Typed_Box CL_OR.
Proof. type_check. Qed.


(***********************)
(** Reversible Gates  **)
(***********************)

(* Apply the f(x,z) = g(x) ⊕ z construction, where g is the classical function 
   and z is an extra target qubit *)

(* This has a more efficient construction where we simply negate z
Definition TRUE : Box Qubit Qubit :=
  box_ z ⇒ 
    let_ x     ← init1 $();
    let_ (x,z) ← CNOT $(x,z);
    let_ ()    ← assert1 $x;
    output z.
*)
Definition TRUE : Box Qubit Qubit := X.
Lemma TRUE_WT : Typed_Box TRUE.
Proof. type_check. Qed.

(* This has a more efficient construction: the identity
Definition FALSE : Box Qubit Qubit :=
  box_ z ⇒ 
    let_ x     ← init0 $();
    let_ (x,z) ← CNOT $(x,z);
    let_ ()    ← assert0 $x;
    output z.
*)
Definition FALSE : Box Qubit Qubit := id_circ.
Lemma FALSE_WT : Typed_Box FALSE.
Proof. type_check. Qed.

Definition NOT : Box (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ (x,z) ⇒ 
    let_ x         ← X $x;
    let_ (x,z)     ← CNOT $(x,z);
    let_ x         ← X $x;
    (x,z).
Lemma NOT_WT : Typed_Box NOT.
Proof. type_check. Qed.

Definition AND : Box (Qubit ⊗ Qubit ⊗ Qubit) (Qubit ⊗ Qubit ⊗ Qubit) :=
  box_ xyz ⇒
    let_ (x,y,z)    ← output xyz;
    let_ (x,(y,z)) ← CCNOT $(x,(y,z));
    (x,y,z).    
Lemma AND_WT : Typed_Box AND.
Proof. type_check. Qed.

Definition XOR : Box (Qubit ⊗ Qubit ⊗ Qubit) (Qubit ⊗ Qubit ⊗ Qubit) := 
  box_ xyz ⇒
    let_ (x,y,z)    ← output xyz;
    let_ (x,z)     ← CNOT $(x,z);
    let_ (y,z)     ← CNOT $(y,z);
    (x,y,z).
Lemma XOR_WT : Typed_Box XOR.
Proof. type_check. Qed.

