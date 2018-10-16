Require Import Datatypes.
Require Export TypeChecking.
Import ListNotations.
Open Scope list_scope.
Open Scope circ_scope.
 

Definition boxed_gate {Var} {W1 W2} (g : Gate W1 W2) : Box Var W1 W2 := 
  box_ p ⇒ 
    gate_ p2 ← g @ p;
    output p2.
Lemma boxed_gate_WT {Var} {W1 W2} (g : Gate W1 W2) : Typed_Box Var (boxed_gate g).
Proof. type_check. Qed.
Coercion boxed_gate : Gate >-> Box.
(* FIXME: this coercion isn't working. For now using notation \lceil - \rceil *)
Notation "⌈ g ⌉" := (boxed_gate g) (at level 10).

Lemma types_circuit_valid : forall Var w (c : Circuit Var w) Γ,
      Γ ⊢ c :Circ -> is_valid Γ.
Proof.
  intros Var w c Γ pf_c.
  induction pf_c.
  - subst. eapply pat_ctx_valid; eauto.
  - destruct pf1. subst. auto.
  - destruct pf. subst. auto.
Qed.

Definition apply_box {Var} {w1 w2} (b : Box Var w1 w2) (c : Circuit Var w1) : Circuit Var w2 :=
  let_ x ← c;
  unbox b x.


Notation "b $ c" := (apply_box b c) (right associativity, at level 12) : circ_scope.

Coercion output : Pat >-> Circuit.
Lemma apply_box_WT : forall Var w1 w2 (b : Box Var w1 w2) (c : Circuit Var w1) Γ,
      Typed_Box Var b -> Γ ⊢ c :Circ -> Γ ⊢ apply_box b c :Circ.
Proof.
  intros Var w1 w2 b c Γ pf_b pf_c.
  type_check; [| solve_merge; eapply types_circuit_valid; eauto].
  apply unbox_typing; auto.
  type_check.
Qed.



(* Should move other notations in Typechecking *)

(* 
Program Fixpoint lift_circ {W W' : WType} (c0 : Circuit W) (c : interpret W -> Circuit W') {struct W} : Circuit W' :=
  match W with 
  | Bit   => compose c0 (fun p => lift p c)
  | Qubit => compose (meas $ c0) (fun p => lift p c)
  | One   => compose c0 (fun _ => c tt) 
  | Tensor W1 W2 => let c' := (curry c) in 
                   compose c0 (fun p => letpair p1 p2 p 
                     (lift_circ W1 W' p1 (fun x1 => lift_circ W2 W' p2 (c' x1))))
  end.
*)

Fixpoint lift_circ {Var} {W W' : WType} 
         (c0 : Circuit Var W) 
         (c : interpret W -> Circuit Var W') {struct W} : Circuit Var W'. 
  induction W.
  + exact (compose (⌈meas⌉ $ c0) (fun p => lift p c)).
  + exact (compose c0 (fun p => lift p c)).
  + exact (compose c0 (fun _ => c tt)). 
  + simpl in c.
    pose (c' := (curry c)).
    exact (compose c0 (fun p => letpair p1 p2 p 
                     (lift_circ _ W1 W' p1 (fun x1 => lift_circ _ W2 W' p2 (c' x1))))).
Defined.

(* One bit/qubit version that the Coq typechecker can deal with *)
Program Definition lift_wire {Var} {W W' : WType} (c0 : Circuit Var W) (c : bool -> Circuit Var W')
  : Circuit Var W' :=
  match W with 
  | Bit   => compose c0 (fun p => lift p c)
  | Qubit => compose (⌈meas⌉ $ c0) (fun p => lift p c)
  | One   => c true (* invalid case *)
  | Tensor W1 W2 => c true  (* invalid case *)
  end.

Notation "'lift_' x ← c0 ; c" := (lift_wire c0 (fun x => c))
         (at level 14, right associativity) : circ_scope.

Notation "'lift_' ( x , y ) ← c0 ; c" := (compose c0 (fun p => 
            letpair p1 p2 p (lift_wire p1 (fun x => lift_wire p2 (fun y => c)))))
         (at level 14, right associativity) : circ_scope.

(* 
Notation "'lift_' x ← c0 ; c" := (lift_circ c0 (fun x => c))
         (at level 14, right associativity) : circ_scope.

Notation "'lift_' ( x , y ) ← c0 ; c" := (lift_circ c0 (fun p => let (x,y) := p in c))
         (at level 14, right associativity) : circ_scope.
*)


(***********************)
(* Structural circuits *)
(***********************)

Section struct_circs.

Context {Var : Set}.

Definition id_circ {W} : Box Var W W :=
  box_ p ⇒ (output p).
Lemma id_circ_WT : forall W, Typed_Box Var (@id_circ W).
Proof. type_check. Qed.

Definition SWAP : Box Var (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) := 
  box_ p ⇒ let_ (p1,p2) ← p; (p2,p1).
Lemma WT_SWAP : Typed_Box Var SWAP. 
Proof. type_check. Qed.


Definition new (b : bool) : Box Var One Bit := if b then ⌈new1⌉ else ⌈new0⌉.
Lemma new_WT : forall b, Typed_Box Var (new b).
Proof. destruct b; type_check. Defined.

Definition init (b : bool) : Box Var One Qubit := if b then boxed_gate init1 else boxed_gate init0.
Lemma init_WT : forall b, Typed_Box Var (init b).
Proof. destruct b; type_check. Defined.

Definition assert (b : bool) : Box Var Qubit One := if b then boxed_gate assert1 else boxed_gate assert0.
Lemma assert_WT : forall b, Typed_Box Var (assert b). Proof. type_check. Qed.

Definition inSeq {w1 w2 w3} (c1 : Box Var w1 w2) (c2 : Box Var w2 w3): Box Var w1 w3 :=
  box_ p1 ⇒ 
    let_ p2 ← unbox c1 p1;
    unbox c2 p2.

Lemma inSeq_WT : forall W1 W2 W3 (c1 : Box Var W1 W2) (c2 : Box Var W2 W3), 
                 Typed_Box Var c1 -> Typed_Box Var c2 -> Typed_Box Var (inSeq c1 c2).
Proof. type_check. Qed.

Definition inPar {w1 w2 w1' w2'} 
                 (c1 : Box Var w1 w2) (c2 : Box Var w1' w2') : Box Var (w1 ⊗ w1') (w2 ⊗ w2'):=
  box_ p12 ⇒ 
    let_ (p1,p2) ← output p12; 
    let_ p1'     ← unbox c1 p1;
    let_ p2'     ← unbox c2 p2; 
    (p1',p2').

(* Idealized inPar 

Unset Printing Notations.

Print inPar.
Print inSeq.

⟦inPar c1 c2⟧ ρ = (I_s' ⊗? ⟦c2⟧) ((⟦c1⟧ ⊗? I_s) ρ)

What is I_s? 

⟦inPar c1 c2⟧ (ρ1 ⊗ ρ2) = ⟦c1⟧ ρ1 ⊗ ⟦c2⟧ ρ2.
*)

Lemma inPar_WT : forall W1 W1' W2 W2' (c1 : Box Var W1 W2) (c2 : Box Var W1' W2'), 
  Typed_Box Var c1 -> Typed_Box Var c2 ->
  Typed_Box Var (inPar c1 c2).
Proof. type_check. Qed.

Fixpoint units (n : nat) : Pat Var (n ⨂ One) := 
  match n with
  | O => unit
  | S n' => pair unit (units n')
  end. 
Lemma types_units : forall n, Types_Pat ∅ (units n).
Proof. induction n; type_check. Qed.

(* Can also just use (init b) #n $ (()) *)
Fixpoint initMany (b : bool) (n : nat) : Box Var One (n ⨂ Qubit):= 
  match n with 
  | 0    => id_circ
  | S n' => box_ () ⇒ 
           let_ q  ← unbox (init b) ();
           let_ qs ← unbox (initMany b n') ();
           (q, qs)
  end.
Lemma initMany_WT : forall b n, Typed_Box Var (initMany b n).
Proof. induction n; type_check. Qed.

Fixpoint inSeqMany (n : nat) {W} (c : Box Var W W) : Box Var W W:= 
  match n with
  | 0 => id_circ
  | S n' => inSeq c (inSeqMany n' c)
  end.
Lemma inSeqMany_WT : forall n W (c : Box Var W W), 
      Typed_Box Var c -> Typed_Box Var (inSeqMany n c).
Proof. intros. induction n as [ | n']; type_check. Qed.

Fixpoint inParMany (n : nat) {W W'} (c : Box Var W W') : Box Var (n ⨂ W) (n ⨂ W') := 
  match n with 
  | 0    => id_circ
  | S n' => inPar c (inParMany n' c)
  end.
Lemma inParMany_WT : forall n W W' (c : Box Var W W'), Typed_Box Var c  -> 
                                 Typed_Box Var (inParMany n c).
Proof. intros. induction n as [ | n']; type_check. Qed.       


End struct_circs.

(* Parallel binds more closely than sequence *)
Notation "b1 ∥ b2" := (inPar b1 b2) (at level 51, right associativity) : circ_scope.
Notation "b' · b" := (inSeq b b') (at level 60, right associativity) : circ_scope.
Notation "c1 ;; c2" := (inSeq c1 c2) (at level 60, right associativity) : circ_scope.

Notation "(())" := (units _) (at level 0) : circ_scope.
Notation "g # n" := (inParMany n g) (at level 11) : circ_scope.




Hint Resolve types_units id_circ_WT boxed_gate_WT init_WT inSeq_WT inPar_WT 
     initMany_WT inSeqMany_WT inParMany_WT : typed_db.


(*********************)
(** Classical Gates **)
(*********************)

Section classical_circs.

Context {Var : Set}.

(* These can't be used in oracles since they're not reversible. *)

(* NOT already exists *)

Definition CL_AND : Box Var (Qubit ⊗ Qubit) Qubit :=
  box_ (a,b) ⇒
    let_ z         ← ⌈init0⌉ $ ();
    let_ (a,(b,z)) ← ⌈CCNOT⌉ $ (a,(b,z));
    let_ a         ← ⌈meas⌉ $ a;
    let_ b         ← ⌈meas⌉ $ b;
    let_ ()        ← ⌈discard⌉ $ a;   
    let_ ()        ← ⌈discard⌉ $ b;   
    z.

Lemma CL_AND_WT : Typed_Box Var CL_AND.
Proof. type_check. Qed.

Definition CL_XOR : Box Var (Qubit ⊗ Qubit) Qubit := 
  box_ (a,b) ⇒ 
    let_ (a, b) ← ⌈CNOT⌉ $ (a,b);
    let_ a      ← ⌈meas⌉ $ a;
    let_ ()     ← ⌈discard⌉ $ a;
    b.
Lemma CL_XOR_WT : Typed_Box Var CL_XOR.
Proof. type_check. Qed.

Definition CL_OR : Box Var (Qubit ⊗ Qubit) Qubit :=
  box_ (a,b) ⇒ 
    let_ a'         ← ⌈_X⌉ $a;
    let_ b'         ← ⌈_X⌉ $b;
    let_ z          ← CL_AND $ (a',b');
    ⌈_X⌉ $z.
Lemma CL_OR_WT : Typed_Box Var CL_OR.
Proof. type_check. Qed.


(***********************)
(** Reversible Gates  **)
(***********************)

(* Apply the f(x,z) = g(x) ⊕ z construction, where g is the classical function 
   and z is an extra target qubit *)

(* This has a more efficient construction where we simply negate z
Definition TRUE : Box Var Qubit Qubit :=
  box_ z ⇒ 
    let_ x     ← init1 $();
    let_ (x,z) ← CNOT $(x,z);
    let_ ()    ← assert1 $x;
    output z.
*)
Definition TRUE : Box Var Qubit Qubit := ⌈_X⌉.
Lemma TRUE_WT : Typed_Box Var TRUE.
Proof. type_check. Qed.

(* This has a more efficient construction: the identity
Definition FALSE : Box Var Qubit Qubit :=
  box_ z ⇒ 
    let_ x     ← init0 $();
    let_ (x,z) ← CNOT $(x,z);
    let_ ()    ← assert0 $x;
    output z.
*)
Definition FALSE : Box Var Qubit Qubit := id_circ.
Lemma FALSE_WT : Typed_Box Var FALSE.
Proof. type_check. Qed.

Definition NOT : Box Var (Qubit ⊗ Qubit) (Qubit ⊗ Qubit) :=
  box_ (x,z) ⇒ 
    let_ x         ← ⌈_X⌉ $x;
    let_ (x,z)     ← ⌈CNOT⌉ $(x,z);
    let_ x         ← ⌈_X⌉ $x;
    (x,z).
Lemma NOT_WT : Typed_Box Var NOT.
Proof. type_check. Qed.

Definition AND : Box Var (Qubit ⊗ Qubit ⊗ Qubit) (Qubit ⊗ Qubit ⊗ Qubit) :=
  box_ (x,y,z) ⇒
    let_ (x,(y,z)) ← ⌈CCNOT⌉ $(x,(y,z));
    (x,y,z).    
Lemma AND_WT : Typed_Box Var AND.
Proof. type_check. Qed.

Definition XOR : Box Var (Qubit ⊗ Qubit ⊗ Qubit) (Qubit ⊗ Qubit ⊗ Qubit) := 
  box_ (x,y,z) ⇒
    let_ (x,z)     ← ⌈CNOT⌉ $(x,z);
    let_ (y,z)     ← ⌈CNOT⌉ $(y,z);
    (x,y,z).
Lemma XOR_WT : Typed_Box Var XOR.
Proof. type_check. Qed.
 
End classical_circs.
