Require Import Contexts.
Require Import FlatCircuits.
Require Import HOASCircuits.
Require Import Program.
Require Import List.
Require Import PeanoNat.
Require Import Omega.
Require Import Denotation.

(* No input, output length *)
Inductive Untyped_Machine_Circuit : Set :=
| m_output : list nat -> Untyped_Machine_Circuit
| m_gate   : forall {w1 w2}, 
                list nat 
             -> Gate w1 w2
             -> Untyped_Machine_Circuit
             -> Untyped_Machine_Circuit.
Definition Machine_Circuit (m n : nat) := Untyped_Machine_Circuit.

Fixpoint input (c : Untyped_Machine_Circuit) : nat :=
  match c with
  | m_output l => length l
  | @m_gate W1 W2 l g c => input c + size_WType W2 - size_WType W1
  end.
Fixpoint output (c : Untyped_Machine_Circuit) : nat :=
  match c with
  | m_output l => length l
  | m_gate _ _ c => output c
  end.

Definition WF_Machine_Circuit {m n} (c : Machine_Circuit m n) : Prop :=
  input c = m /\ output c = n.

(* Version with output length.
Inductive Machine_Circuit : list nat -> Set :=
| m_output : forall l, Machine_Circuit l
| m_gate   : forall {l l' : list nat} {w1 w2}, 
               length l = size_WType w1
             -> Gate w1 w2
             -> Machine_Circuit l'
             -> Machine_Circuit l'.
*)

(* Machine_Circuit m n : m is the number of input wires, n is the number of output wires *)
(*
Inductive Machine_Circuit : nat -> nat -> Set :=
| m_output : forall (l : list nat), Machine_Circuit (length l) (length l)
| m_gate   : forall (l : list nat) {w1 w2 m n}, 
               length l = size_WType w1
             -> Gate w1 w2
             -> Machine_Circuit (m + size_WType w2 - size_WType w1) n
             -> Machine_Circuit m n.
*)

(*
(* morally, a Machine_Box m n should only use variables less than m*)
Inductive Machine_Box : nat -> nat -> Set := 
| m_box : forall m {n}, Machine_Circuit m n -> Machine_Box m n.
*)

(* Naivest possible composition: 
  only makes sense for circuits without input/output *)
Fixpoint m_compose (c1 c2 : Untyped_Machine_Circuit) : Untyped_Machine_Circuit :=
  match c1 with
  | m_output _ => c2
  | m_gate l g c1' => m_gate l g (m_compose c1' c2)
  end.
(* TODO: prove correctness? *)


Fixpoint subst_eq_length (ls1 ls2 : list nat) : nat -> nat :=
  match ls1, ls2 with
  | m1 :: ls1, m2 :: ls2 => fun i => if Nat.eq_dec i m2 then m1 else (subst_eq_length ls1 ls2) i
  | _, _ => id
  end.

Definition subst_add (bound : nat) (ls2 : list nat) : nat * (nat -> nat) :=
  let new_bound := (bound + length ls2)%nat in
  (new_bound, subst_eq_length (seq bound (length ls2)) ls2).

Definition subst_add_1 (bound : nat) (ls2 : list nat) : nat -> nat :=
  match ls2 with
  | [m2] => fun i => if Nat.eq_dec i m2 then bound else i
  | _    => id
  end.

Definition subst_remove_1 (ls1 : list nat) : nat -> nat :=
  match ls1 with
  | [m1] => fun i => if Nat.ltb m1 i then (i-1)%nat else i
  | _    => id
  end.
  
(* Returns a new bound and a substitution *)
Definition subst_with_gate {W1 W2} (bound : nat) (g : Gate W1 W2) (p1 p2 : list nat) 
                           : nat -> nat :=
  match g with
  | @U W u  => subst_eq_length p1 p2
  | meas    => subst_eq_length p1 p2
  | init0   => subst_add_1 bound p2
  | init1   => subst_add_1 bound p2
  | new0    => subst_add_1 bound p2
  | new1    => subst_add_1 bound p2
  | discard => subst_remove_1 p1
  end.

Fixpoint apply_substitution (f : nat -> nat) (C : Untyped_Machine_Circuit) : Untyped_Machine_Circuit :=
  match C with
  | m_output l => m_output (map f l)
  | m_gate l g C' => m_gate (map f l) g (apply_substitution f C')
  end.

Lemma singleton_size_Ctx : forall x Γ W, SingletonCtx x W Γ -> size_Ctx Γ = 1%nat.
Proof.
  induction x; intros Γ W H; inversion H; subst; simpl; auto.
  erewrite IHx; eauto.
Qed.

Lemma pat_square : forall Γ W (p : Pat Γ W), size_OCtx Γ = size_WType W.
Proof.
  induction 1; simpl; auto.
  - eapply singleton_size_Ctx; eauto.
  - eapply singleton_size_Ctx; eauto.
  - subst. rewrite size_ctx_merge; auto.
Defined.

Lemma lift_undefined : Untyped_Machine_Circuit.
Admitted.

Fixpoint Flat_to_Machine_Circuit {Γ W} (C : Flat_Circuit Γ W)  
                 : Machine_Circuit (size_OCtx Γ) (size_WType W) :=
  match C with
  | flat_output p => m_output (pat_to_list p)
  | @flat_gate Γ Γ1 _ _ _ _ _ _ _ _ _ _ g p1 p2 C' => 
    let ls1 := pat_to_list p1 in
    let ls2 := pat_to_list p2 in
    let f := subst_with_gate (size_OCtx (Γ ⋓ Γ1)) g ls1 ls2 in
    m_gate ls1 g (apply_substitution f (Flat_to_Machine_Circuit C'))
  | flat_lift _ _ => lift_undefined
  end.

(*
Definition Flat_Box_to_Machine_Circuit {W1 W2} (b : Flat_Box W1 W2) : Machine_Circuit (size_WType W1) (size_WType W2) :=
  match b with
  | flat_box p C => Flat_to_Machine_Circuit C
  end.
*)

(*
Next Obligation. rewrite pat_to_list_length. rewrite (pat_square _ _ p); auto.
Defined.
Next Obligation. apply pat_to_list_length. Defined.
Next Obligation. apply pat_to_list_length. Defined.
Next Obligation. 
  rewrite (size_ctx_merge Γ2 Γ (Γ2 ⋓ Γ)); auto.
  rewrite (size_ctx_merge Γ1 Γ (Γ1 ⋓ Γ)); auto.
  rewrite (pat_square _ _ p1).
  rewrite (pat_square _ _ p2).
  apply eq_trans with (size_WType W2 + size_OCtx Γ + size_WType W1 - size_WType W1); 
    omega.
Defined. *)


Fixpoint denote_machine_circuit m n (c : Machine_Circuit m n) : Superoperator (2^m) (2^n) :=
  match c with 
  | m_output l         => super (swap_list n l)
  | @m_gate w1 w2 l g c => compose_super (denote_machine_circuit (m+〚w2〛-〚w1〛) n c)
                                        (apply_gate g l)
  end.

(* Need a richer description of correctness because we need to refer to the
circuit in the condition, and we also need a stronger condition thatn WF_Machie_Circuit *)

Instance Denote_Machine_Circuit {m n} : Denote (Machine_Circuit m n) (Superoperator (2^m) (2^n)) := {| denote := fun C => denote_machine_circuit m n C |}.

(* *)
