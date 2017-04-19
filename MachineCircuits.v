Require Import Contexts.
Require Import FlatCircuits.
Require Import TypedCircuits.
Require Import Program.
Require Import List.
Require Import PeanoNat.
Require Import Omega.


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
  | @m_gate W1 W2 l g c => input c + num_wires W2 - num_wires W1
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
               length l = num_wires w1
             -> Gate w1 w2
             -> Machine_Circuit l'
             -> Machine_Circuit l'.
*)

(* Machine_Circuit m n : m is the number of input wires, n is the number of output wires *)
(*
Inductive Machine_Circuit : nat -> nat -> Set :=
| m_output : forall (l : list nat), Machine_Circuit (length l) (length l)
| m_gate   : forall (l : list nat) {w1 w2 m n}, 
               length l = num_wires w1
             -> Gate w1 w2
             -> Machine_Circuit (m + num_wires w2 - num_wires w1) n
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



Fixpoint pat_to_list {Γ W} (p : Pat Γ W) : list nat :=
  match p with
  | pair Γ1 Γ2 Γ0 W1 W2 valid merge p1 p2 => 
      let ls1 := pat_to_list p1 in
      let ls2 := pat_to_list p2 in 
      ls1 ++ ls2
  | qubit x Γ sing => [x]
  | bit   x Γ sing => [x]
  | unit => []
  end.
Lemma pat_to_list_length : forall Γ W (p : Pat Γ W), length (pat_to_list p) = num_wires W.
Proof.
  induction p; simpl; auto.
  rewrite app_length. auto.
Qed.


Fixpoint subst_eq_length (ls1 ls2 : list nat) : nat -> nat :=
  match ls1, ls2 with
  | m1 :: ls1, m2 :: ls2 => fun i => if Nat.eq_dec i m2 then m1 else (subst_eq_length ls1 ls2) i
  | _, _ => id
  end.

Definition subst_add (bound : nat) (ls2 : list nat) : nat * (nat -> nat) :=
  let new_bound := bound + length ls2 in
  (new_bound, subst_eq_length (seq bound (length ls2)) ls2).

Definition subst_add_1 (bound : nat) (ls2 : list nat) : nat -> nat :=
  match ls2 with
  | [m2] => fun i => if Nat.eq_dec i m2 then bound else i
  | _    => id
  end.

Definition subst_remove_1 (ls1 : list nat) : nat -> nat :=
  match ls1 with
  | [m1] => fun i => if Nat.ltb m1 i then i-1 else i
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

Lemma singleton_num_elts : forall x Γ W, SingletonCtx x W Γ -> num_elts Γ = 1.
Proof.
  induction x; intros Γ W H; inversion H; subst; simpl; auto.
  erewrite IHx; eauto.
Qed.

Lemma pat_square : forall Γ W (p : Pat Γ W), num_elts_o Γ = num_wires W.
Proof.
  induction 1; simpl; auto.
  - eapply singleton_num_elts; eauto.
  - eapply singleton_num_elts; eauto.
  - inversion i. rename x into Γ. inversion H; subst.
    erewrite num_elts_merge; [ | eauto | apply valid_valid].
    rewrite IHp1, IHp2; auto.
Defined.

Lemma lift_undefined : Untyped_Machine_Circuit.
Admitted.

Fixpoint Flat_to_Machine_Circuit {Γ W} (C : Flat_Circuit Γ W)  
                 : Machine_Circuit (num_elts_o Γ) (num_wires W) :=
  match C with
  | flat_output _ p => m_output (pat_to_list p)
  | @flat_gate Γ Γ1 _ _ _ _ _ _ _ _ _ _ g p1 p2 C' => 
    let ls1 := pat_to_list p1 in
    let ls2 := pat_to_list p2 in
    let f := subst_with_gate (num_elts_o (Γ ⋓ Γ1)) g ls1 ls2 in
    m_gate ls1 g (apply_substitution f (Flat_to_Machine_Circuit C'))
  | flat_lift _ _ _ _ => lift_undefined
  end.

(*
Definition Flat_Box_to_Machine_Circuit {W1 W2} (b : Flat_Box W1 W2) : Machine_Circuit (num_wires W1) (num_wires W2) :=
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
  rewrite (num_elts_merge Γ2 Γ (Γ2 ⋓ Γ)); auto.
  rewrite (num_elts_merge Γ1 Γ (Γ1 ⋓ Γ)); auto.
  rewrite (pat_square _ _ p1).
  rewrite (pat_square _ _ p2).
  apply eq_trans with (num_wires W2 + num_elts_o Γ + num_wires W1 - num_wires W1); 
    omega.
Defined. *)



(* *)