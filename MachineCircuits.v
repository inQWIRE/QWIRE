Require Import Contexts.
Require Import TypedCircuits.
Require Import Program.

(* No input, output length 
Inductive Machine_Circuit : Set :=
| m_output : Machine_Circuit
| m_gate   : forall (l : list nat) {w1 w2}, 
               length l = num_wires w1
             -> Gate w1 w2
             -> Machine_Circuit
             -> Machine_Circuit.
*)

(* Version with output length.
Inductive Machine_Circuit : list nat -> Set :=
| m_output : forall l, Machine_Circuit l
| m_gate   : forall {l l' : list nat} {w1 w2}, 
               length l = num_wires w1
             -> Gate w1 w2
             -> Machine_Circuit l'
             -> Machine_Circuit l'.
*)

Inductive Tail_Circuit : nat -> Set :=
| m_output : forall (l : list nat), Tail_Circuit (length l)
| m_gate   : forall (l : list nat) {w1 w2 n}, 
               length l = num_wires w1
             -> Gate w1 w2
             -> Tail_Circuit n
             -> Tail_Circuit n.

Inductive Machine_Circuit : nat -> nat -> Set := 
| m_input : forall (l : list nat) {n}, Tail_Circuit n -> Machine_Circuit (length l) n.

(* Naivest possible composition: 
  only makes sense for circuits without input/output
Fixpoint m_compose (c1 c2 : Machine_Circuit) : Machine_Circuit :=
  match c1 with
  | m_output => c2
  | m_gate l eq g c1' => m_gate l eq g (m_compose c1' c2)
  end.
*)

(* *)