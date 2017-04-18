Require Import Contexts.
Require Import TypedCircuits.
Require Import Program.

Inductive Machine_Circuit : Set :=
| m_output : Machine_Circuit
| m_gate   : forall (l : list nat) {w1 w2}, 
               length l = num_wires w1
             -> Gate w1 w2
             -> Machine_Circuit
             -> Machine_Circuit.

(* Version with output length. Might want input length as well.
Inductive Machine_Circuit : list nat -> Set :=
| m_output : forall l, Machine_Circuit l
| m_gate   : forall {l l' : list nat} {w1 w2}, 
               length l = num_wires w1
             -> Gate w1 w2
             -> Machine_Circuit l'
             -> Machine_Circuit l'.
*)

(* Naivest possible composition *)

Fixpoint m_compose (c1 c2 : Machine_Circuit) : Machine_Circuit :=
  match c1 with
  | m_output => c2
  | m_gate l eq g c1' => m_gate l eq g (m_compose c1' c2)
  end.

(* *)