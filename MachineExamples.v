Require Import Program.
Require Import Datatypes.
Require Import Arith.
Require Import List.
Require Import Contexts.
Require Import TypedCircuits.
Require Import MachineCircuits.
Import ListNotations.
Open Scope list_scope.


(*** Paper Examples ***)

(*
Set Printing Coercions.

Tactic Notation (at level 0) "make_circ" uconstr(C) := refine C; type_check.
Tactic Notation (at level 0) "box" uconstr(C) := refine (box (fun _ => C)); type_check.

Notation "()" := unit : circ_scope.
Notation "( x , y , .. , z )" := (pair _ _ _ _ _ _ _ .. (pair _ _ _ _ _ _ _ x y) .. z) (at level 0) : circ_scope.


Notation output p := (output _ p).
Notation gate g p1 := (gate _ _ _ g p1 (fun _ _ _ _ p' => output p')).
Notation comp p c1 c2 := (compose c1 _ _ (fun _ _ _ _ p => c2)).
Notation letpair p1 p2 p c := (let 'existT23 _ _ p1 p2 _ := wproj p in c).


Notation "'letC' p ← c1 ; c2" := (comp p c1 c2)
                            (at level 10, right associativity) : circ_scope.
Notation "'letC' ( p1 , p2 ) ← c1 ; c2" := (compose c1 _ _ (fun _ _ _ _ x => letpair p1 p2 x c2)) 
                            (at level 10, right associativity) : circ_scope.
Notation "'letC' ( p1 , p2 , p3 ) ← c1 ; c2" :=
    (compose c1 _ _ (fun _ _ _ _ x => let 'existT23 _ _ y  p3 _ := wproj x in
                                      let 'existT23 _ _ p1 p2 _ := wproj y in
                                      c2))
                            (at level 10, right associativity) : circ_scope.
Notation "'letC' ( ( p1 , p2 ) , p3 ) ← c1 ; c2" := 
    (compose c1 _ _ (fun _ _ _ _ x => let 'existT23 _ _ y  p3 _ := wproj x in
                                      let 'existT23 _ _ p1 p2 _ := wproj y in
                                      c2))
                            (at level 10, right associativity) : circ_scope.
Notation "'letC' ( p1 , ( p2 , p3 ) ) ← c1 ; c2" :=
    (compose c1 _ _ (fun _ _ _ _ x => let 'existT23 _ _ p1 y  _ := wproj x in
                                      let 'existT23 _ _ p2 p3 _ := wproj y in
                                      c2))
                            (at level 10, right associativity) : circ_scope.
Notation "'letC' ( ( p1 , p2 ) , ( p3 , p4 ) ) ← c1 ; c2" :=
    (compose c1 _ _ (fun _ _ _ _ x => let 'existT23 _ _ y  z  _ := wproj x in
                                      let 'existT23 _ _ p1 p2 _ := wproj y in
                                      let 'existT23 _ _ p3 p4 _ := wproj z in
                                      c2))
                            (at level 10, right associativity) : circ_scope.


Notation unbox c p := (unbox c _ p).

Notation lift_compose x c1 c2 := (compose c1 _ _ (fun _ _ _ _ p' => lift _ _ p' (fun x => c2))).
Notation lift_pat x p c := (lift _ _ p (fun x => c)).
Notation "'lift' x ← c1 ; c2" := (lift_pat x c1 c2) (at level 10, right associativity) : circ_scope.

*)


(* Alternative Notations:

Notation out p := (output p).
Notation gate g p p' c := (gate _ _ _ g p (fun _ _ _ _ p' => c)).

Notation "p1 & p2 <<- p ; c" := (bind' p1 p2 p c) (at level 10, right associativity).
Notation "() <<-- p ; c" := (match elim_unit p with eq_refl => c end) (at level 10).
Notation "p' <-- 'gate g 'on' p ; C" := (gate' g p p' C) 
                                          (at level 10, right associativity).   
Notation "p <-- c1 ;; c2" := (comp' p c1 c2) (at level 10, right associativity).

Future work:
Notation gate' g p1 p2 c := (gate _ _ g p1 (fun _ _ _ z => match z (* w2? *) with
                                                        | p2 => c
                                                        end)).
*)


Infix "↦" := m_compose (at level 12, left associativity).  
Notation "'gate' g 'on' l ; C" := (m_gate l _ g C) (at level 10, right associativity).
Notation out := (m_output). 

Definition id_circ : Machine_Circuit := out.

Program Definition new_discard : Machine_Circuit := 
  gate new0 on [];
  gate discard on [0];
  out.

Program Definition init_discard : Machine_Circuit :=
  gate init0 on [];
  gate meas on [0];
  gate discard on [0];
  out.

Program Definition hadamard_measure : Machine_Circuit :=
  gate H on [0];
  gate meas on [0];
  out.

Program Definition deutsch (U_f : Gate (Qubit ⊗ Qubit) (Qubit ⊗ Qubit)) : Machine_Circuit :=
  gate init0 on [];
  gate H on [0];
  gate init1 on [];
  gate H on [1];
  gate U_f on [0;1];
  gate meas on [0];
  gate discard on [0];
  out.

Program Definition init (b : bool) : Machine_Circuit :=
  if b then (gate init1 on []; out) else (gate init0 on []; out).

(** Teleport **)

Program Definition bell00 : Machine_Circuit :=
  gate init0 on [];
  gate init0 on [];
  gate H on [1];
  gate CNOT on [1;2];
  out.

Program Definition alice : Machine_Circuit :=
  gate CNOT on [0;1];
  gate H on [0];
  gate meas on [0];
  gate meas on [1];
  out.

Program Definition bob : Machine_Circuit :=
  gate (bit_control σx) on [1;2];
  gate (bit_control σz) on [0;2];
  gate discard on [1];
  gate discard on [0]; 
  out.

Definition teleport : Machine_Circuit := bell00 ↦ alice ↦ bob.

Print teleport.
Eval compute in teleport.


(* *)
