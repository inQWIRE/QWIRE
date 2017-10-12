Require Import Contexts.
Require Import HOASCircuits.
Require Import Program.
Import Arith.

Open Scope circ_scope.

(** Flat Circuits **)

Inductive Flat_Circuit (w : WType) : Set :=
| flat_output : Pat w -> Flat_Circuit w
| flat_gate   : forall {w1 w2}, Gate w1 w2 -> Pat w1 -> Pat w2 -> Flat_Circuit w -> Flat_Circuit w
| flat_lift  : Pat Bit -> (bool -> Flat_Circuit w) -> Flat_Circuit w
.
Arguments flat_output {w}.
Arguments flat_gate {w w1 w2}.
Arguments flat_lift {w}.

Inductive Flat_Box w1 w2 : Set :=
| flat_box : Pat w1 -> Flat_Circuit w2 -> Flat_Box w1 w2.
Arguments flat_box {w1 w2}.

Fixpoint fresh_pat (W : WType) (n : nat) : Pat W * nat := 
  match W with 
  | One => (unit, n) 
  | Qubit => (qubit n, S n)
  | Bit => (bit n, S n)
  | W1 ⊗ W2 => let (p1,n') := fresh_pat W1 n in
               let (p2,n'') := fresh_pat W2 n' in
               ((pair p1 p2), n'')
  end.
Print gate.
Definition hoas_to_flat {w} (c : Circuit w) (n : nat): Flat_Circuit w.
Proof.
  generalize dependent n.
  induction c; intros n.
  - refine (flat_output p).
  - destruct (fresh_pat w2 n) as [p' n'].
    refine (flat_gate g p p' (H p' n')).
  - refine (flat_lift p (fun b => H b n)).
Defined.
(*
Fixpoint hoas_to_flat {w} (c : Circuit w) (n : nat): Flat_Circuit w :=
  match c with
  | output p          => flat_output p
  (* This case isn't necessary, but it saves us from constructing extra patterns *)
(*  | gate (U u) p c'      => flat_gate (U u) p p (hoas_to_flat _ (c' p) n)*)
  | gate g p c' => let (p',n') := fresh_pat _ n in
                   flat_gate g p p' (hoas_to_flat (c p') n')
  | lift p c          => _ (*flat_lift p (fun b => hoas_to_flat  (c b) n)*)
  end.
*)

Definition hoas_to_flat_box {w1 w2} (B : Box w1 w2) : Flat_Box w1 w2 :=
  match B with
  | box c => let (p, n) := fresh_pat w1 0  in 
            flat_box p (hoas_to_flat (c p) n)
  end.

(** Minimal Circuits for Denoting **)

(* Pats or just lists of Nats? *)
Inductive Min_Circuit w : Set :=
| min_output : Pat w -> Min_Circuit w
| min_gate   : forall {w1 w2}, Gate w1 w2 -> Pat w1 -> Min_Circuit w -> Min_Circuit w
| min_lift  : Pat Bit -> (bool -> Min_Circuit w) -> Min_Circuit w
.

Inductive Min_Box (w1 w2 : WType) : Set :=
(* the input pattern will just be the first |w1| variables *)
| min_box :  Min_Circuit w2 -> Min_Box w1 w2.
Arguments min_output {w}.
Arguments min_gate {w w1 w2}.
Arguments min_lift {w}.
Arguments min_box w1 {w2}.

(* Uses Nats *)
Definition qubit_to_bit (p : Pat Qubit) : Pat Bit :=
  match p with 
  | qubit n => bit n 
  end.

(* Original:
Parameter decrement_above : nat -> Circuit -> Circuit. *)

(* Expects a bit - otherwise returns 0 *)
Definition get_var {w} (p : Pat w) := match p with 
                                | bit n => n 
                                | qubit n => n
                                | _ => 0 end.

(* Precondition: x must appear in li *)
Fixpoint lookup (x : Var) (li : list Var) : nat :=
  match li with
  | nil => 0
  | y :: ys => if x =? y then 0 else S (lookup x ys)
  end.
 
Fixpoint hash_pat {w} (p : Pat w) (li : list Var) : Pat w :=
  match p with 
  | unit => unit 
  | qubit x => qubit (lookup x li)
  | bit x => bit (lookup x li)
  | pair p1 p2 => pair (hash_pat p1 li) (hash_pat p2 li)
  end.

(* li maps free variables of c to qubit indices, 
   n is an upper bound on variables in c *) 
Program Fixpoint hoas_to_min {w} (c: Circuit w) (li : list Var) (n : nat) 
                          : Min_Circuit w :=

  match c with
  | output p        => min_output (hash_pat p li)
  | gate g p c' => 
    match g with
    | U u           => min_gate g (hash_pat p li) (hoas_to_min (c' p) li n)
    | init0 | init1 => min_gate g unit (hoas_to_min (c' (qubit n)) (li ++ [n]) (S n))
    | new0 | new1   => min_gate g unit (hoas_to_min (c' (bit n)) (li ++ [n]) (S n))
    | meas          => min_gate g (hash_pat p li) 
                                 (hoas_to_min (c' (qubit_to_bit p)) li n)
    | discard       => let li' := List.remove Nat.eq_dec (get_var p) li in
                      min_gate g (hash_pat p li) (hoas_to_min (c' unit) li' n)
    end
  | lift p c'   =>  let li' := List.remove Nat.eq_dec (get_var p) li in
                    min_lift (hash_pat p li) (fun b => hoas_to_min (c' b) li' n) 
  end.

Fixpoint pat_to_list {w} (p : Pat w) : list Var := 
  match p with
  | unit => []
  | bit x => [x]
  | qubit x => [x]
  | pair p1 p2 => (pat_to_list p1) ++ (pat_to_list p2)
  end.

Require Import List.

Definition hoas_to_min_box {w1 w2} (B : Box w1 w2) :=
  match B with
  | box c => let (p, n) := fresh_pat w1 0 in
             let li := pat_to_list p in 
             min_box w1 (hoas_to_min (c p) li n)
  end.

(* Flat Circuit Examples *)

Require Import HOASExamples.
Open Scope circ_scope.

Eval simpl in hoas_to_flat_box bell00.
Eval simpl in hoas_to_flat_box alice.
Eval simpl in hoas_to_flat_box bob.
Eval simpl in hoas_to_flat_box teleport.

(* Min Circuit Examples *)

Eval simpl in hoas_to_min_box bell00.
Eval simpl in hoas_to_min_box alice.
Eval simpl in hoas_to_min_box bob.
Eval simpl in hoas_to_min_box teleport.

Close Scope circ_scope.

(* *)