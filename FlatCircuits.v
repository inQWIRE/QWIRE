Require Import Contexts.
Require Import HOASCircuits.
Require Import Program.
Import Arith.

Open Scope circ_scope.

(** Flat Circuits **)

Inductive Flat_Circuit : Set :=
| flat_output : Pat -> Flat_Circuit 
| flat_gate   : forall {w1 w2}, Gate w1 w2 -> Pat -> Pat -> Flat_Circuit -> Flat_Circuit
| flat_lift  : Pat -> (bool -> Flat_Circuit) -> Flat_Circuit
.

Inductive Flat_Box : Set :=
| flat_box : Pat -> Flat_Circuit -> Flat_Box.

Fixpoint fresh_pat (W : WType) (n : nat) : Pat * nat := 
  match W with 
  | One => (unit, n) 
  | Qubit => (qubit n, S n)
  | Bit => (bit n, S n)
  | W1 ⊗ W2 => let (p1,n') := fresh_pat W1 n in
                   let (p2,n'') := fresh_pat W2 n' in
                   ((pair p1 p2), n'')
  end.

Fixpoint hoas_to_flat (c : Circuit) (n : nat): Flat_Circuit := 
  match c with
  | output p          => flat_output p
  (* This case isn't necessary, but it saves us from constructing extra patterns *)
  | gate (U u) p c    => flat_gate (U u) p p (hoas_to_flat (c p) n)
  | @gate W1 W2 g p c => let (p',n') := fresh_pat W2 n in
                        flat_gate g p p' (hoas_to_flat (c p') n')
  | lift p c          => flat_lift p (fun b => hoas_to_flat  (c b) n)
  end.

Definition hoas_to_flat_box (B : Box) (w : WType) : Flat_Box :=
  match B with
  | box c => let (p, n) := fresh_pat w 0  in 
            flat_box p (hoas_to_flat (c p) n)
  end.

(** Minimal Circuits for Denoting **)

(* Pats or just lists of Nats? *)
Inductive Min_Circuit : Set :=
| min_output : Pat -> Min_Circuit 
| min_gate   : forall {w1 w2}, Gate w1 w2 -> Pat -> Min_Circuit -> Min_Circuit
| min_lift  : Pat -> (bool -> Min_Circuit) -> Min_Circuit
.

Inductive Min_Box : Set :=
| min_box : WType -> Min_Circuit -> Min_Box.

(* Uses Nats *)
Definition qubit_to_bit (p : Pat) : Pat :=
  match p with 
  | qubit n => bit n 
  | _ => unit 
  end.

(* Original:
Parameter decrement_above : nat -> Circuit -> Circuit. *)

(* Expects a bit - otherwise returns 0 *)
Definition get_var (p : Pat) := match p with 
                                | bit n => n 
                                | qubit n => n
                                | _ => 0 end.

(* Precondition: x must appear in li *)
Fixpoint lookup (x : Var) (li : list Var) : nat :=
  match li with
  | nil => 0
  | y :: ys => if x =? y then 0 else S (lookup x ys)
  end.
 
Fixpoint hash_pat (p : Pat) (li : list Var) : Pat :=
  match p with 
  | unit => unit 
  | qubit x => qubit (lookup x li)
  | bit x => bit (lookup x li)
  | pair p1 p2 => pair (hash_pat p1 li) (hash_pat p2 li)
  end.

(* li maps free variables of c to qubit indices, 
   n is an upper bound on variables in c *) 
Program Fixpoint hoas_to_min (c: Circuit) (li : list Var) (n : nat) : Min_Circuit :=
  match c with
  | output p        => min_output (hash_pat p li)
  | gate g p c' => 
    match g with
    | U u           => min_gate g (hash_pat p li) (hoas_to_min (c' p) li n)
    | init0 | init1 => min_gate g unit (hoas_to_min (c' (qubit n)) (li ++ [n]) (S n))
    | new0 | new1   => min_gate g unit (hoas_to_min (c' (qubit n)) (li ++ [n]) (S n))
    | meas          => min_gate g (hash_pat p li) 
                                 (hoas_to_min (c' (qubit_to_bit p)) li n)
    | discard       => let li' := List.remove Nat.eq_dec (get_var p) li in
                      min_gate g (hash_pat p li) (hoas_to_min (c' unit) li' n)
    end
  | lift p c'   =>  let li' := List.remove Nat.eq_dec (get_var p) li in
                    min_lift (hash_pat p li) (fun b => hoas_to_min (c' b) li' n) 
  end.

Fixpoint pat_to_list (p : Pat) : list Var := 
  match p with
  | unit => []
  | bit x => [x]
  | qubit x => [x]
  | pair p1 p2 => (pat_to_list p1) ++ (pat_to_list p2)
  end.

Definition hoas_to_min_box (B : Box) (W : WType) :=
  match B with
  | box c => let (p, n) := fresh_pat W 0 in
            let li := pat_to_list p in 
            min_box W (hoas_to_min (c p) li n)
  end.

(* Flat Circuit Examples *)

Require Import HOASExamples.
Open Scope circ_scope.

Eval simpl in hoas_to_flat_box bell00 One.
Eval simpl in hoas_to_flat_box alice (Qubit ⊗ Qubit).
Eval simpl in hoas_to_flat_box  bob (Bit ⊗ Bit ⊗ Qubit). 
Eval simpl in hoas_to_flat_box teleport Qubit.

(* Min Circuit Examples *)

Eval simpl in hoas_to_min_box bell00 One.
Eval simpl in hoas_to_min_box alice (Qubit ⊗ Qubit).
Eval simpl in hoas_to_min_box bob (Bit ⊗ Bit ⊗ Qubit). 
Eval simpl in hoas_to_min_box teleport Qubit.

Close Scope circ_scope.

(* *)