Require Import Contexts.
Require Import HOASCircuits.
Require Import Program.

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

Fixpoint flatten_circ (c : Circuit) (n : nat): Flat_Circuit := 
  match c with
  | output p          => flat_output p
  (* This case isn't necessary, but it saves us from constructing extra patterns *)
  | gate (U u) p c    => flat_gate (U u) p p (flatten_circ (c p) n)
  | @gate W1 W2 g p c => let (p',n') := fresh_pat W2 n in
                        flat_gate g p p' (flatten_circ (c p') n')
  | lift p c          => flat_lift p (fun b => flatten_circ (c b) n)
  end.

Definition flatten_box (B : Box) (w : WType) : Flat_Box :=
  match B with
  | box c => let (p, n) := fresh_pat w 0  in 
            flat_box p (flatten_circ (c p) n)
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

Import Arith.

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

(*
Require Import Recdef.

Import Arith.

Fixpoint dec_pat_above (n : nat) (p : Pat) :=
  match p with
  | unit    => unit 
  | bit m   => if n <? m then bit (m - 1) else bit m
  | qubit m => if n <? m then qubit (m - 1) else qubit m
  | pair p1 p2 => pair (dec_pat_above n p1) (dec_pat_above n p2)
  end.

Fixpoint dec_above (n : nat) (c : Min_Circuit) :=
  match c with 
  | min_output p => min_output (dec_pat_above n p)
  | min_gate g p c => min_gate g (dec_pat_above n p) (dec_above n c)
  | min_lift p c => min_lift (dec_pat_above n p) (fun b => dec_above n (c b))
  end.

Fixpoint decr_above (n : nat) (c : Circuit) :=
  match c with 
  | output p => output (dec_pat_above n p)
  | gate g p c => gate g (dec_pat_above n p) (fun p => decr_above n (c p))
  | lift p c => lift (dec_pat_above n p) (fun b => decr_above n (c b))
  end.

Fixpoint circuit_size (c : Circuit) := 
  match c with
  | output p => 0
  | gate g p c => 1 + circuit_size (c unit)
  | lift p c   => 1 + circuit_size (c true)
  end.

Program Fixpoint hoas_to_min (c: Circuit) (n : nat) {measure (circuit_size c)} : Min_Circuit :=
  match c with
  | output p        => min_output p
  | gate g p c' => 
    match g with
    | U u           => min_gate g p (hoas_to_min (c' p) n)
    | init0 | init1 => min_gate g p (hoas_to_min (c' (qubit n)) (S n))
    | new0 | new1   => min_gate g p (hoas_to_min (c' (bit n)) (S n))
    | meas          => min_gate g p (hoas_to_min (c' (qubit_to_bit p)) n)
    | discard       => let c'':= decr_above (bit_value p) (c' unit) in 
                      min_gate g p (hoas_to_min c'' (n-1)) 
    end
  | lift p c'   =>  min_lift p (fun b => hoas_to_min (c' b) n) 
  end.

(*
Fixpoint hoas_to_min (c: Circuit) (n : nat) {struct c} : Min_Circuit :=
  match c with
  | output p        => min_output p
  | gate g p c' => 
    match g with
    | U u           => min_gate g p (hoas_to_min (c' p) n)
    | init0 | init1 => min_gate g p (hoas_to_min (c' (qubit n)) (S n))
    | new0 | new1   => min_gate g p (hoas_to_min (c' (bit n)) (S n))
    | meas          => min_gate g p (hoas_to_min (c' (qubit_to_bit p)) n)
    | discard       => let c'':= dec_above (bit_value p)
                                          (hoas_to_min (c' unit) n) in
                      min_gate g p c''
    end
  | lift p c'   =>  min_lift p (fun b => hoas_to_min (c' b) n) (* placeholder *)
  end.
*)  

(* Uses Contexts to order Pats
Parameter new_qubit : Ctx -> Pat * Ctx.
Fixpoint hoas_to_min (c: Circuit) (Γ : Ctx) : Min_Circuit :=
  match c with
  | output p        => min_output p
  | gate g p c' => 
    match g with
    | U u           => min_gate g p (hoas_to_min (c' p) Γ)
    | init0 | init1 => let (p', Γ') :=  new_qubit Γ in
                      min_gate g p (hoas_to_min (c' p) Γ')
    | _             => let Γ' 
                      min_gate g p (hoas_to_min (c' p) Γ) (* placeholder *)
    end
  | lift p c'   =>  min_lift p (fun b => hoas_to_min (c' b) Γ) (* placeholder *)
  end. *)
*)

(* Flat Circuit Examples *)

Require Import HOASExamples.
Open Scope circ_scope.

Eval simpl in flatten_box bell00 One.
Eval simpl in flatten_box alice (Qubit ⊗ Qubit).
Eval simpl in flatten_box bob (Bit ⊗ Bit ⊗ Qubit). 
Eval simpl in flatten_box teleport Qubit.

(* Min Circuit Examples *)

Eval simpl in hoas_to_min_box bell00 One.
Eval simpl in hoas_to_min_box alice (Qubit ⊗ Qubit).
(* Order of discards breaks things. Need to decrement by first discard first. *)
Eval simpl in hoas_to_min_box bob (Bit ⊗ Bit ⊗ Qubit). 
Eval simpl in hoas_to_min_box teleport Qubit.

Close Scope circ_scope.

(* *)