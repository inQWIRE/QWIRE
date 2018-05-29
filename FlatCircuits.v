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

Fixpoint fresh_pat (W : WType) (n : nat) : Pat W := 
  match W with 
  | One => unit 
  | Qubit => qubit n
  | Bit => bit n
  | W1 ⊗ W2 => pair (fresh_pat W1 n) (fresh_pat W2 (n + (size_WType W1)))
  end.


Search "size".

Fixpoint hoas_to_flat {w} (c : Circuit w) (n : nat): Flat_Circuit w :=
  match c with
  | output p             => flat_output p
  (* This case isn't necessary, but it saves us from constructing extra patterns *)
(*  | gate (U u) p c'      => flat_gate (U u) p p (hoas_to_flat _ (c' p) n)*)
  | @gate _ W1 W2 g p c' => let p' := fresh_pat W2 n in
                           flat_gate g p p' (hoas_to_flat (c' p') (n + size_WType W2))
  | lift p c             => flat_lift p (fun b => hoas_to_flat  (c b) n)
  end.

Definition hoas_to_flat_box {w1 w2} (B : Box w1 w2) : Flat_Box w1 w2 :=
  match B with
  | box c => let p := fresh_pat w1 0  in 
            flat_box p (hoas_to_flat (c p) (size_WType w1))
  end.

Fixpoint pat_to_list {w} (p : Pat w) : list Var := 
  match p with
  | unit => []
  | bit x => [x]
  | qubit x => [x]
  | pair p1 p2 => (pat_to_list p1) ++ (pat_to_list p2)
  end.


(* Uses Nats *)
Definition qubit_to_bit (p : Pat Qubit) : Pat Bit :=
  match p with 
  | qubit n => bit n 
  end.

(* Original:
Parameter decrement_above : nat -> Circuit -> Circuit. *)

(* Expects a (qu)bit - otherwise returns 0 *)
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
  | unit       => unit 
  | qubit x    => qubit (lookup x li)
  | bit x      => bit (lookup x li)
  | pair p1 p2 => pair (hash_pat p1 li) (hash_pat p2 li)
  end.


Require Import List.

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

About pat_to_list.
Definition substitution := list nat.
Definition apply_substitution (σ : substitution) (x : nat) := lookup x σ.


(* pat_subst ls p means replace all variables x in p with ls[x] if it is
defined; x otherwise Here, p is an index-pat, meaning that its values are
indices from 0 to n-1, not named variables*)
Fixpoint pat_subst (σ : substitution) {w} (p : Pat w) : Pat w :=
  match p with
  | unit => unit
  | qubit x => qubit (apply_substitution σ  x)
  | bit x => bit (apply_substitution σ x)
  | pair p1 p2 => pair (pat_subst σ p1) (pat_subst σ p2)
  end. 
Definition remove_from_subst {w} (p : Pat w) (σ : substitution) :=
  List.remove Nat.eq_dec (get_var p) σ.
Definition update_subst (σ : substitution) {w1 w2} (g : Gate w1 w2) (p : Pat w1) 
           : substitution :=
  match g with
  | U _ | meas | NOT => (* no change *) σ
  | init0 | init1 | new0 | new1 => σ ++ [length σ] (* since we're dealing with
    index-path, fresh variables should map to themselves *)
  | discard => remove_from_subst p σ
  end.

Fixpoint min_subst (σ : substitution) {w} (c : Min_Circuit w) : Min_Circuit w :=
  match c with
  | min_output p    => min_output (pat_subst σ p)
  | min_gate g p c' => let σ' := update_subst σ g p in
                       min_gate g (pat_subst σ p) (min_subst σ' c')
  | min_lift p f    => let σ' := remove_from_subst p σ in
                       min_lift (pat_subst σ p) (fun b => min_subst σ' (f b))
  end.
Definition mk_subst {w} (p : Pat w) : substitution :=
  pat_to_list p.

(* min_compose c c' plugs the $n$ outputs of c into the first n inputs of c' *)
Fixpoint min_compose {w w'} (c : Min_Circuit w) (c' : Min_Circuit w') : Min_Circuit w' :=
  match c with
  | min_output p => min_subst (mk_subst p) c'
  | min_gate g p c0 => min_gate g p (min_compose c0 c')
  | min_lift p f => min_lift p (fun b => min_compose (f b) c')
  end.

Open Scope circ_scope.
Definition q_pair x y := pair (qubit x) (qubit y).
Definition H_1 (q0 q1 q : nat) : Min_Circuit (Qubit ⊗ Qubit) :=
  min_gate H (qubit q) (
  min_output (q_pair q0 q1)).
Definition H_1_0 q0 q1 := H_1 q0 q1 q0.
Definition H_1_1 q0 q1 := H_1 q0 q1 q1.

(* LHS : let  (0,1) ← (1,0);
         gate 0 ← H @0;
         (0,1)
 
  RHS : gate 1 ← H @1;
        (1,0)
*)
Lemma ex_compose_output : min_compose (min_output (q_pair 1 0)) (H_1_0 0 1)
                        = H_1_0 1 0.
Proof. intros. reflexivity. Qed.

(* LHS : let (0,1) ← [gate 0 ← H @0; (1,0)];
         (1,0)

   RHS : gate 0 ← H @0;
         (0,1)
*)
Lemma ex_compose_H_1 : min_compose (H_1_1 1 0) (min_output (q_pair 1 0))
                     = H_1_0 0 1.
Proof. simpl. unfold H_1_0, H_1. reflexivity. Qed.



(* The type of a gate tells us whether we are 
   - keeping the same # of wires,
   - adding some number of wires, or
   - removing some number of wires
*)

(*
Definition update_pat {w1 w2} (g : Gate w1 w2) (p : Pat w1) : Pat w2 :=
  match g with
  | 
*)

Require Import Monad.
Definition MyState := State (substitution * Var).
Search State.
About stateM. 

Definition get_σ : MyState substitution :=
  do z ← get;
  return_ (fst z).
Definition get_fresh : MyState Var :=
  do z ← get;
  return_ (snd z).
Definition put_fresh (x : Var) : MyState () :=
  do σ ← get_σ;
  put (σ,x).
Definition put_σ (σ : substitution) : MyState () :=
  do x ← get_fresh;
  put (σ,x).
Definition update_σ (σ : substitution) : MyState () :=
  do σ' ← get_σ;
  put_σ (σ' ++ σ).

Definition update_fresh_by n : MyState () :=
  do m ← get_fresh;
  put_fresh (m + n).
Definition inc_fresh := update_fresh_by 1.

Definition hash_pat_M {w} (p : Pat w) : MyState (Pat w) :=
  do σ ← get_σ;
  return_ (hash_pat p σ).

Definition fresh_pat_M {w} : MyState (Pat w) :=
  do m ← get_fresh;
  let p := fresh_pat w m in
  do _ ← put_fresh (size_WType w);
  do _ ← update_σ (pat_to_list p);
  return_ p.

About foldM.
About fold_left.

Definition remove_var_M (x : Var) : MyState () :=
  do σ ← get_σ;
  put_σ (List.remove Nat.eq_dec x σ).

Definition remove_pat_M {w} (p : Pat w) : MyState () :=
  let li := pat_to_list p in
  foldM (fun _ => remove_var_M) () li.

(* process_gate takes as input a gate and the Var-pattern input to a gate, and
produces a Var-pattern than may have some new variables. All new variables are
added to the underlying list, and all expired variables are removed. The fresh
counter is also incremented if necessary

A Var-pattern is one populated by named variables coming from the HOAS
representation. e.g. the input of hash_pat_M is a Var-pattern, and the output of
hash_pat_M is a nat_pattern. *)
Definition process_gate {w1 w2} (g : Gate w1 w2) : Pat w1 -> MyState (Pat w2) :=
  match g with
  | U _ | NOT                   => fun p => return_ p
  | init0 | init1 | new0 | new1 => fun _ => fresh_pat_M
  | meas                        => fun p => return_ (qubit_to_bit p)
  | discard                     => fun p => do _ ← remove_pat_M p;
                                            return_ unit
  end.


(* not at all sure we can do this *)
Definition min_lift_M {w} (p : Pat Bit) (f : bool -> MyState (Min_Circuit w))
                    : MyState (Min_Circuit w).
Proof.
  set (c0 := f false).
  set (c1 := f true).
  intros st.
  set (s0 := c0 st).
  set (s1 := c1 st).
  (* we can just take the max of the two fresh variables, but that's not going to work for substitutions *)
Admitted.

Fixpoint hoas_to_min_aux {w} (c : Circuit w) 
                       : MyState (Min_Circuit w) :=
  match c with
  | output p   => do p ← hash_pat_M p;
                  return_ (min_output p)
  | gate g p f => do p' ← hash_pat_M p;
                  (* should we do fresh_pat_M before or after process_gate? *)
                  do q  ← process_gate g p;
                  do c' ← hoas_to_min_aux (f q);
                  return_ (min_gate g p' c')
  | lift p f   => do p' ← hash_pat_M p;
                  min_lift_M p' (fun x => hoas_to_min_aux (f x))
  end.

Definition hoas_to_min {w} (c : Circuit w) li n : Min_Circuit w :=
  fst (hoas_to_min_aux c (li,n)).

(*
(* li maps free variables of c to qubit indices, 
   n is an upper bound on variables in c *) 
Program Fixpoint hoas_to_min {w} (c: Circuit w) (li : list Var) (n : nat) 
                          : Min_Circuit w :=

  match c with
  | output p        => min_output (hash_pat p li)
  | @gate _ w1 w2 g p c' => 
(*  let n1 := size_WType w1 in
    let n2 := size_WType w2 in
    let li' := if n2 < n1 then (* shrink the list by p--the only time the list shrinks is discard *)
                               List.remove Nat.eq_dec (get_var p) li
                          else (* expand the list *) li ++ (seq n (n2-n1)) in
    let n' := n + (n2-n1) (* never want n to decrease *) in
    
    min_gate g (hash_pat p li) (hoas_to_min (c' _) li' n')
*)    
    match g with
    | U u           => min_gate g (hash_pat p li) (hoas_to_min (c' p) li n)
    | NOT           => min_gate g (hash_pat p li) (hoas_to_min (c' p) li n)
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
*)

Definition hoas_to_min_box {w1 w2} (B : Box w1 w2) :=
  match B with
  | box c => let p := fresh_pat w1 0 in
             let li := pat_to_list p in 
             min_box w1 (hoas_to_min (c p) li (size_WType w1))
  end.

(* Flat Circuit Examples *)

Require Import HOASExamples.
Open Scope circ_scope.

Eval simpl in hoas_to_flat_box bell00.
Eval simpl in hoas_to_flat_box alice.
Eval simpl in hoas_to_flat_box bob.
Eval simpl in hoas_to_flat_box teleport.

(* Min Circuit Examples *)

(*
Eval simpl in hoas_to_min_box bell00.
Eval simpl in hoas_to_min_box alice.
Eval simpl in hoas_to_min_box bob.
Eval simpl in hoas_to_min_box teleport.
*)

Require Import HOASCircuits.
About compose. Search compose.
About compose_typing.


About hoas_to_min.

(*
Definition Types_Continuation Γ {w w'} (f : Pat w -> Circuit w') :=
  forall (p : Pat w) {Γ_in Γ_out} (pf_v : is_valid Γ_out)
                                  (pf_m : Γ_out = Γ_in ⋓ Γ),
  Types_Pat Γ_in p -> Types_Circuit Γ_out (f p).

Record Types_Compose {w w'} (c : Circuit w) (f : Pat w -> Circuit w') :=
  { Γ1' : OCtx
  ; Γ1 : OCtx
  ; Γ  : OCtx
  ; v1 : is_valid Γ1'
  ; m1 : Γ1' = Γ1 ⋓ Γ
  ; types_c : Types_Circuit Γ1 c
  ; types_f : Types_Continuation Γ f 
  }.
Arguments Γ1' {w w' c f}.


Lemma types_compose_correct : forall {w w'} 
                                     (c : Circuit w) (f : Pat w -> Circuit w')
      (rec : Types_Compose c f),
      Types_Circuit (Γ1' rec) (compose c f).
Proof.
  destruct rec. simpl.
  eapply compose_typing; eauto.
Qed.
*)

Close Scope circ_scope.
Definition state_proj_2 {A B C} (op : State (A*B) C) (a : A) : State B C :=
  do b ← get;
  let (c,x) := runState op (a,b) in
  do _ ← put (snd x);
  return_ c.
Definition state_lift_2 {C} (op : State nat C) : MyState C :=
  do fresh ← get_fresh;
  let (c,fresh') := runState op fresh in
  do _ ← put_fresh fresh';
  return_ c.

Open Scope circ_scope.

Definition process_gate' {w1 w2}(g : Gate w1 w2)(p : Pat w1) : State nat (Pat w2) :=
  state_proj_2 (process_gate g p) [].

Fixpoint get_output' {w} (c : Circuit w) : State nat (Pat w) :=
  match c with
  | output p   => return_ p
  | gate g p f => do p' ← process_gate' g p;
                  get_output' (f p')
  | lift p f   => get_output' (f true) (* this is a cheat *)
  end.
Definition get_output {w} (c : Circuit w) (fresh : nat) : Pat w :=
  evalState (get_output' c) fresh.

Lemma get_output_gate : forall {w1 w2 w} 
      (g : Gate w1 w2) (p : Pat w1) (f : Pat w2 -> Circuit w) (fresh : nat),
      get_output (gate g p f) fresh = 
        let (p',fresh') := runState (process_gate' g p) fresh in
        get_output (f p') fresh'.
Admitted.

Definition hoas_to_min_compose {w w'} (c : Circuit w) (f : Pat w -> Circuit w')
   : MyState (Min_Circuit w') :=
  do fresh ← get_fresh;
  do c' ← hoas_to_min_aux c;
                          (* the idea is to figure out the output pattern of c,
                             and plug that into f *)
  do d  ← hoas_to_min_aux (f (get_output c fresh));
  return_ (min_compose c' d).


Lemma hoas_to_min_aux_subst : 
      forall {w w'} (p : Pat w) (f : Pat w -> Circuit w'),
      hoas_to_min_aux (f p) = do p' ← hash_pat_M p;
                              do c  ← hoas_to_min_aux (f p);
                              return_ (min_subst (mk_subst p') c).
Proof.
  intros. unfold hash_pat_M.
Admitted.


Lemma hoas_to_min_compose_correct : 
      forall {w w'} (c : Circuit w) (f : Pat w -> Circuit w'),
      hoas_to_min_aux (compose c f) = hoas_to_min_compose c f.
Proof.
  intros.
  induction c.
  - simpl.
    unfold hoas_to_min_compose.
    unfold hoas_to_min_aux at 2.
    simpl_m. 
    rewrite hoas_to_min_aux_subst.

    apply functional_extensionality; intros [σ fresh].
    simpl_m.
  - 
Opaque return_ bind. 
    unfold hoas_to_min_compose.
    simpl.
    simpl_m.
Transparent return_ bind.
    (* apply the IH *)
    transitivity (do p' ← hash_pat_M p;
                  do q ← process_gate g p;
                  do c' ← hoas_to_min_compose (c q) f;
                  return_ (min_gate g p' c'));
      [ repeat (apply bind_eq; auto; intros) | ].
    unfold hoas_to_min_compose.

    apply functional_extensionality; intros x.
    repeat (autounfold with monad_db; simpl).
    rewrite get_output_gate.

    destruct (process_gate g p x) as [p2 x2] eqn:Hg.
    destruct (hoas_to_min_aux (c p2) x2) as [c2 x2'] eqn:H_c_p2.

    assert (step : runState (process_gate' g p) (snd x) = (p2,snd x2)%core)
      by admit.
    rewrite step. simpl.
    destruct (hoas_to_min_aux (f (get_output (c p2) (snd x2))) x2') 
      as [c' x'].
    reflexivity.
  - unfold hoas_to_min_compose. simpl. 
    unfold hash_pat_M.
    simpl_m.
    admit.
Admitted.




Close Scope circ_scope.

(* *)
