(* Monad type class *)
(* Adapted from https://coq.inria.fr/cocorico/AUGER_Monad *)

Require Import Notations.
Set Implicit Arguments.

Require Import List.
Import ListNotations.

(** * The Monad Type Class *)

Class Monad (m: Type -> Type): Type :=
{ return_: forall A, A -> m A;
  bind: forall A, m A -> forall B, (A -> m B) -> m B;

  right_unit: forall A (a: m A), a = bind a (@return_ A);
  left_unit: forall A (a: A) B (f: A -> m B),
             f a = bind (return_ a) f;
  associativity: forall A (ma: m A) B f C (g: B -> m C),
                 bind ma (fun x => bind (f x) g) = bind (bind ma f) g
}.

Notation "a >>= f" := (bind a _ f) (at level 50, left associativity).

Section monadic_functions.
 Variable m: Type -> Type.
 Variable M: Monad m.

 Definition wbind {A: Type} (ma: m A) {B: Type} (mb: m B) :=
 ma >>= fun _=>mb.

 Definition liftM {A B: Type} (f: A->B) (ma: m A): m B :=
 ma >>= (fun a => return_ (f a)).

 Definition join {A: Type} (mma: m (m A)): m A :=
 mma >>= (fun ma => ma).
End monadic_functions.

Notation "a >> f" := (wbind _ a f) (at level 50, left associativity).
Notation "'do' a ← e ; c" := (e >>= (fun a => c)) (at level 60, right associativity).

(** * Some classic Monads *)
(** ** The Maybe monad (using option type) *)
Instance Maybe: Monad option :=
{| return_ := fun _ => Some;
   bind := fun A m B f => match m with None => None | Some a => f a end
|}.
(* Checking the 3 laws *)
 (* unit_left *)
 abstract (intros A a; case a; split).
 (* unit_right *)
 abstract (split).
 (* associativity *)
 abstract (intros A m B f C g; case m; split).
Defined.

(** The Reader monad *)
Axiom Eta: forall A (B: A -> Type) (f: forall a, B a), f = fun a=>f a.

Instance Reader (E: Type): Monad (fun A => E -> A) :=
{| return_ := fun A (a: A) e => a;
   bind := fun A m B f e => f (m e) e
|}.
(* Checking the 3 laws *)
 (* unit_left *)
 intros; apply Eta.
 (* unit_right *)
 intros; apply Eta.
 (* associativity *)
 reflexivity.
Defined.

(** ** The State monad *)

Axiom Ext: forall A (B: A->Type) (f g: forall a, B a), (forall a, f a = g a) -> f = g.

Definition State S A := S -> A * S.

Instance State_Monad (S: Type): Monad (State S) :=
{| return_ := fun A (a: A) s => (a, s);
   bind := fun A m B f s => let (a, s) := m s in f a s
|}.
(* Checking the 3 laws *)
 (* unit_left *)
 abstract (intros;apply Ext;intros s;destruct (a s);split).
 (* unit_right *)
 abstract (intros;apply Eta).
 (* associativity *)
 abstract (intros;apply Ext;intros s;destruct (ma s);reflexivity).
Defined.

Definition get {S} : State S S := fun s => (s,s).
Definition put {S} (s : S) : State S unit := fun _ => (tt,s).
Definition runState {S A} (st : State S A) (s : S) : A := 
  match st s with (a,_) => a end.
Definition execState {S A} (st : State S A) (s : S) : S := 
  match st s with (_,s') => s' end.

Fixpoint bind_list A (ls : list A) B (f : A -> list B) : list B :=
  match ls with
  | [] => []
  | a :: ls' => f a ++ bind_list ls' f
  end.

Instance List_Monad : Monad list := 
{| return_ := fun A (a : A) => [a];
   bind    := bind_list
|}.
  - induction a as [ | a ls]; simpl; auto.
    rewrite <- IHls; auto.
  - intros; simpl; rewrite app_nil_r; auto.
  - induction ma as [ | a ls]; intros B f C g; simpl; auto.
    rewrite IHls. admit.
Admitted.