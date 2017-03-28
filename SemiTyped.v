Require Import Arith.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require Import Program.
Require Import Contexts.
Require Import Monad.


(* SYNTAX *)

Inductive Pat : WType -> Set :=
| unit  : Pat One
| qubit : Var -> Pat Qubit
| bit   : Var -> Pat Bit
| pair  : forall {w1 w2}, Pat w1 -> Pat w2 -> Pat (Tensor w1 w2)
.




Inductive Unitary : WType -> Set := 
  | H : Unitary Qubit 
  | σx : Unitary Qubit
  | σy : Unitary Qubit
  | σz : Unitary Qubit
  | CNOT : Unitary (Qubit ⊗ Qubit)
  | control : forall {W} (U : Unitary W), Unitary (Qubit ⊗ W) 
  | bit_control : forall {W} (U : Unitary W), Unitary (Bit ⊗ W) 
  | transpose : forall {W} (U : Unitary W), Unitary W.
Inductive Gate : WType -> WType -> Set := 
  | U : forall {W} (u : Unitary W), Gate W W
  | init0 : Gate One Qubit
  | init1 : Gate One Qubit
  | new0 : Gate One Bit
  | new1 : Gate One Bit
  | meas : Gate Qubit Bit
  | discard : Gate Bit One.


Inductive Circuit : WType -> Set :=
| output : forall {w}, Pat w -> Circuit w
| gate   : forall {w1 w2 w},
           Gate w1 w2 -> Pat w1 -> Pat w2 -> Circuit w -> Circuit w
| lift   : forall {w w'}, Pat w -> (interpret w -> Circuit w') -> Circuit w'
.

(*

(* This is a fresh variable monad *)
Definition Fresh := State nat.
Definition inc : Fresh () := get >>= fun x => put (S x).

Definition see_var (x : nat) : Fresh () := get >>= fun y => put (max x y).
Fixpoint see_pat {W} (p : Pat W) : Fresh () :=
  match p with
  | unit    => return_ tt
  | qubit x => see_var x
  | bit x   => see_var x
  | pair p1 p2 => see_pat p1 >> see_pat p2
  end.
Fixpoint see_circuit {W} (c : Circuit W) : Fresh () :=
  match c with
  | output p       => see_pat p
  | gate g p1 p2 c => see_pat p1 >> see_pat p2 >> see_circuit c
  | lift p f       => see_pat p (* bad *)
  end.

Fixpoint var {W : WType} : Fresh (Pat W) :=
  match W with
  | One => return_ unit
  | Qubit => inc >> get >>= fun x => return_ (qubit x)
  | Bit   => inc >> get >>= fun x => return_ (bit x)
  | Tensor W1 W2 => do p1 ← @var W1;
                    do p2 ← @var W2;
                    return_ (pair p1 p2)
  end.

Definition fresh {W1 W2} (f : Pat W1 -> Circuit W2) : Pat W1 :=
  runState ( do p0 ← var; 
             do _  ← see_circuit (f p0);
             var ) 0.

Definition hoas_gate {W1 W2 W} (g : Gate W1 W2) (p1 : Pat W1) 
                               (f : Pat W2 -> Circuit W) : Circuit W :=
  let p2 := fresh f in 
  gate g p1 p2 (f p2).

 
Definition rename {W} {W'} (p' p : Pat W) : Circuit W' -> Circuit W'.
Admitted.
*)

Fixpoint compose {W W'} (c : Circuit W) : (Pat W -> Circuit W') -> Circuit W' :=
  match c with
  | output p       => fun f => f p
  | gate g p1 p2 k => fun f => gate g p1 p2 (compose k f)
  | lift p g       => fun f => lift p (fun p' => compose (g p') f)
  end.

(* TYPING *) 

Definition Merge (Γ1 Γ2 Γ : Ctx) := Γ1 ⋓ Γ2 = Γ.

Inductive WF_Pat : forall {W}, Ctx -> Pat W -> Set :=
| wf_unit  : WF_Pat [] unit
| wf_qubit : forall {x Γ}, SingletonCtx x Qubit Γ -> WF_Pat Γ (qubit x)
| wf_bit   : forall {x Γ}, SingletonCtx x Bit Γ -> WF_Pat Γ (bit x)
| wf_pair  : forall {Γ1 Γ2 Γ : Ctx} {W1 W2} (p1 : Pat W1) (p2 : Pat W2), 
             Merge Γ1 Γ2 Γ ->
             WF_Pat Γ1 p1 -> WF_Pat Γ2 p2 -> WF_Pat Γ (pair p1 p2)
.
             
Inductive WF_Circuit : forall {W}, Ctx -> Circuit W -> Set :=
| wf_output : forall {W} (p : Pat W) {Γ},
              WF_Pat Γ p ->
              WF_Circuit Γ (output p)
| wf_gate   : forall {W1 W2 W} {g : Gate W1 W2} 
                     {p1 : Pat W1} {p2 : Pat W2} {c : Circuit W}
                     {Γ1 Γ Γ1' Γ2 Γ2'},
              Merge Γ1 Γ Γ1' -> Merge Γ2 Γ Γ2' ->
              WF_Pat Γ1 p1 ->
              WF_Pat Γ2 p2 ->
              WF_Circuit Γ2' c ->
              WF_Circuit Γ1' (gate g p1 p2 c)
| wf_lift   : forall {W W'} {p : Pat W} {f : interpret W -> Circuit W'}
                     {Γ Γ' Γ''},
              Merge Γ Γ' Γ'' ->
              WF_Pat Γ p ->
              (forall (x : interpret W), WF_Circuit Γ' (f x)) ->
              WF_Circuit Γ'' (lift p f)
.

Definition FinMap A := list (option A).
Fixpoint union {A} (Γ1 Γ2 : FinMap A) : FinMap A :=
  match Γ1, Γ2 with
  | [], _ => Γ2
  | _, [] => Γ1
  | Some w1 :: Γ1, _  :: Γ2 => Some w1 :: union Γ1 Γ2
  | None    :: Γ1, w2 :: Γ2 => w2 :: union Γ1 Γ2
  end.

Fixpoint domain_pat {W} (p : Pat W) : Ctx :=
  match p with
  | unit       => []
  | qubit x    => singleton x W
  | bit x      => singleton x W
  | pair p1 p2 => union (domain_pat p1) (domain_pat p2)
  end.

Fixpoint zip {A B} (ls1 : list A) (ls2 : list B) : list (A * B) :=
  match ls1, ls2 with
  | [], _ => []
  | _, [] => []
  | a :: ls1, b :: ls2 => (a,b) :: zip ls1 ls2
  end.

Fixpoint all_vals W : list (interpret W) :=
  match W with
  | One     => []
  | Qubit   => [true;false]
  | Bit     => [true;false]
  | W1 ⊗ W2 => zip (all_vals W1) (all_vals W2)
  end.

Fixpoint domain_circ {W} (c : Circuit W) : Ctx :=
  match c with
  | output p       => domain_pat p
  | gate g p1 p2 c => union (domain_pat p1) (domain_circ c)
  | lift p f       => 
    let f' := fun dom x => union dom (domain_circ (f x)) in
    fold_left f' (all_vals _) (domain_pat p) 
  end.


Definition Disjoint (Γ1 Γ2 : OCtx) := {Γ : Ctx & Γ1 ⋓ Γ2 = Valid Γ}.
Definition Disjoint_Pattern {W} Ω (p : Pat W) : Set := Disjoint Ω (domain_pat p).
Definition Disjoint_Circuit {W} Ω (c : Circuit W) : Set := Disjoint Ω (domain_circ c).

Lemma wf_compose : forall {W W'} {Ω Γ1 Γ1' : Ctx} 
                          (c : Circuit W) (f : Pat W -> Circuit W'),
      Disjoint_Circuit Ω c   
   -> Merge Γ1 Ω Γ1' 
   -> WF_Circuit Γ1 c
   -> (forall (p : Pat W){Γ2 Γ2'}, Merge Γ2 Ω Γ2' 
                                -> WF_Pat Γ2 p -> WF_Circuit Γ2' (f p) )
   -> WF_Circuit Γ1' (compose c f).
(*Admitted.*)
Proof.
  intros W W' Ω Γ1 Γ1' c f pf_disjoint pf_merge wf_c.
  revert W' Ω Γ1' f pf_disjoint pf_merge.
  induction wf_c; intros W0 Ω Ω1' h pf_disjoint pf_merge H; simpl.
  - eapply H; eauto.
  - assert (eq1 : Γ1 ⋓ (Γ ⋓ Ω) = Ω1').
      { rewrite <- pf_merge. rewrite <- m. rewrite merge_assoc. reflexivity. }
    remember (Γ ⋓ Ω) as Ω0. destruct Ω0 as [ | Ω0]; [inversion eq1 | ].
    econstructor; [ | | eauto | eauto | ]; unfold Merge in *.
    * exact eq1.
    *
    *
    *
    
    econstructor; [ | | eauto | eauto | eapply IHwf_c; [ | eauto]];
    unfold Merge in *; eauto.
    * rewrite HeqΩ0. rewrite merge_assoc. rewrite m0.
      
(* Γ2 ⊥ Γ
         WTS: Γ2 ⊥ (Γ ⋓ Ω)
         need: Γ2 ⊥ Ω *)
      admit.
    * (* need: Γ2' ⊥ Ω *)
      admit.
  - assert (eq1 : Γ ⋓ (Γ' ⋓ Ω) = Ω1'). 
      { rewrite <- pf_merge. rewrite <- m. rewrite merge_assoc. reflexivity. }
    remember (Γ' ⋓ Ω) as Ω0. destruct Ω0 as [ | Ω0]; [inversion eq1 | ].
    econstructor; [ | eauto | intro x; eapply H0; [ | eauto] ];
    unfold Merge in *; eauto.
Admitted.