Require Import Arith.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require Import Program.
Require Import Contexts.


(* SYNTAX *)

Inductive Pat : WType -> Set :=
| unit  : Pat One
| qubit : Pat Qubit
| bit   : Pat Bit
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

Fixpoint compose {W} (c : Circuit W) : forall {W'},
                             (Pat W -> Circuit W') -> Circuit W' :=
  match c with
  | output p       => fun _ f => f p
  | gate g p1 p2 k => fun _ f => gate g p1 p2 (compose k f)
  | lift p g       => fun _ f => lift p (fun p' => compose (g p') f)
  end.


(* TYPING *) 

Definition Merge (Γ1 Γ2 Γ : Ctx) := Γ1 ⋓ Γ2 = Γ.

Inductive WF_Pat : forall {W}, Ctx -> Pat W -> Set :=
| wf_unit  : WF_Pat [] unit
| wf_qubit : forall {x Γ}, SingletonCtx x Qubit Γ -> WF_Pat Γ qubit
| wf_bit   : forall {x Γ}, SingletonCtx x Bit Γ -> WF_Pat Γ bit
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



(* should not be necessary for checking examples *)

Lemma wf_compose : forall {W W'} {Γ Γ1 Γ1'} 
                          (c : Circuit W) (f : Pat W -> Circuit W'),
      Merge Γ1 Γ Γ1' -> 
      WF_Circuit Γ1 c -> 
      (forall (p : Pat W){Γ2 Γ2'}, Merge Γ2 Γ Γ2' -> WF_Pat Γ2 p -> WF_Circuit Γ2' (f p) ) ->
      WF_Circuit Γ1' (compose c f).
Admitted.
(*
Proof.
  intros W W' Γ Γ1 Γ1' c f pf_merge wf_c.
  revert W' Γ Γ1' f pf_merge.
  induction wf_c; intros W0 Ω Ω1' h pf_merge H; simpl.
  - eapply H; eauto.
  - econstructor; [ | | eauto | eauto | ].
    Focus 3. eapply IHwf_c; [ | eauto]. 
      unfold Merge in *. admit (*?*).
    * unfold Merge in *. 
      assert (H0 : Γ1 ⋓ (Γ ⋓ Ω) = Ω1'). admit.
      destruct (merge_valid _ _ _ H0).  destruct s; destruct s0. 
      rewrite e0 in H0. exact H0.

rewrite <- pf_merge at (Valid Ω1'). instantiate (0:=Γ ⋓ Ω).

rewrite <- pf_merge at 2.

Ω1' = Γ1' ⋓ Ω = Γ1 ⋓ Γ ⋓ Ω
    *
  - 
  -
*)