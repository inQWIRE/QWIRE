Require Export Contexts.
Require Import List.
Import ListNotations.

(* n is the accumulated error *)
Inductive Circuit (w : WType) : Set :=
| output : Pat w -> Circuit w
| gate   : forall {w1 w2}, 
           Gate w1 w2 ->  Pat w1 -> (Pat w2 -> Circuit w) -> Circuit w
| lift   : Pat Bit -> (bool -> Circuit w) -> Circuit w.

Inductive Box w1 w2 : Set :=
  box : (Pat w1 -> Circuit w2) -> Box w1 w2.

Arguments output {w}.
Arguments gate {w w1 w2}.
Arguments lift {w}.
Arguments box {w1 w2}.

Definition Square_Box W := Box W W.

Definition unbox {w1 w2} (b : Box w1 w2)  (p : Pat w1) :
  Circuit w2 := 
  match b with box c => c p end.

Fixpoint compose {w1 w2} (c : Circuit w1) (f : Pat w1 -> Circuit w2) :
  Circuit w2 :=
  match c with 
  | output p     => f p
  | gate g p c'  => gate g p (fun p' => compose (c' p') f)
  | lift p c'    => lift p (fun bs => compose (c' bs) f)
  end.

(* Typed Circuits and Boxes *)

(*Reserved Notation "Γ ⊢ c :Circ" (at level 30).
Reserved Notation "Γ ⊢ f :Fun"  (at level 30).*)

(* nat argument [t] is the error threshold *)
Inductive Types_Circuit : OCtx -> nat -> forall {w}, Circuit w -> Set :=
| types_output : forall {Γ Γ' w} {p : Pat w} {pf : Γ = Γ'} {t}, 
  Γ ⊢ p :Pat -> Types_Circuit Γ' t (output p)
| types_lift : forall {Γ1 Γ2 Γ w} {p : Pat Bit} {f : bool -> Circuit w} {t},
               Γ1 ⊢ p :Pat ->
               (forall b, Types_Circuit Γ2 t (f b)) ->
               forall {pf : Γ == Γ1 ∙ Γ2},
               Types_Circuit Γ t (lift p f)
(* Different (error) typing rules for different gates - not finished (WIP) *)
| types_gate_U : forall {Γ Γ1 Γ1' w1 w} {k} {f : Pat (map_wtype w1 (k + (num_errs_wtype w1))) -> Circuit w} 
                                    {p1 : Pat w1} {u : Unitary k w1} {t},
               Γ1 ⊢ p1 :Pat ->
               k + (num_errs_wtype w1) <= t ->
               (forall Γ2 Γ2' (p2 : Pat (map_wtype w1 (k + (num_errs_wtype w1)))) {pf2 : Γ2' == Γ2 ∙ Γ},
                       Γ2 ⊢ p2 :Pat -> Types_Circuit Γ2' t (f p2)) ->
               forall {pf1 : Γ1' == Γ1 ∙ Γ},
               Types_Circuit Γ1' t (gate (U u) p1 f)
| types_gate : forall {Γ Γ1 Γ1' w1 w2 w} {f : Pat w2 -> Circuit w} 
                                    {p1 : Pat w1} {g : Gate w1 w2} {t},
               Γ1 ⊢ p1 :Pat ->
               num_errs_wtype w1 <= t ->
               num_errs_wtype w2 <= t ->
               (forall Γ2 Γ2' (p2 : Pat w2) {pf2 : Γ2' == Γ2 ∙ Γ},
                       Γ2 ⊢ p2 :Pat -> Types_Circuit Γ2' t (f p2)) ->
               forall {pf1 : Γ1' == Γ1 ∙ Γ},
               Types_Circuit Γ1' t (gate g p1 f).

(*where "Γ ⊢ c :Circ" := (Types_Circuit Γ c)
and "Γ ⊢ f :Fun" := (forall Γ0 Γ0' p0, Γ0' == Γ0 ∙ Γ ->
                                            Γ0 ⊢ p0 :Pat ->
                                            Γ0' ⊢ f p0 :Circ ).*)

(* Notation "Γ ⊢_Q c : w" := (@Types_Circuit Γ w c) (at level 30). *)
(* Notation "Γ ⇒_Q p : w" := (@Types_Pat Γ w p) (at level 30). *)

(*
| types_lift_qubit : forall {Γ1 Γ2 p Γ w f} {v : is_valid Γ} {m : Γ = Γ1 ⋓ Γ2},     
                     Types_Pat Γ1 p Qubit -> 
                     (forall b, Types_Circuit Γ2 (f b) w) ->
                     Types_Circuit Γ (lift p f) w.
*)
(*
Notation "Γ ⊢ c :Circ" := (Types_Circuit Γ c) (at level 30).
Notation "Γ ⊢ f :Fun" := (forall Γ0 Γ0' p0, Γ0' == Γ0 ∙ Γ ->
                                            Γ0 ⊢ p0 :Pat ->
                                            Γ0' ⊢ f p0 :Circ ) (at level 30).
*)

Print Types_Circuit.

Definition Typed_Box {W1 W2 : WType} (b : Box W1 W2) t : Set := 
  forall Γ (p : Pat W1), Γ ⊢ p :Pat -> Types_Circuit Γ t (unbox b p).


(* Prevent compute from unfolding important fixpoints *)
Opaque merge.
Opaque Ctx.
Opaque is_valid.


(* Composition lemma *)

Lemma compose_typing : forall Γ1 Γ1' Γ W W'
                         (c : Circuit W) (f : Pat W -> Circuit W') t,
        Types_Circuit Γ1 t c -> 
        (forall Γ2 Γ2' (p : Pat W) {pf2 : Γ2' == Γ2 ∙ Γ},
           Γ2 ⊢ p :Pat -> Types_Circuit Γ2' t (f p)) ->
        forall {pf : Γ1' == Γ1 ∙ Γ},
        Types_Circuit Γ1' t (compose c f).
Proof.
  intros Γ1 Γ1' Γ W W' c f t.
  intros types_c.
  generalize dependent Γ1'. 
  generalize dependent Γ.
  dependent induction types_c; intros Γ0 Γ01' types_f pf0.
  * simpl. subst. eapply types_f; eauto. 
  * simpl. 
    apply @types_lift with (Γ1 := Γ1) (Γ2 := Γ2 ⋓ Γ0); auto; try solve_merge.
    intros. apply H with (Γ := Γ0); auto; solve_merge.
  * simpl. 
    eapply @types_gate_U with (Γ1 := Γ1) (Γ := Γ ⋓ Γ0); auto; try solve_merge.
    intros. 
    apply H with (Γ2 := Γ2) (Γ := Γ0) (Γ2' := Γ2 ⋓ Γ); auto; solve_merge.
  * simpl. 
    eapply @types_gate with (Γ1 := Γ1) (Γ := Γ ⋓ Γ0); auto; try solve_merge.
    intros. 
    apply H with (Γ2 := Γ2) (Γ := Γ0) (Γ2' := Γ2 ⋓ Γ); auto; solve_merge.  
Qed.


Lemma unbox_typing : forall Γ W1 W2 (p : Pat W1) (c : Box W1 W2) t, 
                                    Γ ⊢ p :Pat ->
                                    Typed_Box c t ->
                                    Types_Circuit Γ t (unbox c p).
Proof. unfold Typed_Box in *. auto. Qed.
