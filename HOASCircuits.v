Require Export Contexts.
Require Import List.
Import ListNotations.

(* n is the accumulated error *)
Inductive Circuit (n : nat) (w : WType) : Set :=
| output : Pat n w -> Circuit n w
| gate   : forall {w1 w2 n1 n2}, 
           Gate n1 w1 n2 w2 ->  Pat n1 w1 -> (Pat n2 w2 -> Circuit n w) -> Circuit n w
| lift   : forall m, Pat m Bit -> (bool -> Circuit n w) -> Circuit n w.

Inductive Box n1 w1 n2 w2 : Set :=
  box : (Pat n1 w1 -> Circuit n2 w2) -> Box n1 w1 n2 w2.

Arguments output {n w}.
Arguments gate {n w w1 w2 n1 n2}.
Arguments lift {n w m}.
Arguments box {n1 w1 n2 w2}.

Definition Square_Box n1 W n2 := Box n1 W n2 W.

Definition unbox {w1 n1 w2 n2} (b : Box n1 w1 n2 w2)  (p : Pat n1 w1) :
  Circuit n2 w2 := 
  match b with box c => c p end.

Fixpoint compose {w1 w2 n1 n2} (c : Circuit n1 w1) (f : Pat n1 w1 -> Circuit n2 w2) :
  Circuit n2 w2 :=
  match c with 
  | output p     => f p
  | gate g p c'  => gate g p (fun p' => compose (c' p') f)
  | lift p c'    => lift p (fun bs => compose (c' bs) f)
  end.

(* Typed Circuits and Boxes *)

(* Notation being uncooperative with added threshold term 

Reserved Notation "Γ ⊢ c :Circ" (at level 30).
Reserved Notation "Γ ⊢ f :Fun"  (at level 30). *)

(* nat argument is the error threshold *)
Inductive Types_Circuit : OCtx -> nat -> forall {w n}, Circuit n w -> Set :=
| types_output : forall {Γ Γ' w n} {p : Pat n w} {pf : Γ = Γ'} {t}, 
  Γ ⊢ p :Pat -> Types_Circuit Γ' t (output p)
| types_gate : forall {Γ Γ1 Γ1' w1 w2 w n n1 n2} {f : Pat n2 w2 -> Circuit n w} 
                                         {p1 : Pat n1 w1} {g : Gate n1 w1 n2 w2} {t},
               Γ1 ⊢ p1 :Pat ->
               n1 <= t ->
(* technically, we want (n1 + num errors introduced) to be at most t; this isn't
   necessarily the same as n2 (e.g. consider the EC gate) *)
               n2 <= t -> 
(*               Γ ⊢ f :Fun ->*)
               (forall Γ2 Γ2' (p2 : Pat n2 w2) {pf2 : Γ2' == Γ2 ∙ Γ},
                       Γ2 ⊢ p2 :Pat -> Types_Circuit Γ2' t (f p2)) ->
               forall {pf1 : Γ1' == Γ1 ∙ Γ},
               Types_Circuit Γ1' t (gate g p1 f)
| types_lift : forall {Γ1 Γ2 Γ w m n} {p : Pat m Bit} {f : bool -> Circuit n w} {t},
               Γ1 ⊢ p :Pat ->
               m <= t ->
               (forall b, Types_Circuit Γ2 t (f b)) ->
               forall {pf : Γ == Γ1 ∙ Γ2},
               Types_Circuit Γ t (lift p f).
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

Definition Typed_Box {W1 W2 : WType} {n1 n2 : nat} (b : Box n1 W1 n2 W2) t : Set := 
  forall Γ (p : Pat n1 W1), Γ ⊢ p :Pat -> Types_Circuit Γ t (unbox b p).


(* Prevent compute from unfolding important fixpoints *)
Opaque merge.
Opaque Ctx.
Opaque is_valid.


(* Composition lemma *)

Lemma compose_typing : forall Γ1 Γ1' Γ W W' n n'
                         (c : Circuit n W) (f : Pat n W -> Circuit n' W') t,
        Types_Circuit Γ1 t c -> 
        (forall Γ2 Γ2' (p : Pat n W) {pf2 : Γ2' == Γ2 ∙ Γ},
           Γ2 ⊢ p :Pat -> Types_Circuit Γ2' t (f p)) ->
        forall {pf : Γ1' == Γ1 ∙ Γ},
        Types_Circuit Γ1' t (compose c f).
Proof.
  intros Γ1 Γ1' Γ W W' n n' c f t.
  intros types_c.
  generalize dependent Γ1'. 
  generalize dependent Γ.
  dependent induction types_c; intros Γ0 Γ01' types_f pf0.
  * simpl. subst. eapply types_f; eauto. 
  * simpl. 
    eapply @types_gate with (Γ1 := Γ1) (Γ := Γ ⋓ Γ0); auto; try solve_merge.
    intros. 
    apply H with (Γ2 := Γ2) (Γ := Γ0) (Γ2' := Γ2 ⋓ Γ); auto; solve_merge.
  * simpl. 
    apply @types_lift with (Γ1 := Γ1) (Γ2 := Γ2 ⋓ Γ0); auto; try solve_merge.
    intros. apply H with (Γ := Γ0); auto; solve_merge.
Qed.


Lemma unbox_typing : forall Γ W1 W2 n1 n2 (p : Pat n1 W1) (c : Box n1 W1 n2 W2) t, 
                                    Γ ⊢ p :Pat ->
                                    Typed_Box c t ->
                                    Types_Circuit Γ t (unbox c p).
Proof. unfold Typed_Box in *. auto. Qed.
