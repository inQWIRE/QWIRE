Require Export Contexts.
Require Import List.
Import ListNotations.

Inductive Circuit (w : WType) : Set :=
| output : Pat w -> Circuit w
| gate   : forall {w1 w2}, 
           Gate w1 w2 ->  Pat w1 -> (Pat w2 -> Circuit w) -> Circuit w
| lift   : Pat Bit -> (bool -> Circuit w) -> Circuit w.

Inductive Box w1 w2 : Set := box : (Pat w1 -> Circuit w2) -> Box w1 w2.
Arguments output {w}.
Arguments gate {w w1 w2}.
Arguments lift {w}.
Arguments box {w1 w2}.

Definition Square_Box W := Box W W.

Definition unbox {w1 w2} (b : Box w1 w2)  (p : Pat w1) : Circuit w2 := 
  match b with box c => c p end.

Fixpoint compose {w1 w2} (c : Circuit w1) (f : Pat w1 -> Circuit w2) : Circuit w2 :=
  match c with 
  | output p     => f p
  | gate g p c'  => gate g p (fun p' => compose (c' p') f)
  | lift p c'    => lift p (fun bs => compose (c' bs) f)
  end.

(* Typed Circuits and Boxes *)

Reserved Notation "Γ ⊢ c :Circ" (at level 30).
Reserved Notation "Γ ⊢ f :Fun"  (at level 30).

Inductive Types_Circuit : Ctx -> forall {w}, Circuit w -> Set :=
| types_output : forall {Γ Γ' w} {p : Pat w} {pf : Γ = Γ'}, 
  Γ ⊢ p :Pat -> Γ' ⊢ output p :Circ
| types_gate : forall {Γ Γ1 Γ1' w1 w2 w} {f : Pat w2 -> Circuit w} 
                                    {p1 : Pat w1} {g : Gate w1 w2} ,
               Γ1 ⊢ p1 :Pat ->
               Γ ⊢ f :Fun ->
               Γ1' == Γ1 ∙ Γ ->
               Γ1' ⊢ gate g p1 f :Circ
| types_lift : forall {Γ1 Γ2 Γ w } {p : Pat Bit} {f : bool -> Circuit w},
               Γ1 ⊢ p :Pat ->
               (forall b, Γ2 ⊢ f b :Circ) ->
               Γ == Γ1 ∙ Γ2 ->
               Γ ⊢ lift p f :Circ
where "Γ ⊢ c :Circ" := (Types_Circuit Γ c)
and "Γ ⊢ f :Fun" := (forall Γ0 Γ0' p0, Γ0' == Γ0 ∙ Γ -> 
                                  Γ0 ⊢ p0 :Pat ->
                                  Γ0' ⊢ f p0 :Circ).

Definition Typed_Box {W1 W2 : WType} (b : Box W1 W2) : Set := 
  forall Γ (p : Pat W1), Γ ⊢ p :Pat -> Γ ⊢ unbox b p :Circ.

Lemma unbox_typing : forall Γ W1 W2 (p : Pat W1) (c : Box W1 W2), 
                                    Γ ⊢ p :Pat ->
                                    Typed_Box c ->
                                    Γ ⊢ unbox c p :Circ.
Proof. unfold Typed_Box in *. auto. Qed.

