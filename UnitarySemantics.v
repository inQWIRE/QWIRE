Require Import Denotation.

Open Scope matrix_scope.

(* Propositional version (in Set). Could also just have a unitary circuit type and a 
   (trivial) coercion from circuit. *)
Inductive Unitary_Circuit {W} : Circuit W -> Prop :=
| u_output : forall p, Unitary_Circuit (output p)
| u_gate : forall W' c (u : Unitary W') p,
    (forall p', Unitary_Circuit (c p')) ->
    Unitary_Circuit (gate (U u) p c).

Definition Unitary_Box {W} (b : Box W W) : Prop :=
  match b with
  | box c => forall p, (Unitary_Circuit (c p))
  end.

Inductive Unitary_DB_Circuit {W} : DeBruijn_Circuit W -> Prop :=
| u_db_output : forall p, Unitary_DB_Circuit (db_output p)
| u_db_gate : forall W' c (u : Unitary W') p,
    Unitary_DB_Circuit c ->
    Unitary_DB_Circuit (db_gate (U u) p c).

Definition Unitary_DB_Box {W} (b : DeBruijn_Box W W) : Prop :=
  match b with
  | db_box _ c => Unitary_DB_Circuit c
  end.

Fixpoint denote_u_db_circuit {W} n (c : DeBruijn_Circuit W) : Square (2^n) :=
  match c with
  | db_output p => pad n (⟦p⟧)
  | db_gate g p c  => match g with
                     | U u => (denote_u_db_circuit n c) × (apply_unitary n u (pat_to_list p))
                     | _   => dummy_mat
                     end
  | _   => dummy_mat
  end.

Definition denote_u_db_box {W} (c : DeBruijn_Box W W) : Square (2^⟦W⟧) :=
  match c with
  | db_box _ c' => denote_u_db_circuit (⟦W⟧) c' 
  end.

Lemma unitary_to_db : forall W Γ (c : Circuit W) , Unitary_Circuit c -> Unitary_DB_Circuit (hoas_to_db Γ c).
Proof.
  intros W Γ c U.
  gen Γ.
  induction c; intros.
  - simpl. constructor.
  - simpl.
    destruct (process_gate g p Γ) eqn:E.
    dependent destruction U.
    constructor. 
    apply H.
    apply H0.
  - inversion U.
Qed.

Lemma unitary_box_to_db : forall W (c : Box W W) , Unitary_Box c -> Unitary_DB_Box (hoas_to_db_box c).
Proof.
  intros W c U.
  unfold Unitary_Box, Unitary_DB_Box in *.
  destruct c; simpl in *.
  destruct (add_fresh W []).
  apply unitary_to_db.
  apply U.
Qed.

(*
denote_circuit

Definition denote_unitary_circuit {W} 
*)

Definition denote_unitary_box {W} (c : Box W W) :=
  denote_u_db_box (hoas_to_db_box c).

Lemma denote_unitary_box_eq : forall W safe (c : Box W W) ρ,
    Unitary_Box c ->
    denote_box safe c ρ = denote_unitary_box c × ρ × (denote_unitary_box c)†.
Proof.
  intros W safe [c] ρ pf.
  simpl in pf.
  unfold denote_unitary_box, denote_box.
  unfold denote_db_box.
  unfold hoas_to_db_box.
  destruct (add_fresh W []) as [p Γ].
  specialize (pf p).
  gen ρ.
  induction (c p).
  - reflexivity.
  - intros ρ.
    simpl.
    dependent destruction pf.
    simpl.
    unfold compose_super, super.
    rewrite Nat.add_sub.
    rewrite H0 by auto.
    unfold denote_u_db_box.
    simpl.
    unfold apply_U, super.
    rewrite Mmult_adjoint.
    repeat rewrite Mmult_assoc.
    reflexivity.
  - inversion pf.
Qed.
    
