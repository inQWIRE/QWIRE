Require Import Denotation.

Open Scope matrix_scope.

(* Propositional version (in Set). Could also just have a unitary circuit type and a 
   (trivial) coercion from circuit. *)
Inductive Unitary_Circuit {W} : Circuit W -> Set :=
| u_output : forall p, Unitary_Circuit (output p)
| u_gate : forall W' c (u : Unitary W') p,
    (forall p', Unitary_Circuit (c p')) ->
    Unitary_Circuit (gate (U u) p c).

Definition Unitary_Box {W} (b : Box W W) : Set :=
  match b with
  | box c => forall p, (Unitary_Circuit (c p))
  end.

Inductive Unitary_DB_Circuit {W} : DeBruijn_Circuit W -> Set :=
| u_db_output : forall p, Unitary_DB_Circuit (db_output p)
| u_db_gate : forall W' c (u : Unitary W') p,
    Unitary_DB_Circuit c ->
    Unitary_DB_Circuit (db_gate (U u) p c).

Definition Unitary_DB_Box {W} (b : DeBruijn_Box W W) : Set :=
  match b with
  | db_box _ c => Unitary_DB_Circuit c
  end.

Definition apply_unitary {W} (n : nat) (U : Unitary W) (li : list nat) : Square (2^n) :=
  match W with
  | Qubit => let k := (hd O li) in
            I (2^k) ⊗ ⟦U⟧ ⊗ I (2 ^ (n - k -1))
  | _     => denote_ctrls n U li
  end.

(*
apply_U = 
fun (W : WType) (n : nat) (U : Unitary W) (l : list nat) =>
match W with
| Qubit => apply_to_first (apply_qubit_unitary (⟦ U ⟧)) l
| _ => super (denote_ctrls n U l)
end
     : forall (W : WType) (n : nat), Unitary W -> list nat -> Superoperator (2 ^ n) (2 ^ n)
*)

Fixpoint denote_u_db_circuit {W} n (c : DeBruijn_Circuit W) (pf : Unitary_DB_Circuit c)
                         : Square (2^n) :=
  match pf with
  | u_db_output p => pad n (⟦p⟧)
  | u_db_gate W' c u p pf' => (denote_u_db_circuit n c pf') × (apply_unitary n u (pat_to_list p))
  end.

(*
Fixpoint denote_u_db_circuit {w} n (c : DeBruijn_Circuit w) (pf : Unitary_DB_Circuit c)
                         : Square (2^n) :=
  match c with
  | db_output p    => pad n (⟦p⟧)
  | db_gate g p c' => match g with
                              | U u => (denote_u_db_circuit n c') ×
                                      (apply_unitary n u (pat_to_list p))
                              | _ => IDProp
                              end
  | _              => IDProp
  end.
*)

Print Unitary_DB_Box.

Definition denote_db_box {W} (b : DeBruijn_Box W W) (pf : Unitary_DB_Box b) : Square (2^⟦W⟧).
  unfold Unitary_DB_Box in pf.
  destruct b.
  exact (denote_u_db_circuit (⟦W⟧) d pf).
Defined.

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
    apply u0.
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

