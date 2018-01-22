Require Import Denotation.
Require Import TypeChecking.

(*************************)
(* Assertion Correctness *)
(*************************)

Inductive ancilla_free {W} : Circuit W -> Prop := 
  | af_output : forall p, ancilla_free (output p)
  | af_gate : forall g p c', g <> assert0 -> 
                        g <> assert1 -> 
                        (forall p, ancilla_free (c' p)) -> 
                        ancilla_free (gate g p c').

(* Replace given ancilla with an if statement to be filled with a dummy *)
Fixpoint swap_ancilla (loc : nat)  {W} (c dummy : Circuit W) := 
  match loc with 
  (* replace here *)
  | O => match c with 
        | gate assert0 p c' => gate meas p (fun p' => lift p' 
                                             (fun b => if b then dummy else c' unit ))
        | gate assert1 p c' => gate meas p (fun p' => lift p' 
                                             (fun b => if b then c' unit else dummy))
        | c''               => c''
        end
  (* replace later *)
  | S n' => match c with 
           | output p  => output p (* index does not exist *)
           | gate g p c' => gate g p (fun p' => swap_ancilla n' (c' p') dummy)
           | lift p c' => lift p (fun b => swap_ancilla n' (c' b) dummy)
           end
  end.

(*
Fixpoint swap_ancilla (loc : nat)  {W W'} (c : Circuit W) (dummy : Circuit W') := 
  match c with 
  | output p => output p
  | gate g p c' => match g with 
                  | assert0 => gate meas p (fun p' => lift p' 
                                             (fun b => if b then dummy else c' p'))
                  | assert1 => gate meas p (fun p' => lift p' 
                                             (fun b => if b then c' p' else dummy))
                  | _ => gate g p c''
                  end
  end.

Program Fixpoint swap_ancillae {W W'} (c : Circuit W) (dummy : Circuit W') :=
  match c with 
  | output p    => output p
  | gate g p c' => let c'' := (fun p' => swap_ancillae (c' p') dummy) in 
                  match g with 
                  | assert0 => gate meas p (fun p' => lift p' 
                                             (fun b => if b then dummy else c'' p'))
                  | assert1 => gate meas p (fun p' => lift p' 
                                             (fun b => if b then c'' p' else dummy))
                  | _ => gate g p c''
                  end
  end.

*)

Definition swap_box_ancilla loc {W1 W2} (b : Box W1 W2) dummy :=
  match b with
  | box c => box (fun p => swap_ancilla loc (c p) dummy)
  end.

Definition Assertion_Correct {W1 W2} (c : Box W1 W2) := forall loc dummy, 
    c ≡ swap_box_ancilla loc c dummy.

Lemma id_correct : forall W, Assertion_Correct (box (fun (p : Pat W) => output p)).
Proof.
  intros W n dummy ρ Mρ.
  induction n; simpl; reflexivity.
Qed.

Lemma ancilla_free_correct : forall W (c : Circuit W), ancilla_free c -> 
                             Assertion_Correct (box (fun (p : Pat W) => c)).
Proof.
  intros W c AF n dummy ρ Mρ.
  induction AF as [|g p c' a0 a1 AF IH].
  + simpl. destruct n; reflexivity.
  + simpl.
    destruct n.
    - replace (swap_ancilla 0 (gate g p c') dummy) with (gate g p c').
      reflexivity.
      dependent destruction g.
      contradiction.
      contradiction.
    - (* true for the continuation from IH *)
      simpl in *.    
      unfold denote_box in *.
      simpl in *.
      unfold compose_super.
Admitted.

Definition init_assert0 :=
  box (fun (_ : Pat One) => 
    gate_ p  ← init0 @();
    gate_ () ← assert0 @p;
    output ()).

Lemma init_assert_correct0 :  Assertion_Correct init_assert0. 
Proof.  
  intros loc dummy ρ Mρ.
  simpl.
  unfold init_assert0.
  destruct loc.
  + simpl. reflexivity.
  + destruct loc. simpl.
    repeat (simpl; autounfold with den_db).
    apply mixed_state_id1 in Mρ. subst.
    Msimpl.
    repeat match goal with 
    | [ |- context[?A : Matrix ?m ?n]] => reduce_aux A
    | [e := _ : C |- _] => unfold e; clear e 
    end.
    unfold Splus.
    cbn.

Arguments Zero {m n}.

Lemma denote_zero : forall W pad input c, @denote_db_circuit W pad input c Zero = Zero.
Proof.
  intros W pad input c.
  induction c.
  + unfold denote_db_circuit.
    repeat (simpl; autounfold with den_db).
    Msimpl.
    rewrite Mmult_0_r.
    rewrite Mmult_0_l.
    reflexivity.
  + unfold denote_db_circuit.
    repeat (simpl; autounfold with den_db).
    Msimpl.
    rewrite Mmult_0_r.
    rewrite Mmult_0_l.
    reflexivity.
    
    Msimpl.
    simpl.