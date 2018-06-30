Require Import Contexts.
Require Import HOASCircuits.
Require Import DBCircuits.

Require Import String. Open Scope string.
Require Import Reals.

Open Scope circ_scope.

Require Import TypeChecking.

Definition test_circ_3 : Box One Qubit :=
  box_ () ⇒ 
       gate_ v0 ← new0 @();
    (lift v0 (fun b0 =>
                match b0 with
                | true => gate_ v2 ← init0 @();
                            output v2
                | false => gate_ v2 ← init0 @();
                             output v2
                end)
    ).
Lemma test_circ_3_WT : Typed_Box test_circ_3.
Proof. type_check. Qed.
Definition test_circ_3_db_box := (hoas_to_db_box test_circ_3).
Definition test_circ_3_db_circ :=
  match test_circ_3_db_box with
  | db_box _ db_circ => db_circ
  end.
Lemma test_circ_3_db_circ_WT :
  Types_DB ∅ (test_circ_3_db_circ).
Proof.
  unfold test_circ_3_db_circ. simpl.
  eapply (types_db_gate ∅ ∅ ∅).
  { apply types_unit. }
  { unfold process_gate_state. simpl.
    eapply (types_db_lift (Valid [Some Bit]) (Valid [Some Bit]) (Valid [None]) ∅).
    { type_check. unfold subst_var. simpl. apply SingletonHere. }
    { destruct b.
      { unfold remove_pat. simpl. eapply (types_db_gate ∅ ∅ ∅).
        { apply types_unit. }
        { unfold process_gate_state. simpl.
          eapply types_db_output. type_check. unfold subst_var. simpl.
          apply SingletonHere. }
        { type_check. }
      }
      { unfold remove_pat. simpl. eapply (types_db_gate ∅ ∅ ∅).
        { apply types_unit. }
        { unfold process_gate_state. simpl.
          eapply types_db_output. type_check. unfold subst_var. simpl.
          apply SingletonHere. }
        { type_check. }
      }
    }
    { type_check. rewrite merge_merge'. unfold merge'. simpl. reflexivity. }
    { admit. }
  }
  { type_check. }
  Admitted.
  
Definition test_circ_4 : Box One Qubit :=
  box_ () ⇒ 
       gate_ v0 ← init0 @();
    output v0.
Lemma test_circ_4_WT : Typed_Box test_circ_4.
Proof. type_check. Qed.
Definition test_circ_4_db_box := (hoas_to_db_box test_circ_4).
Definition test_circ_4_db_circ :=
  match test_circ_4_db_box with
  | db_box _ db_circ => db_circ
  end.
Lemma test_circ_4_db_circ_WT :
  Types_DB ∅ (test_circ_4_db_circ).
Proof.
  unfold test_circ_4_db_circ. simpl.
  eapply (types_db_gate ∅ ∅ ∅).
  { apply types_unit. }
  { unfold process_gate_state. simpl.
    eapply types_db_output. type_check. unfold subst_var. simpl.
    apply SingletonHere. }
  { type_check. }
Qed.

Definition test_circ_5 : Box One Qubit :=
  box_ () ⇒ 
       gate_ v0 ← new0 @();
    (lift v0 (fun _ => gate_ v2 ← init0 @();
                         output v2)
    ).
Lemma test_circ_5_WT : Typed_Box test_circ_5.
Proof. type_check. Qed.
Definition test_circ_5_db_box := (hoas_to_db_box test_circ_5).
Definition test_circ_5_db_circ :=
  match test_circ_5_db_box with
  | db_box _ db_circ => db_circ
  end.
Lemma test_circ_5_db_circ_WT :
  Types_DB ∅ (test_circ_5_db_circ).
Proof.
  unfold test_circ_5_db_circ. simpl.
  eapply (types_db_gate ∅ ∅ ∅).
  { apply types_unit. }
  { unfold process_gate_state. simpl.
    eapply (types_db_lift (Valid [Some Bit]) (Valid [Some Bit]) (Valid [None]) ∅).
    { type_check. unfold subst_var. simpl. apply SingletonHere. }
    { intro.
      unfold remove_pat. simpl. eapply (types_db_gate ∅ ∅ ∅).
      { apply types_unit. }
      { unfold process_gate_state. simpl.
        eapply types_db_output. type_check.
        { unfold subst_var. simpl. apply SingletonHere. }
        { unfold subst_var. simpl. apply SingletonHere. }
      }
      { type_check. }
    }
    { type_check. rewrite merge_merge'. unfold merge'. simpl. reflexivity. }
    { unfold remove_pat. simpl. admit. }
  }
  { type_check. }
Admitted.

Definition test_circ_6 : Box One Qubit :=
  box_ () ⇒ 
       gate_ v0 ← new0 @();
    gate_ () ← discard @v0;
    gate_ v2 ← init0 @();
    output v2.
Lemma test_circ_6_WT : Typed_Box test_circ_6.
Proof. type_check. Qed.
Definition test_circ_6_db_box := (hoas_to_db_box test_circ_6).
Definition test_circ_6_db_circ :=
  match test_circ_6_db_box with
  | db_box _ db_circ => db_circ
  end.
Lemma test_circ_6_db_circ_WT :
  Types_DB ∅ (test_circ_6_db_circ).
Proof.
  unfold test_circ_6_db_circ. simpl.
  eapply (types_db_gate ∅ ∅ ∅).
  { apply types_unit. }
  { unfold process_gate_state. simpl.
    eapply (types_db_gate (Valid [Some Bit]) (Valid [Some Bit]) ∅).
    { type_check. unfold subst_var. simpl. apply SingletonHere. }
    { unfold process_gate_state. simpl. unfold remove_pat. simpl.
      eapply (types_db_gate (Valid [None]) ∅ (Valid [None])).
      { unfold hoas_to_db_pat. simpl. type_check. }
      { unfold process_gate_state. simpl.
        unfold hoas_to_db_pat. simpl.
        eapply types_db_output. type_check.
        unfold subst_var. simpl. admit. }
      { type_check. }
    }
    { type_check. }
  }
  { type_check. }
  Admitted.
