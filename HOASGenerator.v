From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Contexts.
Require Import HOASCircuits.
Require Import DBCircuits.
Require Import Generator.
Require Import DBGenerator.
Require Import TypeChecking.
Require Import HOASLib.

Require Import String. Open Scope string.
Require Import Reals.

Open Scope circ_scope.

(* HOASCircuit 
Inductive Circuit (w : WType) : Set :=
| output : Pat w -> Circuit w
| gate   : forall {w1 w2}, 
           Gate w1 w2 ->  Pat w1 -> (Pat w2 -> Circuit w) -> Circuit w
| lift   : Pat Bit -> (bool -> Circuit w) -> Circuit w.
*)
Fixpoint get_new_pat_of (w : WType) (v : nat) : Pat w :=
  match w with
  | Qubit => qubit v
  | Bit => bit v
  | One => unit
  | Tensor l r => let v' := (v + (size_wtype l)) in
                  pair (get_new_pat_of l v) (get_new_pat_of r v')
  end.
Instance showCircuit {w} : Show (Circuit w) :=
  {| show :=
       let fix aux v t :=
           match t with
           | output p => "output (" ++ (show p) ++ ")"
           | gate w1 w2 g p t' => let nv := (v + (size_wtype w2)) in
                                  "gate (" ++ (show g) ++ ") (" ++ (show p) ++ ") ("
                                           ++ "fun (" ++ (show (get_new_pat_of w2 v))
                                           ++ ") => (" ++ (aux nv (t' (get_new_pat_of w2 v)))
                                           ++ "))"
           | lift b f =>
             "lift (" ++ (show b) ++ ") ("
                      ++ (aux v (f true)) ++ ") ("
                      ++ (aux v (f true)) ++ ")"
           end
       in (aux O)
  |}.
Eval compute in (show (output (pair (qubit 1) (bit 0)))).

(* HOASBox 
Inductive Box w1 w2 : Set := box : (Pat w1 -> Circuit w2) -> Box w1 w2.
*)
Instance showBox {w1 w2} : Show (Box w1 w2) :=
  {| show :=
       let fix aux_circ v t :=
           match t with
           | output p => "output (" ++ (show p) ++ ")"
           | gate w1 w2 g p t' => let nv := (v + (size_wtype w2)) in
                                  "gate (" ++ (show g) ++ ") (" ++ (show p) ++ ") ("
                                           ++ "fun (" ++ (show (get_new_pat_of w2 v))
                                           ++ ") => (" ++ (aux_circ nv (t' (get_new_pat_of w2 v)))
                                           ++ "))"
           | lift b f =>
             "lift (" ++ (show b) ++ ") ("
                      ++ (aux_circ v (f true)) ++ ") ("
                      ++ (aux_circ v (f true)) ++ ")"
           end
       in 
       let fix aux_box t :=
           match t with
           | box c => let sv := (size_wtype w1) in
                      "box (" ++ "fun (" ++ (show (get_new_pat_of w1 0)) ++ ") => ("
                              ++ (aux_circ sv (c (get_new_pat_of w1 0)))
                               ++ "))"
           end
       in aux_box
  |}.

Definition test_circ : Box One Qubit :=
  box_ () ⇒  
    gate_ a0 ← init0 @();
    gate_ a ← _H @a0;
    gate_ b ← init0 @();
    gate_ (a1, b1) ← CNOT @(Contexts.pair a b);
    gate_ b2       ← meas @(b1);
    gate_ ()       ← discard @(b2);   
    output a1.
Eval compute in (show test_circ).

Definition bell00 : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒  
    gate_ a0 ← init0 @();
    gate_ a ← _H @a0;
    gate_ b ← init0 @();
    gate_ (a1, b1) ← CNOT @(Contexts.pair a b);
    output (Contexts.pair a1 b1).
Eval compute in (show bell00).

Definition test_circ_2 : Box One Qubit :=
  box_ () ⇒ 
       gate_ v0 ← new0 @();
    (lift v0 (fun b0 =>
                match b0 with
                | true => gate_ v1 ← new0 @();
                            (lift v1 (fun b1 => match b1 with
                                                | true => gate_ v2 ← init0 @();
                                                            output v2
                                                | false => gate_ v2 ← init0 @();
                                                             output v2
                                                end)
                            )
                | false => gate_ v1 ← new0 @();
                             (lift v1 (fun b1 => match b1 with
                                                 | true => gate_ v2 ← init0 @();
                                                             output v2
                                                 | false => gate_ v2 ← init0 @();
                                                              output v2
                                                 end)
                             )
                end)
    ).
Eval compute in (show test_circ_2).
Definition test_circ_2_db_box := (hoas_to_db_box test_circ_2).
Definition test_circ_2_db_circ :=
  match test_circ_2_db_box with
  | db_box db_circ => db_circ
  end.
Eval compute in (show test_circ_2_db_circ).

(* Too Slow !
Fail Eval compute in test_circ_2_denotation.
*)

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
Definition test_circ_3_db_box := (hoas_to_db_box test_circ_3).
Definition test_circ_3_db_circ :=
  match test_circ_3_db_box with
  | db_box db_circ => db_circ
  end.
Eval compute in (show test_circ_3_db_circ).

Definition test_circ_4 : Box One Qubit :=
  box_ () ⇒ 
       gate_ v0 ← init0 @();
    output v0.
Definition test_circ_4_db_box := (hoas_to_db_box test_circ_4).
Definition test_circ_4_db_circ :=
  match test_circ_4_db_box with
  | db_box db_circ => db_circ
  end.
Eval compute in (show test_circ_4_db_circ).

Definition test_circ_5 : Box One Qubit :=
  box_ () ⇒ 
       gate_ v0 ← new0 @();
    (lift v0 (fun _ => gate_ v2 ← init0 @();
                         output v2)
    ).
Definition test_circ_5_db_box := (hoas_to_db_box test_circ_5).
Definition test_circ_5_db_circ :=
  match test_circ_5_db_box with
  | db_box db_circ => db_circ
  end.
Eval compute in (show test_circ_5_db_circ).

Definition test_circ_6 : Box One Qubit :=
  box_ () ⇒ 
       gate_ v0 ← new0 @();
    gate_ () ← discard @v0;
    gate_ v2 ← init0 @();
    output v2.
Definition test_circ_6_db_box := (hoas_to_db_box test_circ_6).
Definition test_circ_6_db_circ :=
  match test_circ_6_db_box with
  | db_box db_circ => db_circ
  end.
Eval compute in (show test_circ_6_db_circ).

(* WTypeMatch *)
Inductive WTypeMatch : WType -> WType -> Set :=
| match_none        : WTypeMatch One One
| match_unitary (uw : UnitaryWType) : 
    WTypeMatch (UnitaryWType_to_WType uw) (UnitaryWType_to_WType uw) (* Unitary *)
| match_bit_bit     : WTypeMatch Bit Bit (* BNOT, id *)
| match_one_qubit   : WTypeMatch One Qubit (* init0, init1 *)
| match_one_bit     : WTypeMatch One Bit (* new0, new1 *)
| match_qubit_bit   : WTypeMatch Qubit Bit (* meas *)
| match_qubit_qubit : WTypeMatch Qubit Qubit (* measQ, Unitary, id *)
| match_bit_one     : WTypeMatch Bit One (* discard *)
| match_bit_qubit   : WTypeMatch Bit Qubit (* init0 nv -> bit_ctrl bit nv
                                              -> discard bit -> output nv *)
| match_qubit_one   : WTypeMatch Qubit One (* meas -> discard (maybe, assert0, assert1) *)
| match_l_w2 : forall {w1l w2 w1r : WType},
    WTypeMatch w1l w2 -> WTypeMatch w1r One -> WTypeMatch (Tensor w1l w1r) w2
| match_r_w2 : forall {w1r w2 w1l : WType},
    WTypeMatch w1r w2 -> WTypeMatch w1l One -> WTypeMatch (Tensor w1l w1r) w2
| match_w1_l : forall {w1 w2l w2r : WType},
    WTypeMatch w1 w2l -> WTypeMatch One w2r -> WTypeMatch w1 (Tensor w2l w2r)
| match_w1_r : forall {w1 w2r w2l : WType},
    WTypeMatch w1 w2r -> WTypeMatch One w2l -> WTypeMatch w1 (Tensor w2l w2r)
| match_w1_w2 : forall {w1l w1r w2l w2r : WType},
    WTypeMatch w1l w2l -> WTypeMatch w1r w2r -> WTypeMatch (Tensor w1l w1r) (Tensor w2l w2r)
.

Instance showWTypeMatch {w1 w2 : WType} : Show (WTypeMatch w1 w2) :=
  {| show := 
       let fix aux {w1 w2} t :=
           match t with
           | match_none        => "match (One - One)"
           | match_unitary uw =>
             "match ((" ++ (show (UnitaryWType_to_WType uw)) ++ ") - ("
                        ++ (show (UnitaryWType_to_WType uw)) ++ ")"
           | match_bit_bit     => "match (Bit - Bit)"
           | match_one_qubit   => "match (One - Qubit)"
           | match_one_bit     => "match (One - Bit)"
           | match_qubit_bit   => "match (Qubit - Bit)"
           | match_qubit_qubit => "match (Qubit - Qubit)"
           | match_bit_one     => "match (Bit - One)"
           | match_bit_qubit   => "match (Bit - Qubit)"
           | match_qubit_one   => "match (Qubit - One)"
           | match_l_w2 _ _ w1r m1 m2 => "match (" ++ (aux m1) ++ ") ("
                                                   ++ (@aux w1r One m2) ++ ")"
           | match_r_w2 _ _ _ m1 m2 => "match (" ++ (aux m2) ++ ") (" ++ (aux m1) ++ ")"
           | match_w1_l _ _ _ m1 m2 => "match (" ++ (aux m1) ++ ") (" ++ (aux m2) ++ ")"
           | match_w1_r _ _ _ m1 m2 => "match (" ++ (aux m2) ++ ") (" ++ (aux m1) ++ ")"
           | match_w1_w2 _ _ _ _ m1 m2 => "match (" ++ (aux m1) ++ ") ("
                                                    ++ (aux m2) ++ ")"
           end
       in aux
  |}.
(*
Inductive GeneralWTypeMatchLeftOne :=
| general_match_left_one_none   : GeneralWTypeMatchLeftOne
| general_match_left_one_bit    : GeneralWTypeMatchLeftOne
| general_match_left_one_qubit  : GeneralWTypeMatchLeftOne
| general_match_left_one_tensor :
    GeneralWTypeMatchLeftOne -> GeneralWTypeMatchLeftOne -> GeneralWTypeMatchLeftOne
.
Fixpoint GeneralWTypeMatchLeftOne_to_WType (gwm : GeneralWTypeMatchLeftOne) : WType :=
  match gwm with
  | general_match_left_one_none         => One
  | general_match_left_one_bit          => Bit
  | general_match_left_one_qubit        => Qubit
  | general_match_left_one_tensor m1 m2 =>
    (Tensor (GeneralWTypeMatchLeftOne_to_WType m1) (GeneralWTypeMatchLeftOne_to_WType m2))
  end.
Check GeneralWTypeMatchLeftOne_to_WType.
Fixpoint GeneralWTypeMatchLeftOne_to_WTypeMatch (gwm : GeneralWTypeMatchLeftOne)
  : WTypeMatch One (GeneralWTypeMatchLeftOne_to_WType gwm)
  :=
    match gwm with
    | general_match_left_one_none         => match_none
    | general_match_left_one_bit          => match_one_bit
    | general_match_left_one_qubit        => match_one_qubit
    | general_match_left_one_tensor m1 m2 =>
      (@match_w1_l One
                   (GeneralWTypeMatchLeftOne_to_WType m1)
                   (GeneralWTypeMatchLeftOne_to_WType m2)
                   (GeneralWTypeMatchLeftOne_to_WTypeMatch m1)
                   (GeneralWTypeMatchLeftOne_to_WTypeMatch m2))
    end.
Check GeneralWTypeMatchLeftOne_to_WTypeMatch.
Fixpoint genGeneralWTypeMatchLeftOne (w2 : WType) : G (GeneralWTypeMatchLeftOne) :=
  match w2 with
  | One => returnGen general_match_left_one_none
  | Bit => returnGen general_match_left_one_bit
  | Qubit => returnGen general_match_left_one_qubit
  | Tensor l r => liftGen2 general_match_left_one_tensor
                           (genGeneralWTypeMatchLeftOne l) (genGeneralWTypeMatchLeftOne r)
  end.

Inductive GeneralWTypeMatchRightOne :=
| general_match_right_one_none   : GeneralWTypeMatchRightOne
| general_match_right_one_bit    : GeneralWTypeMatchRightOne
| general_match_right_one_qubit  : GeneralWTypeMatchRightOne
| general_match_right_one_tensor :
    GeneralWTypeMatchRightOne -> GeneralWTypeMatchRightOne -> GeneralWTypeMatchRightOne
.
Fixpoint GeneralWTypeMatchRightOne_to_WType (gwm : GeneralWTypeMatchRightOne) : WType :=
  match gwm with
  | general_match_right_one_none         => One
  | general_match_right_one_bit          => Bit
  | general_match_right_one_qubit        => Qubit
  | general_match_right_one_tensor m1 m2 =>
    (Tensor (GeneralWTypeMatchRightOne_to_WType m1) (GeneralWTypeMatchRightOne_to_WType m2))
  end.
Check GeneralWTypeMatchRightOne_to_WType.
Fixpoint GeneralWTypeMatchRightOne_to_WTypeMatch (gwm : GeneralWTypeMatchRightOne)
  : WTypeMatch (GeneralWTypeMatchRightOne_to_WType gwm) One
  :=
    match gwm with
    | general_match_right_one_none         => match_none
    | general_match_right_one_bit          => match_bit_one
    | general_match_right_one_qubit        => match_qubit_one
    | general_match_right_one_tensor m1 m2 =>
      (@match_l_w2 (GeneralWTypeMatchRightOne_to_WType m1)
                   One
                   (GeneralWTypeMatchRightOne_to_WType m2)
                   (GeneralWTypeMatchRightOne_to_WTypeMatch m1)
                   (GeneralWTypeMatchRightOne_to_WTypeMatch m2))
    end.
Check GeneralWTypeMatchRightOne_to_WTypeMatch.
Fixpoint genGeneralWTypeMatchRightOne (w1 : WType) : G (GeneralWTypeMatchRightOne) :=
  match w1 with
  | One => returnGen general_match_right_one_none
  | Bit => returnGen general_match_right_one_bit
  | Qubit => returnGen general_match_right_one_qubit
  | Tensor l r => liftGen2 general_match_right_one_tensor
                           (genGeneralWTypeMatchRightOne l) (genGeneralWTypeMatchRightOne r)
  end.

Inductive GeneralWTypeMatch :=
| general_match_none        : GeneralWTypeMatch
| general_match_unitary     : UnitaryWType -> GeneralWTypeMatch (* Unitray *)
| general_match_bit_bit     : GeneralWTypeMatch (* BNOT *)
| general_match_one_qubit   : GeneralWTypeMatch (* init0, init1 *)
| general_match_one_bit     : GeneralWTypeMatch (* new0, new1 *)
| general_match_qubit_bit   : GeneralWTypeMatch (* meas *)
| general_match_qubit_qubit : GeneralWTypeMatch (* measQ, Unitary *)
| general_match_bit_one     : GeneralWTypeMatch (* discard *)
| general_match_bit_qubit   : GeneralWTypeMatch (* init0 nv -> bit_ctrl bit nv
                                                -> discard bit -> output nv *)
| general_match_qubit_one   : GeneralWTypeMatch (* meas -> discard (or, assert0, assert1) *)
| general_match_l_w2        :
    GeneralWTypeMatch -> GeneralWTypeMatchRightOne -> GeneralWTypeMatch
| general_match_r_w2        :
    GeneralWTypeMatch -> GeneralWTypeMatchRightOne -> GeneralWTypeMatch
| general_match_w1_l        :
    GeneralWTypeMatch -> GeneralWTypeMatchLeftOne -> GeneralWTypeMatch
| general_match_w1_r        :
    GeneralWTypeMatch -> GeneralWTypeMatchLeftOne -> GeneralWTypeMatch
| general_match_w1_w2       : GeneralWTypeMatch -> GeneralWTypeMatch -> GeneralWTypeMatch
.

Fixpoint GeneralWTypeMatch_to_WType (gwm : GeneralWTypeMatch) : WType * WType :=
  match gwm with
  | general_match_none        => (Datatypes.pair One One)
  | general_match_unitary uw  => (Datatypes.pair (UnitaryWType_to_WType uw)
                                                 (UnitaryWType_to_WType uw))
  | general_match_bit_bit     => (Datatypes.pair Bit Bit)
  | general_match_one_qubit   => (Datatypes.pair One Qubit)
  | general_match_one_bit     => (Datatypes.pair One Bit)
  | general_match_qubit_bit   => (Datatypes.pair Qubit Bit)
  | general_match_qubit_qubit => (Datatypes.pair Qubit Qubit)
  | general_match_bit_one     => (Datatypes.pair Bit One)
  | general_match_bit_qubit   => (Datatypes.pair Bit Qubit)
  | general_match_qubit_one   => (Datatypes.pair Qubit One)
  | general_match_l_w2 m1 m2  =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w2 := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (GeneralWTypeMatchRightOne_to_WType m2) in
    (Datatypes.pair (Tensor w1l w1r) w2)
  | general_match_r_w2 m1 m2  =>
    let w1r := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w2 := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w1l := (GeneralWTypeMatchRightOne_to_WType m2) in
    (Datatypes.pair (Tensor w1l w1r) w2)
  | general_match_w1_l m1 m2  =>
    let w1 := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w2l := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2r := (GeneralWTypeMatchLeftOne_to_WType m2) in
    (Datatypes.pair w1 (Tensor w2l w2r))
  | general_match_w1_r m1 m2  =>
    let w1 := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w2r := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2l := (GeneralWTypeMatchLeftOne_to_WType m2) in
    (Datatypes.pair w1 (Tensor w2l w2r))
  | general_match_w1_w2 m1 m2 =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w2l := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (fst (GeneralWTypeMatch_to_WType m2)) in
    let w2r := (snd (GeneralWTypeMatch_to_WType m2)) in
    (Datatypes.pair (Tensor w1l w1r) (Tensor w2l w2r))
  end.
Check GeneralWTypeMatch_to_WType.
Check (fst (GeneralWTypeMatch_to_WType general_match_none)).
Fixpoint GeneralWTypeMatch_to_WTypeMatch (gwm : GeneralWTypeMatch)
  : WTypeMatch (fst (GeneralWTypeMatch_to_WType gwm)) (snd (GeneralWTypeMatch_to_WType gwm))
  :=
  match gwm with
  | general_match_none        => match_none
  | general_match_unitary uw  => match_unitary uw
  | general_match_bit_bit     => match_bit_bit
  | general_match_one_qubit   => match_one_qubit
  | general_match_one_bit     => match_one_bit
  | general_match_qubit_bit   => match_qubit_bit
  | general_match_qubit_qubit => match_qubit_qubit
  | general_match_bit_one     => match_bit_one
  | general_match_bit_qubit   => match_bit_qubit
  | general_match_qubit_one   => match_qubit_one
  | general_match_l_w2 m1 m2  =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w2 := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (GeneralWTypeMatchRightOne_to_WType m2) in
    @match_l_w2 w1l w2 w1r
                (GeneralWTypeMatch_to_WTypeMatch m1)
                (GeneralWTypeMatchRightOne_to_WTypeMatch m2)
  | general_match_r_w2 m1 m2  =>
    let w1r := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w2 := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w1l := (GeneralWTypeMatchRightOne_to_WType m2) in
    @match_r_w2 w1r w2 w1l
                (GeneralWTypeMatch_to_WTypeMatch m1)
                (GeneralWTypeMatchRightOne_to_WTypeMatch m2)
  | general_match_w1_l m1 m2  =>
    let w1 := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w2l := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2r := (GeneralWTypeMatchLeftOne_to_WType m2) in
    @match_w1_l w1 w2l w2r
                (GeneralWTypeMatch_to_WTypeMatch m1)
                (GeneralWTypeMatchLeftOne_to_WTypeMatch m2)
  | general_match_w1_r m1 m2  =>
    let w1 := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w2r := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2l := (GeneralWTypeMatchLeftOne_to_WType m2) in
    @match_w1_r w1 w2r w2l
                (GeneralWTypeMatch_to_WTypeMatch m1)
                (GeneralWTypeMatchLeftOne_to_WTypeMatch m2)
  | general_match_w1_w2 m1 m2 =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w2l := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (fst (GeneralWTypeMatch_to_WType m2)) in
    let w2r := (snd (GeneralWTypeMatch_to_WType m2)) in
    @match_w1_w2 w1l w1r w2l w2r
                 (GeneralWTypeMatch_to_WTypeMatch m1) (GeneralWTypeMatch_to_WTypeMatch m2)
  end.
Check GeneralWTypeMatch_to_WTypeMatch.

Fixpoint genGeneralWTypeMatchRec (step : nat) (w1 : WType) (w2 : WType)
  : G (GeneralWTypeMatch) :=
  match step with
  | O => returnGen general_match_none
  | S step' =>
    match w1, w2 with
    | One, One => returnGen general_match_none
    | One, Bit => returnGen general_match_one_bit
    | One, Qubit => returnGen general_match_one_qubit
    | One, Tensor l r =>
      liftGen2 general_match_w1_l
               (genGeneralWTypeMatchRec step' One l) (genGeneralWTypeMatchLeftOne r)
    | Bit, One => returnGen general_match_bit_one
    | Bit, Bit => returnGen general_match_bit_bit
    | Bit, Qubit => returnGen general_match_bit_qubit
    | Bit, Tensor l r =>
      liftGen2 general_match_w1_l
               (genGeneralWTypeMatchRec step' Bit l) (genGeneralWTypeMatchLeftOne r)
    | Qubit, One => returnGen general_match_qubit_one
    | Qubit, Bit => returnGen general_match_qubit_bit
    | Qubit, Qubit => returnGen general_match_qubit_qubit
    | Qubit, Tensor l r =>
      liftGen2 general_match_w1_l
               (genGeneralWTypeMatchRec step' Qubit l) (genGeneralWTypeMatchLeftOne r)
    | Tensor l r, One =>
      liftGen2 general_match_l_w2
               (genGeneralWTypeMatchRec step' l One) (genGeneralWTypeMatchRightOne r)
    | Tensor l r, Bit =>
      liftGen2 general_match_l_w2
               (genGeneralWTypeMatchRec step' l Bit) (genGeneralWTypeMatchRightOne r)
    | Tensor l r, Qubit =>
      liftGen2 general_match_l_w2
               (genGeneralWTypeMatchRec step' l Qubit) (genGeneralWTypeMatchRightOne r)
    | Tensor ll lr, Tensor rl rr =>
      oneOf [ liftGen2 general_match_l_w2
                       (genGeneralWTypeMatchRec step' ll (Tensor rl rr))
                       (genGeneralWTypeMatchRightOne lr) ;
                liftGen2 general_match_r_w2
                         (genGeneralWTypeMatchRec step' lr (Tensor rl rr))
                         (genGeneralWTypeMatchRightOne ll) ;
                liftGen2 general_match_w1_l
                         (genGeneralWTypeMatchRec step' (Tensor ll lr) rl)
                         (genGeneralWTypeMatchLeftOne rr) ;
                liftGen2 general_match_w1_r
                         (genGeneralWTypeMatchRec step' (Tensor ll lr) rr)
                         (genGeneralWTypeMatchLeftOne rl) ;
                liftGen2 general_match_w1_w2
                         (genGeneralWTypeMatchRec step' ll rl)
                         (genGeneralWTypeMatchRec step' lr rr)
            ]
    end
  end.
*)
Fixpoint simplWTypeMatchWTyped_One_w2 (w2 : WType) : WTypeMatch One w2 :=
  match w2 with
  | One => match_none
  | Bit => match_one_bit
  | Qubit => match_one_qubit
  | Tensor w2l w2r
    => @match_w1_l One w2l w2r
                   (simplWTypeMatchWTyped_One_w2 w2l)
                   (simplWTypeMatchWTyped_One_w2 w2r)
  end.
Fixpoint simplWTypeMatchWTyped_Bit_w2 (w2 : WType) : WTypeMatch Bit w2 :=
  match w2 with
  | One => match_bit_one
  | Bit => match_bit_bit
  | Qubit => match_bit_qubit
  | Tensor w2l w2r
    => @match_w1_l Bit w2l w2r
                   (simplWTypeMatchWTyped_Bit_w2 w2l)
                   (simplWTypeMatchWTyped_One_w2 w2r)
  end.
Fixpoint simplWTypeMatchWTyped_Qubit_w2 (w2 : WType) : WTypeMatch Qubit w2 :=
  match w2 with
  | One => match_qubit_one
  | Bit => match_qubit_bit
  | Qubit => match_qubit_qubit
  | Tensor w2l w2r
    => @match_w1_l Qubit w2l w2r
                   (simplWTypeMatchWTyped_Qubit_w2 w2l)
                   (simplWTypeMatchWTyped_One_w2 w2r)
  end.
Fixpoint simplWTypeMatchWTyped_w1_w2 (w1 w2 : WType) : WTypeMatch w1 w2 :=
  match w1 with
  | One => simplWTypeMatchWTyped_One_w2 w2
  | Bit => simplWTypeMatchWTyped_Bit_w2 w2
  | Qubit => simplWTypeMatchWTyped_Qubit_w2 w2
  | Tensor w1l w1r
    => match w2 with
       | One
         => @match_l_w2 w1l One w1r
                        (simplWTypeMatchWTyped_w1_w2 w1l One)
                        (simplWTypeMatchWTyped_w1_w2 w1r One)
       | Bit
         => @match_l_w2 w1l Bit w1r
                        (simplWTypeMatchWTyped_w1_w2 w1l Bit)
                        (simplWTypeMatchWTyped_w1_w2 w1r One)
       | Qubit
         => @match_l_w2 w1l Qubit w1r
                        (simplWTypeMatchWTyped_w1_w2 w1l Qubit)
                        (simplWTypeMatchWTyped_w1_w2 w1r One)
       | Tensor w2l w2r
         => @match_w1_w2 w1l w1r w2l w2r
                         (simplWTypeMatchWTyped_w1_w2 w1l w2l)
                         (simplWTypeMatchWTyped_w1_w2 w1r w2r)
       end
  end.

Fixpoint genWTypeMatchRec (step : nat) (w1 : WType) (w2 : WType) : G (WTypeMatch w1 w2) :=
  match step with
  | O => returnGen (simplWTypeMatchWTyped_w1_w2 w1 w2)
  | S step' =>
    match w1, w2 with
    | One, One => returnGen match_none
    | One, Bit => returnGen match_one_bit
    | One, Qubit => returnGen match_one_qubit
    | One, Tensor l r =>
      liftGen2 match_w1_l (genWTypeMatchRec step' One l) (genWTypeMatchRec step' One r)
    | Bit, One => returnGen match_bit_one
    | Bit, Bit => returnGen match_bit_bit
    | Bit, Qubit => returnGen match_bit_qubit
    | Bit, Tensor l r =>
      liftGen2 match_w1_l (genWTypeMatchRec step' Bit l) (genWTypeMatchRec step' One r)
    | Qubit, One => returnGen match_qubit_one
    | Qubit, Bit => returnGen match_qubit_bit
    | Qubit, Qubit => returnGen match_qubit_qubit
    | Qubit, Tensor l r =>
      liftGen2 match_w1_l (genWTypeMatchRec step' Qubit l) (genWTypeMatchRec step' One r)
    | Tensor l r, One =>
      liftGen2 match_l_w2 (genWTypeMatchRec step' l One) (genWTypeMatchRec step' r One)
    | Tensor l r, Bit =>
      liftGen2 match_l_w2 (genWTypeMatchRec step' l Bit) (genWTypeMatchRec step' r One)
    | Tensor l r, Qubit =>
      liftGen2 match_l_w2 (genWTypeMatchRec step' l Qubit) (genWTypeMatchRec step' r One)
    | Tensor ll lr, Tensor rl rr =>
      oneOf [ liftGen2 match_l_w2
                       (genWTypeMatchRec step' ll (Tensor rl rr))
                       (genWTypeMatchRec step' lr One) ;
                liftGen2 match_r_w2
                         (genWTypeMatchRec step' lr (Tensor rl rr))
                         (genWTypeMatchRec step' ll One) ;
                liftGen2 match_w1_l
                         (genWTypeMatchRec step' (Tensor ll lr) rl)
                         (genWTypeMatchRec step' One rr) ;
                liftGen2 match_w1_r
                         (genWTypeMatchRec step' (Tensor ll lr) rr)
                         (genWTypeMatchRec step' One rl) ;
                liftGen2 match_w1_w2
                         (genWTypeMatchRec step' ll rl)
                         (genWTypeMatchRec step' lr rr)
            ]
    end
  end.

Fixpoint count_pair_in_WType (w : WType) : nat :=
  match w with
  | Tensor l r => 1 + (count_pair_in_WType l) + (count_pair_in_WType r)
  | _ => O
  end.
(*
Definition genGeneralWTypeMatch (w1 : WType) (w2 : WType) : G (GeneralWTypeMatch) :=
(*
 count_pair_in_WType (Tensor w1 w2) = 1 + (count_pair_in_WType w1) + (count_pair_in_WType w2)
 *)
  (genGeneralWTypeMatchRec (count_pair_in_WType (Tensor w1 w2)) w1 w2).
*)

(*
 count_pair_in_WType (Tensor w1 w2) = 1 + (count_pair_in_WType w1) + (count_pair_in_WType w2)
*)
Definition genWTypeMatch (w1 : WType) (w2 : WType) : G (WTypeMatch w1 w2) :=
  (genWTypeMatchRec (count_pair_in_WType (Tensor w1 w2)) w1 w2).
(*
(* GeneralBox *)
Inductive GeneralBox :=
| general_box (w1 w2 : WType) : (Box w1 w2) -> GeneralBox.

Check GeneralBox.

Instance showGeneralBox : Show (GeneralBox) :=
  {| show := 
       let fix aux_box t := 
           match t with
           | general_box w1 w2 b => "general_box (" ++ (show b) ++ ")"
           end
       in aux_box
  |}.

Fixpoint GeneralBox_to_WType (gb : GeneralBox) : WType * WType :=
  match gb with
  | general_box w1 w2 b => Datatypes.pair w1 w2
  end.
Check GeneralBox_to_WType.
Fixpoint GeneralBox_to_Box (gb : GeneralBox) :
  Box (fst (GeneralBox_to_WType gb)) (snd (GeneralBox_to_WType gb)) :=
  match gb with
  | general_box w1 w2 b => b
  end.
Check GeneralBox_to_Box.
Fixpoint Box_to_GeneralBox {w1 w2} (b : Box w1 w2) : GeneralBox :=
  match b with
  | box b' => general_box w1 w2 (box b')
  end.
Check Box_to_GeneralBox.

Inductive GeneralBoxLeftOne :=
| general_box_left_one : forall {w : WType}, Box One w -> GeneralBoxLeftOne.

Instance showGeneralBoxLeftOne : Show (GeneralBoxLeftOne) :=
  {| show := 
       let fix aux t := 
           match t with
           | general_box_left_one w b => "general_box_left_one (" ++ (show) b ++ ")"
           end
       in aux
  |}.

Fixpoint GeneralBoxLeftOne_to_WType (gb : GeneralBoxLeftOne) : WType * WType :=
  match gb with
  | general_box_left_one w b => Datatypes.pair One w
  end.
Check GeneralBoxLeftOne_to_WType.
Fixpoint GeneralBoxLeftOne_to_Box (gb : GeneralBoxLeftOne) :
  Box One (snd (GeneralBoxLeftOne_to_WType gb)) :=
  match gb with
  | general_box_left_one w b => b
  end.
Check GeneralBoxLeftOne_to_Box.
Fixpoint Box_to_GeneralBoxLeftOne {w : WType} (b : Box One w) : GeneralBoxLeftOne :=
  general_box_left_one b.
Check Box_to_GeneralBoxLeftOne.

Inductive GeneralBoxRightOne :=
| general_box_right_one : forall {w : WType}, Box w One -> GeneralBoxRightOne.

Instance showGeneralBoxRightOne : Show (GeneralBoxRightOne) :=
  {| show := 
       let fix aux t := 
           match t with
           | general_box_right_one w b => "general_box_right_one (" ++ (show) b ++ ")"
           end
       in aux
  |}.

Fixpoint GeneralBoxRightOne_to_WType (gb : GeneralBoxRightOne) : WType * WType :=
  match gb with
  | general_box_right_one w b => Datatypes.pair w One
  end.
Check GeneralBoxRightOne_to_WType.
Fixpoint GeneralBoxRightOne_to_Box (gb : GeneralBoxRightOne) :
  Box (fst (GeneralBoxRightOne_to_WType gb)) One :=
  match gb with
  | general_box_right_one w b => b
  end.
Check GeneralBoxRightOne_to_Box.
Fixpoint Box_to_GeneralBoxRightOne {w : WType} (b : Box w One) : GeneralBoxRightOne :=
  general_box_right_one b.
Check Box_to_GeneralBoxRightOne.

(* Generator for GeneralBox composed of inPar and inSeq *)
Fixpoint genGeneralBoxFromGeneralWTypeMatchLeftOne
         (gwm : GeneralWTypeMatchLeftOne) : G GeneralBoxLeftOne :=
  match gwm with
  | general_match_left_one_none  => fmap (@Box_to_GeneralBoxLeftOne One)
                                         (returnGen (box (fun (p : Pat One) => output unit)))
  | general_match_left_one_bit   => oneOf [ fmap (@Box_to_GeneralBoxLeftOne Bit)
                                                 (returnGen (new false)) ;
                                              fmap (@Box_to_GeneralBoxLeftOne Bit)
                                                   (returnGen (new true))
                                          ] (* new0, new1 *)
  | general_match_left_one_qubit => oneOf [ fmap Box_to_GeneralBoxLeftOne
                                                 (returnGen (init false)) ;
                                              fmap Box_to_GeneralBoxLeftOne
                                                   (returnGen (init true))
                                          ] (* init0, init1 *)
  | general_match_left_one_tensor m1 m2 =>
    (liftGen2 (fun (gc1 gc2 : GeneralBoxLeftOne) =>
                 let c1 := (GeneralBoxLeftOne_to_Box gc1) in
                 let c2 := (GeneralBoxLeftOne_to_Box gc2) in
                 ((@Box_to_GeneralBoxLeftOne
                     (Tensor (snd (GeneralBoxLeftOne_to_WType gc1))
                             (snd (GeneralBoxLeftOne_to_WType gc2))))
                    (box_ () ⇒ 
                          let_ p1'     ← unbox c1 unit;
                       let_ p2'     ← unbox c2 unit; 
                       (p1', p2'))))
              (genGeneralBoxFromGeneralWTypeMatchLeftOne m1)
              (genGeneralBoxFromGeneralWTypeMatchLeftOne m2)
    )
  end.

Fixpoint genGeneralBoxFromGeneralWTypeMatchRightOne
         (gwm : GeneralWTypeMatchRightOne) : G GeneralBoxRightOne :=
  match gwm with
  | general_match_right_one_none  => fmap (@Box_to_GeneralBoxRightOne One)
                                          (returnGen (box (fun (p : Pat One) => output unit)))
  | general_match_right_one_bit   => fmap (@Box_to_GeneralBoxRightOne Bit)
                                          (returnGen (@boxed_gate Bit One discard))
  | general_match_right_one_qubit => fmap (@Box_to_GeneralBoxRightOne Qubit)
                                          (returnGen
                                             (box (fun (p0 : Pat Qubit) =>
                                                     gate meas p0
                                                          (fun (p1 : Pat Bit) =>
                                                             gate discard p1
                                                                  (fun (p2 : Pat One) =>
                                                                     output unit)))))
  | general_match_right_one_tensor m1 m2 =>
    (liftGen2 (fun (gc1 gc2 : GeneralBoxRightOne) =>
                 let c1 := (GeneralBoxRightOne_to_Box gc1) in
                 let c2 := (GeneralBoxRightOne_to_Box gc2) in
                 ((@Box_to_GeneralBoxRightOne
                     (Tensor (fst (GeneralBoxRightOne_to_WType gc1))
                             (fst (GeneralBoxRightOne_to_WType gc2))))
                    (box_ p12 ⇒
                          let_ (p1,p2) ← output p12;
                       let_ p1'     ← unbox c1 p1;
                       let_ p2'     ← unbox c2 p2; 
                       (unit))))
              (genGeneralBoxFromGeneralWTypeMatchRightOne m1)
              (genGeneralBoxFromGeneralWTypeMatchRightOne m2)
    )
  end.

Fixpoint genGeneralBoxFromGeneralWTypeMatch (gwm : GeneralWTypeMatch) : G GeneralBox :=
  match gwm with
  | general_match_none        => fmap (@Box_to_GeneralBox One One)
                                      (returnGen (box (fun (p : Pat One) => output unit)))
  | general_match_unitary uw  => let wt := (UnitaryWType_to_WType uw) in
                                 oneOf [ fmap Box_to_GeneralBox
                                              (fmap (fun (ug : Unitary wt) =>
                                                       (@boxed_gate wt wt ug))
                                                    (genUnitaryWTyped uw)) ;
                                           fmap Box_to_GeneralBox
                                                (returnGen (@id_circ wt))
                                       ] (* Unitary, id *)
  | general_match_bit_bit     => oneOf [ fmap Box_to_GeneralBox
                                              (returnGen
                                                 (box (fun (p : Pat Bit) =>
                                                         gate BNOT p (fun (p' : Pat Bit) =>
                                                                        output p')))) ;
                                           fmap Box_to_GeneralBox
                                                (returnGen (@id_circ Bit))
                                       ] (* BNOT, id *)
  | general_match_one_qubit   => oneOf [ fmap Box_to_GeneralBox
                                              (returnGen (init false)) ;
                                           fmap Box_to_GeneralBox
                                                (returnGen (init true))
                                       ] (* init0, init1 *)
  | general_match_one_bit     => oneOf [ fmap Box_to_GeneralBox
                                              (returnGen (new false)) ;
                                           fmap Box_to_GeneralBox
                                                (returnGen (new true))
                                       ] (* new0, new1 *)
  | general_match_qubit_bit   => fmap Box_to_GeneralBox
                                      (returnGen (@boxed_gate Qubit Bit meas)) (* meas *)
  | general_match_qubit_qubit => oneOf [ fmap Box_to_GeneralBox
                                              (returnGen (@boxed_gate Qubit Qubit measQ)) ;
                                           fmap Box_to_GeneralBox
                                                (fmap (fun (ug : Unitary Qubit) =>
                                                         (@boxed_gate Qubit Qubit ug))
                                                      (genUnitaryWTyped Unitary_Qubit)) ;
                                           fmap Box_to_GeneralBox
                                                (returnGen (@id_circ Qubit))
                                       ] (* measQ, Unitary, id *)
  | general_match_bit_one     => fmap Box_to_GeneralBox
                                      (returnGen (@boxed_gate Bit One discard)) (* discard *)
  | general_match_bit_qubit   => fmap Box_to_GeneralBox
                                      (returnGen
                                         (box (fun (p0 : Pat Bit) =>
                                                 gate_ nv ← init0 @();
                                                   gate_ (p1, nv') ←
                                                         (U (bit_ctrl _X)) @(pair p0 nv);
                                                   gate_ () ← discard @p1;
                                                   output nv')))
  (* init0 nv -> bit_ctrl bit nv -> discard bit -> output nv' *)
  | general_match_qubit_one   => fmap Box_to_GeneralBox
                                      (returnGen
                                         (box (fun (p0 : Pat Qubit) =>
                                                 gate_ p1 ← meas @p0;
                                                   gate_ () ← discard @p1;
                                                   output unit)))
  (* meas -> discard (or, assert0, assert1) *)
  | general_match_l_w2 m1 m2  => (liftGen2 (fun (gc1 : GeneralBox)
                                                (gc2 : GeneralBoxRightOne) =>
                                              let c1 := (GeneralBox_to_Box gc1) in
                                              let c2 := (GeneralBoxRightOne_to_Box gc2) in
                                              (Box_to_GeneralBox
                                                 (box_ p12 ⇒ 
                                                       let_ (p1,p2) ← output p12; 
                                                    let_ p1'     ← unbox c1 p1;
                                                    let_ p2'     ← unbox c2 p2; 
                                                    p1')))
                                           (genGeneralBoxFromGeneralWTypeMatch m1)
                                           (genGeneralBoxFromGeneralWTypeMatchRightOne m2)
                                 )
  | general_match_r_w2 m1 m2  => (liftGen2 (fun (gc1 : GeneralBox)
                                                (gc2 : GeneralBoxRightOne) =>
                                              let c1 := (GeneralBox_to_Box gc1) in
                                              let c2 := (GeneralBoxRightOne_to_Box gc2) in
                                              (Box_to_GeneralBox
                                                 (box_ p12 ⇒ 
                                                       let_ (p1,p2) ← output p12; 
                                                    let_ p1'     ← unbox c2 p1;
                                                    let_ p2'     ← unbox c1 p2; 
                                                    p2')))
                                           (genGeneralBoxFromGeneralWTypeMatch m1)
                                           (genGeneralBoxFromGeneralWTypeMatchRightOne m2)
                                 )
  | general_match_w1_l m1 m2  => (liftGen2 (fun (gc1 : GeneralBox)
                                                (gc2 : GeneralBoxLeftOne) =>
                                              let c1 := (GeneralBox_to_Box gc1) in
                                              let c2 := (GeneralBoxLeftOne_to_Box gc2) in
                                              (Box_to_GeneralBox
                                                 (box_ p ⇒ 
                                                       let_ p1'     ← unbox c1 p;
                                                    let_ p2'     ← unbox c2 unit; 
                                                    (p1', p2'))))
                                           (genGeneralBoxFromGeneralWTypeMatch m1)
                                           (genGeneralBoxFromGeneralWTypeMatchLeftOne m2)
                                 )
  | general_match_w1_r m1 m2  => (liftGen2 (fun (gc1 : GeneralBox)
                                                (gc2 : GeneralBoxLeftOne) =>
                                              let c1 := (GeneralBox_to_Box gc1) in
                                              let c2 := (GeneralBoxLeftOne_to_Box gc2) in
                                              (Box_to_GeneralBox
                                                 (box_ p ⇒ 
                                                       let_ p1'     ← unbox c2 unit;
                                                    let_ p2'     ← unbox c1 p; 
                                                    (p1', p2'))))
                                           (genGeneralBoxFromGeneralWTypeMatch m1)
                                           (genGeneralBoxFromGeneralWTypeMatchLeftOne m2)
                                 )
  | general_match_w1_w2 m1 m2 => (liftGen2 (fun (gc1 gc2 : GeneralBox) =>
                                              let c1 := (GeneralBox_to_Box gc1) in
                                              let c2 := (GeneralBox_to_Box gc2) in
                                              (Box_to_GeneralBox (inPar c1 c2)))
                                           (genGeneralBoxFromGeneralWTypeMatch m1)
                                           (genGeneralBoxFromGeneralWTypeMatch m2)
                                 )
  end.

Definition genGeneralBoxWTyped (w1 : WType) (w2 : WType) : G GeneralBox :=
  bindGen (genGeneralWTypeMatch w1 w2) genGeneralBoxFromGeneralWTypeMatch.

(* Left General WTypeMatch *)
Inductive LeftGeneralWTypeMatchLeftOne : WType -> Set :=
| left_general_match_left_one_none   : LeftGeneralWTypeMatchLeftOne One
| left_general_match_left_one_bit    : LeftGeneralWTypeMatchLeftOne Bit
| left_general_match_left_one_qubit  : LeftGeneralWTypeMatchLeftOne Qubit
| left_general_match_left_one_tensor (w2l w2r : WType) :
    LeftGeneralWTypeMatchLeftOne w2l -> LeftGeneralWTypeMatchLeftOne w2r
    -> LeftGeneralWTypeMatchLeftOne (Tensor w2l w2r)
.
Fixpoint LeftGeneralWTypeMatchLeftOne_to_WType
         {w2 : WType} (lgwm : LeftGeneralWTypeMatchLeftOne w2) : WType := w2.
Check LeftGeneralWTypeMatchLeftOne_to_WType.
Fixpoint LeftGeneralWTypeMatchLeftOne_to_WTypeMatch
        {w2 : WType} (lgwm : LeftGeneralWTypeMatchLeftOne w2)
  : WTypeMatch One w2 :=
    match lgwm with
    | left_general_match_left_one_none                 => match_none
    | left_general_match_left_one_bit                  => match_one_bit
    | left_general_match_left_one_qubit                => match_one_qubit
    | left_general_match_left_one_tensor w2l w2r m1 m2 =>
      (@match_w1_l One w2l w2r
                   (LeftGeneralWTypeMatchLeftOne_to_WTypeMatch m1)
                   (LeftGeneralWTypeMatchLeftOne_to_WTypeMatch m2))
    end.
Check LeftGeneralWTypeMatchLeftOne_to_WTypeMatch.
Fixpoint genLeftGeneralWTypeMatchLeftOne (w2 : WType) : G (LeftGeneralWTypeMatchLeftOne w2) :=
  match w2 with
  | One => returnGen left_general_match_left_one_none
  | Bit => returnGen left_general_match_left_one_bit
  | Qubit => returnGen left_general_match_left_one_qubit
  | Tensor l r =>
    liftGen2 (left_general_match_left_one_tensor l r)
             (genLeftGeneralWTypeMatchLeftOne l) (genLeftGeneralWTypeMatchLeftOne r)
  end.

Inductive LeftGeneralWTypeMatchRightOne : Set :=
| left_general_match_right_one_none   : LeftGeneralWTypeMatchRightOne
| left_general_match_right_one_bit    : LeftGeneralWTypeMatchRightOne
| left_general_match_right_one_qubit  : LeftGeneralWTypeMatchRightOne
| left_general_match_right_one_tensor :
    LeftGeneralWTypeMatchRightOne -> LeftGeneralWTypeMatchRightOne
    -> LeftGeneralWTypeMatchRightOne
.
Fixpoint LeftGeneralWTypeMatchRightOne_to_WType
         (lgwm : LeftGeneralWTypeMatchRightOne) : WType :=
  match lgwm with
  | left_general_match_right_one_none         => One
  | left_general_match_right_one_bit          => Bit
  | left_general_match_right_one_qubit        => Qubit
  | left_general_match_right_one_tensor m1 m2 =>
    (Tensor (LeftGeneralWTypeMatchRightOne_to_WType m1)
            (LeftGeneralWTypeMatchRightOne_to_WType m2))
  end.
Check LeftGeneralWTypeMatchRightOne_to_WType.
Fixpoint LeftGeneralWTypeMatchRightOne_to_WTypeMatch
         (lgwm : LeftGeneralWTypeMatchRightOne)
  : WTypeMatch (LeftGeneralWTypeMatchRightOne_to_WType lgwm) One :=
    match lgwm with
    | left_general_match_right_one_none         => match_none
    | left_general_match_right_one_bit          => match_bit_one
    | left_general_match_right_one_qubit        => match_qubit_one
    | left_general_match_right_one_tensor m1 m2 =>
      (@match_l_w2 (LeftGeneralWTypeMatchRightOne_to_WType m1)
                   One
                   (LeftGeneralWTypeMatchRightOne_to_WType m2)
                   (LeftGeneralWTypeMatchRightOne_to_WTypeMatch m1)
                   (LeftGeneralWTypeMatchRightOne_to_WTypeMatch m2))
    end.
Check LeftGeneralWTypeMatchRightOne_to_WTypeMatch.
Fixpoint genLeftGeneralWTypeMatchRightOne (w1 : WType)
  : G (LeftGeneralWTypeMatchRightOne) :=
  match w1 with
  | One => returnGen left_general_match_right_one_none
  | Bit => returnGen left_general_match_right_one_bit
  | Qubit => returnGen left_general_match_right_one_qubit
  | Tensor l r => liftGen2 left_general_match_right_one_tensor
                           (genLeftGeneralWTypeMatchRightOne l)
                           (genLeftGeneralWTypeMatchRightOne r)
  end.

(* LeftGeneralWTypeMatch *)
Inductive LeftGeneralWTypeMatch : WType -> Set :=
| left_general_match_none        : LeftGeneralWTypeMatch One
| left_general_match_unitary (ut : UnitaryWType) :
    LeftGeneralWTypeMatch (UnitaryWType_to_WType ut) (* Unitray *)
| left_general_match_bit_bit     : LeftGeneralWTypeMatch Bit (* BNOT *)
| left_general_match_one_qubit   : LeftGeneralWTypeMatch Qubit (* init0, init1 *)
| left_general_match_one_bit     : LeftGeneralWTypeMatch Bit (* new0, new1 *)
| left_general_match_qubit_bit   : LeftGeneralWTypeMatch Bit (* meas *)
| left_general_match_qubit_qubit : LeftGeneralWTypeMatch Qubit (* measQ, Unitary *)
| left_general_match_bit_one     : LeftGeneralWTypeMatch One (* discard *)
| left_general_match_bit_qubit   : LeftGeneralWTypeMatch Qubit (* init0 nv -> bit_ctrl bit nv
                                                                  -> discard bit -> 
                                                                  output nv *)
| left_general_match_qubit_one   : LeftGeneralWTypeMatch One (* meas -> discard 
                                                                (or, assert0, assert1) *)
| left_general_match_l_w2 (w2 : WType) :
    LeftGeneralWTypeMatch w2 -> LeftGeneralWTypeMatchRightOne -> LeftGeneralWTypeMatch w2
| left_general_match_r_w2 (w2 : WType) :
    LeftGeneralWTypeMatch w2 -> LeftGeneralWTypeMatchRightOne -> LeftGeneralWTypeMatch w2
| left_general_match_w1_l (w2l w2r : WType) :
    LeftGeneralWTypeMatch w2l -> LeftGeneralWTypeMatchLeftOne w2r
    -> LeftGeneralWTypeMatch (Tensor w2l w2r)
| left_general_match_w1_r (w2l w2r : WType) :
    LeftGeneralWTypeMatch w2r -> LeftGeneralWTypeMatchLeftOne w2l
    -> LeftGeneralWTypeMatch (Tensor w2l w2r)
| left_general_match_w1_w2 (w2l w2r : WType) :
    LeftGeneralWTypeMatch w2l -> LeftGeneralWTypeMatch w2r
    -> LeftGeneralWTypeMatch (Tensor w2l w2r)
.

Fixpoint LeftGeneralWTypeMatch_to_WType
         {w2 : WType} (lgwm : LeftGeneralWTypeMatch w2) : WType * WType :=
  match lgwm with
  | left_general_match_none        => (Datatypes.pair One One)
  | left_general_match_unitary uw  => (Datatypes.pair (UnitaryWType_to_WType uw)
                                                 (UnitaryWType_to_WType uw))
  | left_general_match_bit_bit     => (Datatypes.pair Bit Bit)
  | left_general_match_one_qubit   => (Datatypes.pair One Qubit)
  | left_general_match_one_bit     => (Datatypes.pair One Bit)
  | left_general_match_qubit_bit   => (Datatypes.pair Qubit Bit)
  | left_general_match_qubit_qubit => (Datatypes.pair Qubit Qubit)
  | left_general_match_bit_one     => (Datatypes.pair Bit One)
  | left_general_match_bit_qubit   => (Datatypes.pair Bit Qubit)
  | left_general_match_qubit_one   => (Datatypes.pair Qubit One)
  | left_general_match_l_w2 _ m1 m2  =>
    let w1l := (fst (LeftGeneralWTypeMatch_to_WType m1)) in
    let w1r := (LeftGeneralWTypeMatchRightOne_to_WType m2) in
    (Datatypes.pair (Tensor w1l w1r) w2)
  | left_general_match_r_w2 _ m1 m2  =>
    let w1r := (fst (LeftGeneralWTypeMatch_to_WType m1)) in
    let w1l := (LeftGeneralWTypeMatchRightOne_to_WType m2) in
    (Datatypes.pair (Tensor w1l w1r) w2)
  | left_general_match_w1_l w2l w2r m1 m2  =>
    let w1 := (fst (LeftGeneralWTypeMatch_to_WType m1)) in
    (Datatypes.pair w1 (Tensor w2l w2r))
  | left_general_match_w1_r w2l w2r m1 m2  =>
    let w1 := (fst (LeftGeneralWTypeMatch_to_WType m1)) in
    (Datatypes.pair w1 (Tensor w2l w2r))
  | left_general_match_w1_w2 w2l w2r m1 m2 =>
    let w1l := (fst (LeftGeneralWTypeMatch_to_WType m1)) in
    let w1r := (fst (LeftGeneralWTypeMatch_to_WType m2)) in
    (Datatypes.pair (Tensor w1l w1r) (Tensor w2l w2r))
  end.
Check LeftGeneralWTypeMatch_to_WType.
Check (fst (LeftGeneralWTypeMatch_to_WType left_general_match_none)).
Program Fixpoint LeftGeneralWTypeMatch_to_WTypeMatch
        {w2 : WType} (lgwm : LeftGeneralWTypeMatch w2)
  : WTypeMatch (fst (LeftGeneralWTypeMatch_to_WType lgwm)) w2 :=
  match lgwm with
  | left_general_match_none        => match_none
  | left_general_match_unitary uw  => match_unitary uw
  | left_general_match_bit_bit     => match_bit_bit
  | left_general_match_one_qubit   => match_one_qubit
  | left_general_match_one_bit     => match_one_bit
  | left_general_match_qubit_bit   => match_qubit_bit
  | left_general_match_qubit_qubit => match_qubit_qubit
  | left_general_match_bit_one     => match_bit_one
  | left_general_match_bit_qubit   => match_bit_qubit
  | left_general_match_qubit_one   => match_qubit_one
  | left_general_match_l_w2 _ m1 m2  =>
    let w1l := (fst (LeftGeneralWTypeMatch_to_WType m1)) in
    let w1r := (LeftGeneralWTypeMatchRightOne_to_WType m2) in
    @match_l_w2 w1l w2 w1r
                (LeftGeneralWTypeMatch_to_WTypeMatch m1)
                (LeftGeneralWTypeMatchRightOne_to_WTypeMatch m2)
  | left_general_match_r_w2 _ m1 m2  =>
    let w1r := (fst (LeftGeneralWTypeMatch_to_WType m1)) in
    let w1l := (LeftGeneralWTypeMatchRightOne_to_WType m2) in
    @match_r_w2 w1r w2 w1l
                (LeftGeneralWTypeMatch_to_WTypeMatch m1)
                (LeftGeneralWTypeMatchRightOne_to_WTypeMatch m2)
  | left_general_match_w1_l w2l w2r m1 m2  =>
    let w1 := (fst (LeftGeneralWTypeMatch_to_WType m1)) in
    @match_w1_l w1 w2l w2r
                (LeftGeneralWTypeMatch_to_WTypeMatch m1)
                (LeftGeneralWTypeMatchLeftOne_to_WTypeMatch m2)
  | left_general_match_w1_r w2l w2r m1 m2  =>
    let w1 := (fst (LeftGeneralWTypeMatch_to_WType m1)) in
    @match_w1_r w1 w2r w2l
                (LeftGeneralWTypeMatch_to_WTypeMatch m1)
                (LeftGeneralWTypeMatchLeftOne_to_WTypeMatch m2)
  | left_general_match_w1_w2 w2l w2r m1 m2 =>
    let w1l := (fst (LeftGeneralWTypeMatch_to_WType m1)) in
    let w1r := (fst (LeftGeneralWTypeMatch_to_WType m2)) in
    @match_w1_w2 w1l w1r w2l w2r
                 (LeftGeneralWTypeMatch_to_WTypeMatch m1)
                 (LeftGeneralWTypeMatch_to_WTypeMatch m2)
  end.
Check GeneralWTypeMatch_to_WTypeMatch.

Fixpoint LeftGeneralWTypeMatchLeftOne_to_LeftGeneralWTypeMatch
         {w2 : WType} (lgwm : LeftGeneralWTypeMatchLeftOne w2) : LeftGeneralWTypeMatch w2 :=
  match lgwm with
  | left_general_match_left_one_none         => left_general_match_none
  | left_general_match_left_one_bit          => left_general_match_one_bit
  | left_general_match_left_one_qubit        => left_general_match_one_qubit
  | left_general_match_left_one_tensor w2l w2r m1 m2 =>
    (@left_general_match_w1_w2
       w2l w2r
       (LeftGeneralWTypeMatchLeftOne_to_LeftGeneralWTypeMatch m1)
       (LeftGeneralWTypeMatchLeftOne_to_LeftGeneralWTypeMatch m2))
  end.

Fixpoint genLeftGeneralWTypeMatchRec (step : nat) (w1 : WType) (w2 : WType)
  : G (LeftGeneralWTypeMatch w2) :=
  match step with
  | O => fmap (LeftGeneralWTypeMatchLeftOne_to_LeftGeneralWTypeMatch)
              (genLeftGeneralWTypeMatchLeftOne w2)
  | S step' =>
    match w1, w2 with
    | One, One => returnGen left_general_match_none
    | One, Bit => returnGen left_general_match_one_bit
    | One, Qubit => returnGen left_general_match_one_qubit
    | One, Tensor l r =>
      liftGen2 (left_general_match_w1_l l r)
               (genLeftGeneralWTypeMatchRec step' One l)
               (genLeftGeneralWTypeMatchLeftOne r)
    | Bit, One => returnGen left_general_match_bit_one
    | Bit, Bit => returnGen left_general_match_bit_bit
    | Bit, Qubit => returnGen left_general_match_bit_qubit
    | Bit, Tensor l r =>
      liftGen2 (left_general_match_w1_l l r)
               (genLeftGeneralWTypeMatchRec step' Bit l)
               (genLeftGeneralWTypeMatchLeftOne r)
    | Qubit, One => returnGen left_general_match_qubit_one
    | Qubit, Bit => returnGen left_general_match_qubit_bit
    | Qubit, Qubit => returnGen left_general_match_qubit_qubit
    | Qubit, Tensor l r =>
      liftGen2 (left_general_match_w1_l l r)
               (genLeftGeneralWTypeMatchRec step' Qubit l)
               (genLeftGeneralWTypeMatchLeftOne r)
    | Tensor l r, One =>
      liftGen2 (left_general_match_l_w2 One)
               (genLeftGeneralWTypeMatchRec step' l One)
               (genLeftGeneralWTypeMatchRightOne r)
    | Tensor l r, Bit =>
      liftGen2 (left_general_match_l_w2 Bit)
               (genLeftGeneralWTypeMatchRec step' l Bit)
               (genLeftGeneralWTypeMatchRightOne r)
    | Tensor l r, Qubit =>
      liftGen2 (left_general_match_l_w2 Qubit)
               (genLeftGeneralWTypeMatchRec step' l Qubit)
               (genLeftGeneralWTypeMatchRightOne r)
    | Tensor ll lr, Tensor rl rr =>
      oneOf [ liftGen2 (left_general_match_l_w2 (Tensor rl rr))
                       (genLeftGeneralWTypeMatchRec step' ll (Tensor rl rr))
                       (genLeftGeneralWTypeMatchRightOne lr) ;
                liftGen2 (left_general_match_r_w2 (Tensor rl rr))
                         (genLeftGeneralWTypeMatchRec step' lr (Tensor rl rr))
                         (genLeftGeneralWTypeMatchRightOne ll) ;
                liftGen2 (left_general_match_w1_l rl rr)
                         (genLeftGeneralWTypeMatchRec step' (Tensor ll lr) rl)
                         (genLeftGeneralWTypeMatchLeftOne rr) ;
                liftGen2 (left_general_match_w1_r rl rr)
                         (genLeftGeneralWTypeMatchRec step' (Tensor ll lr) rr)
                         (genLeftGeneralWTypeMatchLeftOne rl) ;
                liftGen2 (left_general_match_w1_w2 rl rr)
                         (genLeftGeneralWTypeMatchRec step' ll rl)
                         (genLeftGeneralWTypeMatchRec step' lr rr)
            ]
    end
  end.

Definition genLeftGeneralWTypeMatch (w1 : WType) (w2 : WType)
  : G (LeftGeneralWTypeMatch w2) :=
  (genLeftGeneralWTypeMatchRec (count_pair_in_WType (Tensor w1 w2)) w1 w2).

(* Generator for Box composed of inPar and inSeq *)
Check GeneralWTypeMatchLeftOne_to_WType.
Fixpoint genBoxFromGeneralWTypeMatchLeftOne (gwm : GeneralWTypeMatchLeftOne)
  : G (Box One (GeneralWTypeMatchLeftOne_to_WType gwm)) :=
  match gwm with
  | general_match_left_one_none
    => returnGen (box (fun (p : Pat One) => output unit))
  | general_match_left_one_bit
    => oneOf [ returnGen (new false) ;
                 returnGen (new true)
             ] (* new0, new1 *)
  | general_match_left_one_qubit
    => oneOf [ returnGen (init false) ;
                 returnGen (init true)
             ] (* init0, init1 *)
  | general_match_left_one_tensor m1 m2
    => (liftGen2 (fun (c1 : Box One (GeneralWTypeMatchLeftOne_to_WType m1))
                      (c2 : Box One (GeneralWTypeMatchLeftOne_to_WType m2)) =>
                    (box_ () ⇒ 
                          let_ p1'     ← unbox c1 unit;
                       let_ p2'     ← unbox c2 unit; 
                       (p1', p2')))
                 (genBoxFromGeneralWTypeMatchLeftOne m1)
                 (genBoxFromGeneralWTypeMatchLeftOne m2)
       )
  end.

Fixpoint genBoxFromGeneralWTypeMatchRightOne (gwm : GeneralWTypeMatchRightOne)
  : G (Box (GeneralWTypeMatchRightOne_to_WType gwm) One) :=
  match gwm with
  | general_match_right_one_none
    => returnGen (box (fun (p : Pat One) => output unit))
  | general_match_right_one_bit
    => returnGen (@boxed_gate Bit One discard)
  | general_match_right_one_qubit
    => returnGen
         (box (fun (p0 : Pat Qubit) =>
                 gate meas p0
                      (fun (p1 : Pat Bit) =>
                         gate discard p1
                              (fun (p2 : Pat One) =>
                                 output unit))))
  | general_match_right_one_tensor m1 m2
    => (liftGen2 (fun (c1 : Box (GeneralWTypeMatchRightOne_to_WType m1) One)
                      (c2 : Box (GeneralWTypeMatchRightOne_to_WType m2) One) =>
                    (box_ p12 ⇒
                          let_ (p1,p2) ← output p12;
                       let_ p1'     ← unbox c1 p1;
                       let_ p2'     ← unbox c2 p2; 
                       (unit)))
                 (genBoxFromGeneralWTypeMatchRightOne m1)
                 (genBoxFromGeneralWTypeMatchRightOne m2)
       )
  end.

Program Fixpoint genBoxFromGeneralWTypeMatch (gwm : GeneralWTypeMatch)
  : G (Box (fst (GeneralWTypeMatch_to_WType gwm)) (snd (GeneralWTypeMatch_to_WType gwm))) :=
  match gwm with
  | general_match_none
    => returnGen (box (fun (p : Pat One) => output unit))
  | general_match_unitary uw
    => let wt := (UnitaryWType_to_WType uw) in
       oneOf [ fmap (fun (ug : Unitary wt) =>
                       (@boxed_gate wt wt ug))
                    (genUnitaryWTyped uw) ;
                 returnGen (@id_circ wt)
             ] (* Unitary, id *)
  | general_match_bit_bit
    => oneOf [ returnGen
                 (box (fun (p : Pat Bit) =>
                         gate BNOT p (fun (p' : Pat Bit) =>
                                        output p'))) ;
                 returnGen (@id_circ Bit)
             ] (* BNOT, id *)
  | general_match_one_qubit
    => oneOf [ returnGen (init false) ;
                 returnGen (init true)
             ] (* init0, init1 *)
  | general_match_one_bit
    => oneOf [ returnGen (new false) ;
                 returnGen (new true)
             ] (* new0, new1 *)
  | general_match_qubit_bit
    => returnGen (@boxed_gate Qubit Bit meas) (* meas *)
  | general_match_qubit_qubit
    => oneOf [ returnGen (@boxed_gate Qubit Qubit measQ) ;
                 fmap (fun (ug : Unitary Qubit) =>
                         (@boxed_gate Qubit Qubit ug))
                      (genUnitaryWTyped Unitary_Qubit) ;
                 returnGen (@id_circ Qubit)
             ] (* measQ, Unitary, id *)
  | general_match_bit_one
    => returnGen (@boxed_gate Bit One discard) (* discard *)
  | general_match_bit_qubit
    => returnGen
         (box (fun (p0 : Pat Bit) =>
                 gate_ nv ← init0 @();
                   gate_ (p1, nv') ←
                         (U (bit_ctrl _X)) @(pair p0 nv);
                   gate_ () ← discard @p1;
                   output nv'))
  (* init0 nv -> bit_ctrl bit nv -> discard bit -> output nv' *)
  | general_match_qubit_one
    => returnGen
         (box (fun (p0 : Pat Qubit) =>
                 gate_ p1 ← meas @p0;
                   gate_ () ← discard @p1;
                   output unit))
  (* meas -> discard (or, assert0, assert1) *)
  | general_match_l_w2 m1 m2
    => (liftGen2 (fun (c1 : Box (fst (GeneralWTypeMatch_to_WType m1))
                                (snd (GeneralWTypeMatch_to_WType m1)))
                      (c2 : Box (GeneralWTypeMatchRightOne_to_WType m2) One) =>
                    (box_ p12 ⇒ 
                          let_ (p1,p2) ← output p12; 
                       let_ p1'     ← unbox c1 p1;
                       let_ p2'     ← unbox c2 p2; 
                       p1'))
                 (genBoxFromGeneralWTypeMatch m1)
                 (genBoxFromGeneralWTypeMatchRightOne m2)
       )
  | general_match_r_w2 m1 m2
    => (liftGen2 (fun (c1 : Box (fst (GeneralWTypeMatch_to_WType m1))
                                (snd (GeneralWTypeMatch_to_WType m1)))
                      (c2 : Box (GeneralWTypeMatchRightOne_to_WType m2) One) =>
                    (box_ p12 ⇒ 
                          let_ (p1,p2) ← output p12; 
                       let_ p1'     ← unbox c2 p1;
                       let_ p2'     ← unbox c1 p2; 
                       p2'))
                 (genBoxFromGeneralWTypeMatch m1)
                 (genBoxFromGeneralWTypeMatchRightOne m2)
       )
  | general_match_w1_l m1 m2
    => (liftGen2 (fun (c1 : Box (fst (GeneralWTypeMatch_to_WType m1))
                                (snd (GeneralWTypeMatch_to_WType m1)))
                      (c2 : Box One (GeneralWTypeMatchLeftOne_to_WType m2)) =>
                    (box_ p ⇒ 
                          let_ p1'     ← unbox c1 p;
                       let_ p2'     ← unbox c2 unit; 
                       (p1', p2')))
                 (genBoxFromGeneralWTypeMatch m1)
                 (genBoxFromGeneralWTypeMatchLeftOne m2)
       )
  | general_match_w1_r m1 m2
    => (liftGen2 (fun (c1 : Box (fst (GeneralWTypeMatch_to_WType m1))
                                (snd (GeneralWTypeMatch_to_WType m1)))
                      (c2 : Box One (GeneralWTypeMatchLeftOne_to_WType m2)) =>
                    (box_ p ⇒ 
                          let_ p1'     ← unbox c2 unit;
                       let_ p2'     ← unbox c1 p; 
                       (p1', p2')))
                 (genBoxFromGeneralWTypeMatch m1)
                 (genBoxFromGeneralWTypeMatchLeftOne m2)
       )
  | general_match_w1_w2 m1 m2
    => (liftGen2 (fun (c1 : Box (fst (GeneralWTypeMatch_to_WType m1))
                                (snd (GeneralWTypeMatch_to_WType m1)))
                      (c2 : Box (fst (GeneralWTypeMatch_to_WType m2))
                                (snd (GeneralWTypeMatch_to_WType m2))) =>
                    (inPar c1 c2))
                 (genBoxFromGeneralWTypeMatch m1)
                 (genBoxFromGeneralWTypeMatch m2)
       )
  end.
*)
Fixpoint genBoxFromWTypeMatch {w1 w2 : WType} (wm : WTypeMatch w1 w2)
  : G (Box w1 w2) :=
  match wm with
  | match_none
    => returnGen (box (fun (p : Pat One) => output unit))
  | match_unitary uw
    => let wt := (UnitaryWType_to_WType uw) in
       oneOf [ fmap (fun (ug : Unitary wt) =>
                       (@boxed_gate wt wt ug))
                    (genUnitaryWTyped uw) ;
                 returnGen (@id_circ wt)
             ] (* Unitary, id *)
  | match_bit_bit
    => oneOf [ returnGen
                 (box (fun (p : Pat Bit) =>
                         gate BNOT p (fun (p' : Pat Bit) =>
                                        output p'))) ;
                 returnGen (@id_circ Bit)
             ] (* BNOT, id *)
  | match_one_qubit
    => oneOf [ returnGen (init false) ;
                 returnGen (init true)
             ] (* init0, init1 *)
  | match_one_bit
    => oneOf [ returnGen (new false) ;
                 returnGen (new true)
             ] (* new0, new1 *)
  | match_qubit_bit
    => returnGen (@boxed_gate Qubit Bit meas) (* meas *)
  | match_qubit_qubit
    => oneOf [ returnGen (@boxed_gate Qubit Qubit measQ) ;
                 fmap (fun (ug : Unitary Qubit) =>
                         (@boxed_gate Qubit Qubit ug))
                      (genUnitaryWTyped Unitary_Qubit) ;
                 returnGen (@id_circ Qubit)
             ] (* measQ, Unitary, id *)
  | match_bit_one
    => returnGen (@boxed_gate Bit One discard) (* discard *)
  | match_bit_qubit
    => returnGen
         (box (fun (p0 : Pat Bit) =>
                 gate_ nv ← init0 @();
                   gate_ (p1, nv') ←
                         (U (bit_ctrl _X)) @(pair p0 nv);
                   gate_ () ← discard @p1;
                   output nv'))
  (* init0 nv -> bit_ctrl bit nv -> discard bit -> output nv' *)
  | match_qubit_one
    => returnGen
         (box (fun (p0 : Pat Qubit) =>
                 gate_ p1 ← meas @p0;
                   gate_ () ← discard @p1;
                   output unit))
  (* meas -> discard (or, assert0, assert1) *)
  | match_l_w2 w1l w2 w1r m1 m2
    => (liftGen2 (fun (c1 : Box w1l w2) (c2 : Box w1r One) =>
                    (box_ p12 ⇒ 
                          let_ (p1,p2) ← output p12; 
                       let_ p1'     ← unbox c1 p1;
                       let_ p2'     ← unbox c2 p2; 
                       p1'))
                 (genBoxFromWTypeMatch m1)
                 (genBoxFromWTypeMatch m2)
       )
  | match_r_w2 w1r w2 w1l m1 m2
    => (liftGen2 (fun (c1 : Box w1r w2) (c2 : Box w1l One) =>
                    (box_ p12 ⇒ 
                          let_ (p1,p2) ← output p12; 
                       let_ p1'     ← unbox c2 p1;
                       let_ p2'     ← unbox c1 p2; 
                       p2'))
                 (genBoxFromWTypeMatch m1)
                 (genBoxFromWTypeMatch m2)
       )
  | match_w1_l w1 w2l w2r m1 m2
    => (liftGen2 (fun (c1 : Box w1 w2l) (c2 : Box One w2r) =>
                    (box_ p ⇒ 
                          let_ p1'     ← unbox c1 p;
                       let_ p2'     ← unbox c2 unit; 
                       (p1', p2')))
                 (genBoxFromWTypeMatch m1)
                 (genBoxFromWTypeMatch m2)
       )
  | match_w1_r w1 w2r w2l m1 m2
    => (liftGen2 (fun (c1 : Box w1 w2r) (c2 : Box One w2l) =>
                    (box_ p ⇒ 
                          let_ p1'     ← unbox c2 unit;
                       let_ p2'     ← unbox c1 p; 
                       (p1', p2')))
                 (genBoxFromWTypeMatch m1)
                 (genBoxFromWTypeMatch m2)
       )
  | match_w1_w2 w1l w1r w2l w2r m1 m2
    => (liftGen2 (fun (c1 : Box w1l w2l) (c2 : Box w1r w2r) =>
                    (inPar c1 c2))
                 (genBoxFromWTypeMatch m1)
                 (genBoxFromWTypeMatch m2)
       )
  end.

Definition genBoxWTyped (w1 : WType) (w2 : WType) : G (Box w1 w2) :=
  bindGen (genWTypeMatch w1 w2) genBoxFromWTypeMatch.
(*
(* LeftGeneralBox *)
Inductive LeftGeneralBox (w2 : WType) : Set :=
| left_general_box (w1 : WType) : (Box w1 w2) -> LeftGeneralBox w2.

Check LeftGeneralBox.

Instance showLeftGeneralBox {w2 : WType} : Show (LeftGeneralBox w2) :=
  {| show := 
       let fix aux_box {w2} t := 
           match t with
           | left_general_box w1 b => "left_general_box (" ++ (show b) ++ ")"
           end
       in aux_box
  |}.

Fixpoint LeftGeneralBox_to_WType {w2 : WType} (lgb : LeftGeneralBox w2) : WType * WType :=
  match lgb with
  | left_general_box w1 b => Datatypes.pair w1 w2
  end.
Check LeftGeneralBox_to_WType.
Program Fixpoint LeftGeneralBox_to_Box {w2 : WType} (lgb : LeftGeneralBox w2)
  : Box (fst (@LeftGeneralBox_to_WType w2 lgb)) (snd (@LeftGeneralBox_to_WType w2 lgb)) :=
  match lgb with
  | left_general_box w1 b => b
  end.
Next Obligation.
  destruct w2; reflexivity.
Next Obligation.
  destruct w2; reflexivity.
Qed.
Next Obligation.
  destruct w2; reflexivity.
Qed.
Check LeftGeneralBox_to_Box.
Fixpoint Box_to_LeftGeneralBox {w1 w2} (b : Box w1 w2) : LeftGeneralBox w2 :=
  match b with
  | box c => left_general_box w2 w1 (box c)
  end.
Check Box_to_LeftGeneralBox.

Inductive LeftGeneralBoxLeftOne (w2 : WType) : Set :=
| left_general_box_left_one : Box One w2 -> LeftGeneralBoxLeftOne w2.

Instance showLeftGeneralBoxLeftOne {w2 : WType} : Show (LeftGeneralBoxLeftOne w2) :=
  {| show := 
       let fix aux {w2} t := 
           match t with
           | left_general_box_left_one b => "left_general_box_left_one (" ++ (show) b ++ ")"
           end
       in aux
  |}.

Fixpoint LeftGeneralBoxLeftOne_to_WType
         {w2} (lgb : LeftGeneralBoxLeftOne w2) : WType * WType :=
  match lgb with
  | left_general_box_left_one b => Datatypes.pair One w2
  end.
Check LeftGeneralBoxLeftOne_to_WType.
Fixpoint LeftGeneralBoxLeftOne_to_Box {w2 : WType} (lgb : LeftGeneralBoxLeftOne w2) :
  Box One w2 :=
  match lgb with
  | left_general_box_left_one b => b
  end.
Check LeftGeneralBoxLeftOne_to_Box.
Fixpoint Box_to_LeftGeneralBoxLeftOne
         {w2 : WType} (b : Box One w2) : LeftGeneralBoxLeftOne w2 :=
  left_general_box_left_one w2 b.
Check Box_to_LeftGeneralBoxLeftOne.

Inductive LeftGeneralBoxRightOne :=
| left_general_box_right_one : forall {w1 : WType}, Box w1 One -> LeftGeneralBoxRightOne.

Instance showLeftGeneralBoxRightOne : Show (LeftGeneralBoxRightOne) :=
  {| show := 
       let fix aux t := 
           match t with
           | left_general_box_right_one w1 b
             => "left_general_box_right_one (" ++ (show) b ++ ")"
           end
       in aux
  |}.

Fixpoint LeftGeneralBoxRightOne_to_WType (lgb : LeftGeneralBoxRightOne) : WType * WType :=
  match lgb with
  | left_general_box_right_one w1 b => Datatypes.pair w1 One
  end.
Check LeftGeneralBoxRightOne_to_WType.
Fixpoint LeftGeneralBoxRightOne_to_Box (lgb : LeftGeneralBoxRightOne) :
  Box (fst (LeftGeneralBoxRightOne_to_WType lgb)) One :=
  match lgb with
  | left_general_box_right_one w1 b => b
  end.
Check LeftGeneralBoxRightOne_to_Box.
Fixpoint Box_to_LeftGeneralBoxRightOne
         {w1 : WType} (b : Box w1 One) : LeftGeneralBoxRightOne :=
  left_general_box_right_one b.
Check Box_to_LeftGeneralBoxRightOne.

(* Generator for LeftGeneralBox composed of inPar and inSeq *)
Fixpoint genLeftGeneralBoxFromLeftGeneralWTypeMatchLeftOne
         {w2 : WType} (lgwm : LeftGeneralWTypeMatchLeftOne w2)
  : G (LeftGeneralBoxLeftOne w2) :=
  match lgwm with
  | left_general_match_left_one_none
    => fmap (@Box_to_LeftGeneralBoxLeftOne One)
            (returnGen (box (fun (p : Pat One) => output unit)))
  | left_general_match_left_one_bit
    => oneOf [ fmap (@Box_to_LeftGeneralBoxLeftOne Bit)
                    (returnGen (new false)) ;
                 fmap (@Box_to_LeftGeneralBoxLeftOne Bit)
                      (returnGen (new true))
             ] (* new0, new1 *)
  | left_general_match_left_one_qubit
    => oneOf [ fmap Box_to_LeftGeneralBoxLeftOne
                    (returnGen (init false)) ;
                 fmap Box_to_LeftGeneralBoxLeftOne
                      (returnGen (init true))
             ] (* init0, init1 *)
  | left_general_match_left_one_tensor w2l w2r m1 m2
    => (liftGen2 (fun (gc1 : LeftGeneralBoxLeftOne w2l)
                      (gc2 : LeftGeneralBoxLeftOne w2r) =>
                    let c1 := (LeftGeneralBoxLeftOne_to_Box gc1) in
                    let c2 := (LeftGeneralBoxLeftOne_to_Box gc2) in
                    ((@Box_to_LeftGeneralBoxLeftOne (Tensor w2l w2r))
                       (box_ () ⇒ 
                             let_ p1'     ← unbox c1 unit;
                          let_ p2'     ← unbox c2 unit; 
                          (p1', p2'))))
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatchLeftOne m1)
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatchLeftOne m2)
       )
  end.

Fixpoint genLeftGeneralBoxFromLeftGeneralWTypeMatchRightOne
         (lgwm : LeftGeneralWTypeMatchRightOne) : G (LeftGeneralBoxRightOne) :=
  match lgwm with
  | left_general_match_right_one_none
    => fmap (@Box_to_LeftGeneralBoxRightOne One)
            (returnGen (box (fun (p : Pat One) => output unit)))
  | left_general_match_right_one_bit
    => fmap (@Box_to_LeftGeneralBoxRightOne Bit)
            (returnGen (@boxed_gate Bit One discard))
  | left_general_match_right_one_qubit
    => fmap (@Box_to_LeftGeneralBoxRightOne Qubit)
            (returnGen
               (box (fun (p0 : Pat Qubit) =>
                       gate meas p0
                            (fun (p1 : Pat Bit) =>
                               gate discard p1
                                    (fun (p2 : Pat One) =>
                                       output unit)))))
  | left_general_match_right_one_tensor m1 m2
    => (liftGen2 (fun (gc1 gc2 : LeftGeneralBoxRightOne) =>
                    let c1 := (LeftGeneralBoxRightOne_to_Box gc1) in
                    let c2 := (LeftGeneralBoxRightOne_to_Box gc2) in
                    ((@Box_to_LeftGeneralBoxRightOne
                        (Tensor (fst (LeftGeneralBoxRightOne_to_WType gc1))
                                (fst (LeftGeneralBoxRightOne_to_WType gc2))))
                       (box_ p12 ⇒
                             let_ (p1,p2) ← output p12;
                          let_ p1'     ← unbox c1 p1;
                          let_ p2'     ← unbox c2 p2; 
                          (unit))))
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatchRightOne m1)
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatchRightOne m2)
       )
  end.

Program Fixpoint genLeftGeneralBoxFromLeftGeneralWTypeMatch
         {w2 : WType} (lgwm : LeftGeneralWTypeMatch w2) : G (LeftGeneralBox w2) :=
  match lgwm with
  | left_general_match_none
    => fmap (@Box_to_LeftGeneralBox One One)
            (returnGen (box (fun (p : Pat One) => output unit)))
  | left_general_match_unitary uw
    => let wt := (UnitaryWType_to_WType uw) in
       oneOf [ fmap Box_to_LeftGeneralBox
                    (fmap (fun (ug : Unitary wt) =>
                             (@boxed_gate wt wt ug))
                          (genUnitaryWTyped uw)) ;
                 fmap Box_to_LeftGeneralBox
                      (returnGen (@id_circ wt))
             ] (* Unitary, id *)
  | left_general_match_bit_bit
    => oneOf [ fmap Box_to_LeftGeneralBox
                    (returnGen
                       (box (fun (p : Pat Bit) =>
                               gate BNOT p (fun (p' : Pat Bit) =>
                                              output p')))) ;
                 fmap Box_to_LeftGeneralBox
                      (returnGen (@id_circ Bit))
             ] (* BNOT, id *)
  | left_general_match_one_qubit
    => oneOf [ fmap Box_to_LeftGeneralBox
                    (returnGen (init false)) ;
                 fmap Box_to_LeftGeneralBox
                      (returnGen (init true))
             ] (* init0, init1 *)
  | left_general_match_one_bit
    => oneOf [ fmap Box_to_LeftGeneralBox
                    (returnGen (new false)) ;
                 fmap Box_to_LeftGeneralBox
                      (returnGen (new true))
             ] (* new0, new1 *)
  | left_general_match_qubit_bit
    => fmap Box_to_LeftGeneralBox
            (returnGen (@boxed_gate Qubit Bit meas)) (* meas *)
  | left_general_match_qubit_qubit
    => oneOf [ fmap Box_to_LeftGeneralBox
                    (returnGen (@boxed_gate Qubit Qubit measQ)) ;
                 fmap Box_to_LeftGeneralBox
                      (fmap (fun (ug : Unitary Qubit) =>
                               (@boxed_gate Qubit Qubit ug))
                            (genUnitaryWTyped Unitary_Qubit)) ;
                 fmap Box_to_LeftGeneralBox
                      (returnGen (@id_circ Qubit))
             ] (* measQ, Unitary, id *)
  | left_general_match_bit_one
    => fmap Box_to_LeftGeneralBox
            (returnGen (@boxed_gate Bit One discard)) (* discard *)
  | left_general_match_bit_qubit
    => fmap Box_to_LeftGeneralBox
            (returnGen
               (box (fun (p0 : Pat Bit) =>
                       gate_ nv ← init0 @();
                         gate_ (p1, nv') ←
                               (U (bit_ctrl _X)) @(pair p0 nv);
                         gate_ () ← discard @p1;
                         output nv')))
  (* init0 nv -> bit_ctrl bit nv -> discard bit -> output nv' *)
  | left_general_match_qubit_one
    => fmap Box_to_LeftGeneralBox
            (returnGen
               (box (fun (p0 : Pat Qubit) =>
                       gate_ p1 ← meas @p0;
                         gate_ () ← discard @p1;
                         output unit)))
  (* meas -> discard (or, assert0, assert1) *)
  | left_general_match_l_w2 w2' m1 m2
    => (liftGen2 (fun (gc1 : LeftGeneralBox w2')
                      (gc2 : LeftGeneralBoxRightOne) =>
                    let c1 := (LeftGeneralBox_to_Box gc1) in
                    let c2 := (LeftGeneralBoxRightOne_to_Box gc2) in
                    (@Box_to_LeftGeneralBox _ w2'
                                            (box_ p12 ⇒ 
                                                  let_ (p1,p2) ← output p12; 
                                               let_ p1'     ← unbox c1 p1;
                                               let_ p2'     ← unbox c2 p2; 
                                               p1')))
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatch m1)
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatchRightOne m2)
       )
  | left_general_match_r_w2 w2' m1 m2
    => (liftGen2 (fun (gc1 : LeftGeneralBox w2')
                      (gc2 : LeftGeneralBoxRightOne) =>
                    let c1 := (LeftGeneralBox_to_Box gc1) in
                    let c2 := (LeftGeneralBoxRightOne_to_Box gc2) in
                    (@Box_to_LeftGeneralBox _ w2'
                                            (box_ p12 ⇒ 
                                                  let_ (p1,p2) ← output p12; 
                                               let_ p1'     ← unbox c2 p1;
                                               let_ p2'     ← unbox c1 p2; 
                                               p2')))
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatch m1)
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatchRightOne m2)
       )
  | left_general_match_w1_l w2l w2r m1 m2
    => (liftGen2 (fun (gc1 : LeftGeneralBox w2l)
                      (gc2 : LeftGeneralBoxLeftOne w2r) =>
                    let c1 := (LeftGeneralBox_to_Box gc1) in
                    let c2 := (LeftGeneralBoxLeftOne_to_Box gc2) in
                    (@Box_to_LeftGeneralBox _ (Tensor w2l w2r)
                                            (box_ p ⇒ 
                                                  let_ p1'     ← unbox c1 p;
                                               let_ p2'     ← unbox c2 unit; 
                                               (p1', p2'))))
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatch m1)
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatchLeftOne m2)
       )
  | left_general_match_w1_r w2l w2r m1 m2
    => (liftGen2 (fun (gc1 : LeftGeneralBox w2r)
                      (gc2 : LeftGeneralBoxLeftOne w2l) =>
                    let c1 := (LeftGeneralBox_to_Box gc1) in
                    let c2 := (LeftGeneralBoxLeftOne_to_Box gc2) in
                    (@Box_to_LeftGeneralBox _ (Tensor w2l w2r)
                                            (box_ p ⇒ 
                                                  let_ p1'     ← unbox c2 unit;
                                               let_ p2'     ← unbox c1 p; 
                                               (p1', p2'))))
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatch m1)
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatchLeftOne m2)
       )
  | left_general_match_w1_w2 w2l w2r m1 m2
    => (liftGen2 (fun (gc1 : LeftGeneralBox w2l)
                      (gc2 : LeftGeneralBox w2r) =>
                    let c1 := (LeftGeneralBox_to_Box gc1) in
                    let c2 := (LeftGeneralBox_to_Box gc2) in
                    (@Box_to_LeftGeneralBox _ (Tensor w2l w2r) (inPar c1 c2)))
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatch m1)
                 (genLeftGeneralBoxFromLeftGeneralWTypeMatch m2)
       )
  end.
Next Obligation.
  destruct w2; destruct gc1; simpl; reflexivity.
Qed.
Next Obligation.
  destruct w2; destruct gc1; simpl; reflexivity.
Qed.
Next Obligation.
  destruct w2l; destruct gc1; simpl; reflexivity.
Qed.
Next Obligation.
  destruct w2r; destruct gc1; simpl; reflexivity.
Qed.
Next Obligation.
  destruct w2l; destruct w2r; destruct gc1; destruct gc2; simpl; reflexivity.
Qed.

Definition genLeftGeneralBoxWTyped (w1 : WType) (w2 : WType) : G (LeftGeneralBox w2) :=
  bindGen (genLeftGeneralWTypeMatch w1 w2) genLeftGeneralBoxFromLeftGeneralWTypeMatch.
*)
(* BoxSeq *)
Inductive BoxSeq : WType -> WType -> Set :=
| box_seq_single : forall {w1 w2 : WType}, Box w1 w2 -> BoxSeq w1 w2
| box_seq_append : forall {w1 w2 w3 : WType},
    Box w1 w2 -> BoxSeq w2 w3 -> BoxSeq w1 w3.

Fixpoint BoxSeq_to_WType {w1 w2 : WType} (bs : BoxSeq w1 w2) : WType * WType :=
  Datatypes.pair w1 w2.
Check BoxSeq_to_WType.

Fixpoint BoxSeq_to_Box {wb we : WType} (bs : BoxSeq wb we)
  : Box wb we :=
  match bs with
  | box_seq_single w1 w2 b => b
  | box_seq_append w1 w2 w3 b1 bs2 =>
    (box_ p1 ⇒ 
          let_ p2 ← unbox b1 p1;
       unbox (BoxSeq_to_Box bs2) p2)
  end.
Check BoxSeq_to_Box.

Fixpoint genBoxSeqWTypedSized (w1 w2 : WType) (len : nat) : G (BoxSeq w1 w2) :=
  match len with
  | O => fmap (fun (b : Box w1 w2) => @box_seq_single w1 w2 b)
              (genBoxWTyped w1 w2)
  | S len' => bindGen genWType
                      (fun w : WType =>
                         (liftGen2 (@box_seq_append w1 w w2)
                                   (genBoxWTyped w1 w)
                                   (genBoxSeqWTypedSized w w2 len')))
  end.

Fixpoint genBoxWTypedSized (w1 w2 : WType) (len : nat) : G (Box w1 w2) :=
  fmap BoxSeq_to_Box (genBoxSeqWTypedSized w1 w2 len).

Sample (genBoxWTypedSized One Qubit 0).

Definition box_example_1 : (Box One Qubit) := box (fun (unit : Pat One) => (gate (init0) (unit) (fun (q0: Pat Qubit) => (output (q0))))).
Lemma WT_box_example_1 : Typed_Box box_example_1.
Proof. type_check. Qed.

(*
Require Import Denotation.

Check Superoperator.
Check denote.
Print Superoperator.
Check Superoperator 1 2.
Check (Id 1).
Check (denote box_example_1).
Check (denote box_example_1) (Id 1).
Check (denote box_example_1) (Id 1) O O.
Lemma test : forall {b : Box One Qubit}, (denote b) (Id 1) O O = C0. Abort.
Check C1.
Check (Id (2 ^ ⟦ One ⟧)).
Fixpoint eq_denotation_qasm_simulator (b : Box One Qubit) :=
  ((denote b) (Id 1) O O) = C1?.

QuickChick (forAll (genBoxWTypedSized One Qubit 2) (eq_denotation_qasm_simulator Qubit)).

Definition WT_RandomBox (w1 w2 : WType) (b : Box w1 w2) :=
  Typed_Box b.

QuickChick (forAll (genBoxWTypedSized One Qubit 2) (WT_RandomBox One Qubit)).
  type_check (GeneralDBCircuit_to_DBCircuit gdb).
*)

(* --------------------------------- Repository ------------------------------------ *)


(* AuxiliaryCircuit *)
Inductive AuxiliaryCircuit : WType -> Set :=
| aux_output {w} (p : Pat w) : AuxiliaryCircuit w
| aux_gate {w} (gg : GeneralGate) (pw1 : Pat (fst (GeneralGate_to_WType gg)))
           (b : Pat (snd (GeneralGate_to_WType gg)) -> AuxiliaryCircuit w)
  : AuxiliaryCircuit w
| aux_lift {w} (pb : Pat Bit) (f : bool -> AuxiliaryCircuit w)
  : AuxiliaryCircuit w.

Instance showAuxiliaryCircuit {w} : Show (AuxiliaryCircuit w) :=
  {| show := 
       let fix aux {w} v t := 
           match t with
           | aux_output _ p => "aux_output (" ++ (show p) ++ ")"
           | aux_gate _ gg p t' =>
             let nv := (v + (size_wtype (snd (GeneralGate_to_WType gg)))) in
             "aux_gate (" ++ (show gg) ++ ") (" ++ (show p) ++ ") ("
                      ++ "fun (" ++ (show (get_new_pat_of (snd (GeneralGate_to_WType gg)) v))
                      ++ ") => ("
                      ++ (aux nv (t' (get_new_pat_of (snd (GeneralGate_to_WType gg)) v)))
                      ++ "))"
           | aux_lift _ p f =>
             "aux_lift (" ++ (show p) ++ ") ("
                         ++ (aux v (f true)) ++ ") (" ++ (aux v (f false)) ++ ")"
           end
       in aux 0
  |}.

Eval compute in (show (aux_output (pair (qubit 1) (bit 2)))).

Fixpoint AuxiliaryCircuit_to_WType {w} (ac : AuxiliaryCircuit w) : WType := w.
Check AuxiliaryCircuit_to_WType.
Fixpoint AuxiliaryCircuit_to_Circuit {w} (ac : AuxiliaryCircuit w) : Circuit w :=
  match ac with
  | aux_output _ p => output p
  | aux_gate _ gg pw1 ac' => gate (GeneralGate_to_Gate gg) pw1
                                  (fun (pw2 : Pat (snd (GeneralGate_to_WType gg))) =>
                                     AuxiliaryCircuit_to_Circuit (ac' pw2))
  | aux_lift _ pb f => lift pb
                            (fun (b : bool) =>
                               match b with
                               | true => (AuxiliaryCircuit_to_Circuit (f true))
                               | false => (AuxiliaryCircuit_to_Circuit (f false))
                               end)
  end.
Check AuxiliaryCircuit_to_Circuit.

(* GeneralCircuit *)
Inductive GeneralCircuit :=
| general_circuit : forall (w : WType), AuxiliaryCircuit w -> GeneralCircuit.

Check GeneralCircuit.

Instance showGeneralCircuit : Show (GeneralCircuit) :=
  {| show := 
       let fix aux t := 
           match t with
           | general_circuit w ac => "general_circuit (" ++ (show ac) ++ ")"
           end
       in aux
  |}.

Eval compute in (show (general_circuit 
                         Qubit
                         (aux_gate general_init0 (unit)
                                   (fun (q0 : Pat Qubit) => (aux_output q0))))).

Fixpoint GeneralCircuit_to_WType (gc : GeneralCircuit) : WType :=
  match gc with
  | general_circuit w ac => w
  end.
Check GeneralCircuit_to_WType.
Fixpoint GeneralCircuit_to_Circuit (gc : GeneralCircuit)
  : Circuit (GeneralCircuit_to_WType gc) :=
  match gc with
  | general_circuit w ac => AuxiliaryCircuit_to_Circuit ac
  end.
Check GeneralCircuit_to_Circuit.

(* AuxiliaryBox *)
Inductive AuxiliaryBox :=
| auxiliary_box : forall (w1 w2 : WType), (GeneralPat -> GeneralCircuit) -> AuxiliaryBox.

Instance showAuxiliaryBox : Show (AuxiliaryBox) :=
  {| show := 
       let fix aux_circ {w} v t :=
           match t with
           | aux_output _ p => "aux_output (" ++ (show p) ++ ")"
           | aux_gate _ gg p t' =>
             let nv := (v + (size_wtype (snd (GeneralGate_to_WType gg)))) in
             "aux_gate (" ++ (show gg) ++ ") (" ++ (show p) ++ ") ("
                      ++ "fun (" ++ (show (get_new_pat_of (snd (GeneralGate_to_WType gg)) v))
                      ++ ") => ("
                      ++ (aux_circ nv (t' (get_new_pat_of (snd (GeneralGate_to_WType gg)) v)))
                      ++ "))"
           | aux_lift _ p f =>
             "aux_lift (" ++ (show p) ++ ") ("
                         ++ (aux_circ v (f true)) ++ ") (" ++ (aux_circ v (f false)) ++ ")"
           end
       in
       let fix aux_circ' v t :=
           match t with
           | general_circuit w2 ac => aux_circ v ac
           end
       in 
       let fix aux_box t := 
           match t with
           | auxiliary_box w1 w2 b =>
             let sv := (size_wtype w1) in
             "auxiliary_box (" ++ "fun (" ++ show (get_new_pat_of w1 0) ++ ") => ("
                               ++ (aux_circ' sv (b (Pat_to_GeneralPat (get_new_pat_of w1 0))))
                               ++ "))"
           end
       in aux_box
  |}.

Fixpoint AuxiliaryBox_to_WType (ab : AuxiliaryBox) : WType * WType :=
  match ab with
  | auxiliary_box w1 w2 b => Datatypes.pair w1 w2
  end.
Check AuxiliaryBox_to_WType.

