From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Contexts.
Require Import HOASCircuits.
Require Import HOASLib.
Require Import DBCircuits.
Require Import Generator.
Require Import DBGenerator.
Require Import TypeChecking.

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
    gate_ a ← H @a0;
    gate_ b ← init0 @();
    gate_ (a1, b1) ← CNOT @(Contexts.pair a b);
    gate_ b2       ← meas @(b1);
    gate_ ()       ← discard @(b2);   
    output a1.
Eval compute in (show test_circ).

Definition bell00 : Box One (Qubit ⊗ Qubit) :=
  box_ () ⇒  
    gate_ a0 ← init0 @();
    gate_ a ← H @a0;
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
| match_1_wr : forall {wl wr w : WType},
    WTypeMatch wl wr -> WTypeMatch w One -> WTypeMatch (Tensor wl w) wr
| match_2_wr : forall {wl wr w : WType},
    WTypeMatch wl wr -> WTypeMatch w One -> WTypeMatch (Tensor w wl) wr
| match_wl_1 : forall {wl wr w : WType},
    WTypeMatch wl wr -> WTypeMatch One w -> WTypeMatch wl (Tensor wr w)
| match_wl_2 : forall {wl wr w : WType},
    WTypeMatch wl wr -> WTypeMatch One w -> WTypeMatch wl (Tensor w wr)
| match_wl_wr : forall {wll wlr wrl wrr : WType},
    WTypeMatch wll wrl -> WTypeMatch wlr wrr -> WTypeMatch (Tensor wll wlr) (Tensor wrl wrr)
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
           | match_1_wr wl wr w m1 m2 => "match (" ++ (aux m1) ++ ") ("
                                                   ++ (@aux  w One m2) ++ ")"
           | match_2_wr wl wr w m1 m2 => "match (" ++ (aux m2) ++ ") (" ++ (aux m1) ++ ")"
           | match_wl_1 wl wr w m1 m2 => "match (" ++ (aux m1) ++ ") (" ++ (aux m2) ++ ")"
           | match_wl_2 wl wr w m1 m2 => "match (" ++ (aux m2) ++ ") (" ++ (aux m1) ++ ")"
           | match_wl_wr wll wlr wrl wrr m1 m2 => "match (" ++ (aux m1) ++ ") ("
                                                            ++ (aux m2) ++ ")"
         end
       in aux
  |}.

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
Program Fixpoint GeneralWTypeMatchLeftOne_to_WTypeMatch (gwm : GeneralWTypeMatchLeftOne)
  : WTypeMatch One (GeneralWTypeMatchLeftOne_to_WType gwm)
  :=
    match gwm with
    | general_match_left_one_none         => match_none
    | general_match_left_one_bit          => match_one_bit
    | general_match_left_one_qubit        => match_one_qubit
    | general_match_left_one_tensor m1 m2 =>
      (@match_wl_1 One
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
      (@match_1_wr (GeneralWTypeMatchRightOne_to_WType m1)
                   One
                   (GeneralWTypeMatchRightOne_to_WType m2)
                   (GeneralWTypeMatchRightOne_to_WTypeMatch m1)
                   (GeneralWTypeMatchRightOne_to_WTypeMatch m2))
    end.
Check GeneralWTypeMatchRightOne_to_WTypeMatch.
Fixpoint genGeneralWTypeMatchRightOne (w2 : WType) : G (GeneralWTypeMatchRightOne) :=
  match w2 with
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
| general_match_1_wr        :
    GeneralWTypeMatch -> GeneralWTypeMatchRightOne -> GeneralWTypeMatch
| general_match_2_wr        :
    GeneralWTypeMatch -> GeneralWTypeMatchRightOne -> GeneralWTypeMatch
| general_match_wl_1        :
    GeneralWTypeMatch -> GeneralWTypeMatchLeftOne -> GeneralWTypeMatch
| general_match_wl_2        :
    GeneralWTypeMatch -> GeneralWTypeMatchLeftOne -> GeneralWTypeMatch
| general_match_wl_wr       : GeneralWTypeMatch -> GeneralWTypeMatch -> GeneralWTypeMatch
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
  | general_match_1_wr m1 m2  =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2l := (GeneralWTypeMatchRightOne_to_WType m2) in
    (Datatypes.pair (Tensor w1l w2l) w1r)
  | general_match_2_wr m1 m2  =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2l := (GeneralWTypeMatchRightOne_to_WType m2) in
    (Datatypes.pair (Tensor w2l w1l) w1r)
  | general_match_wl_1 m1 m2  =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2r := (GeneralWTypeMatchLeftOne_to_WType m2) in
    (Datatypes.pair w1l (Tensor w1r w2r))
  | general_match_wl_2 m1 m2  =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2r := (GeneralWTypeMatchLeftOne_to_WType m2) in
    (Datatypes.pair w1l (Tensor w2r w1r))
  | general_match_wl_wr m1 m2 =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2l := (fst (GeneralWTypeMatch_to_WType m2)) in
    let w2r := (snd (GeneralWTypeMatch_to_WType m2)) in
    (Datatypes.pair (Tensor w1l w2l) (Tensor w1r w2r))
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
  | general_match_1_wr m1 m2  =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2l := (GeneralWTypeMatchRightOne_to_WType m2) in
    @match_1_wr w1l w1r w2l
                (GeneralWTypeMatch_to_WTypeMatch m1)
                (GeneralWTypeMatchRightOne_to_WTypeMatch m2)
  | general_match_2_wr m1 m2  =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2l := (GeneralWTypeMatchRightOne_to_WType m2) in
    @match_2_wr w1l w1r w2l
                (GeneralWTypeMatch_to_WTypeMatch m1)
                (GeneralWTypeMatchRightOne_to_WTypeMatch m2)
  | general_match_wl_1 m1 m2  =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2r := (GeneralWTypeMatchLeftOne_to_WType m2) in
    @match_wl_1 w1l w1r w2r
                (GeneralWTypeMatch_to_WTypeMatch m1)
                (GeneralWTypeMatchLeftOne_to_WTypeMatch m2)
  | general_match_wl_2 m1 m2  =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2r := (GeneralWTypeMatchLeftOne_to_WType m2) in
    @match_wl_2 w1l w1r w2r
                (GeneralWTypeMatch_to_WTypeMatch m1)
                (GeneralWTypeMatchLeftOne_to_WTypeMatch m2)
  | general_match_wl_wr m1 m2 =>
    let w1l := (fst (GeneralWTypeMatch_to_WType m1)) in
    let w1r := (snd (GeneralWTypeMatch_to_WType m1)) in
    let w2l := (fst (GeneralWTypeMatch_to_WType m2)) in
    let w2r := (snd (GeneralWTypeMatch_to_WType m2)) in
    @match_wl_wr w1l w2l w1r w2r
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
      liftGen2 general_match_wl_1
               (genGeneralWTypeMatchRec step' One l) (genGeneralWTypeMatchLeftOne r)
    | Bit, One => returnGen general_match_bit_one
    | Bit, Bit => returnGen general_match_bit_bit
    | Bit, Qubit => returnGen general_match_bit_qubit
    | Bit, Tensor l r =>
      liftGen2 general_match_wl_1
               (genGeneralWTypeMatchRec step' Bit l) (genGeneralWTypeMatchLeftOne r)
    | Qubit, One => returnGen general_match_qubit_one
    | Qubit, Bit => returnGen general_match_qubit_bit
    | Qubit, Qubit => returnGen general_match_qubit_qubit
    | Qubit, Tensor l r =>
      liftGen2 general_match_wl_1
               (genGeneralWTypeMatchRec step' Qubit l) (genGeneralWTypeMatchLeftOne r)
    | Tensor l r, One =>
      liftGen2 general_match_1_wr
               (genGeneralWTypeMatchRec step' l One) (genGeneralWTypeMatchRightOne r)
    | Tensor l r, Bit =>
      liftGen2 general_match_1_wr
               (genGeneralWTypeMatchRec step' l Bit) (genGeneralWTypeMatchRightOne r)
    | Tensor l r, Qubit =>
      liftGen2 general_match_1_wr
               (genGeneralWTypeMatchRec step' l Qubit) (genGeneralWTypeMatchRightOne r)
    | Tensor ll lr, Tensor rl rr =>
      oneOf [ liftGen2 general_match_1_wr
                       (genGeneralWTypeMatchRec step' ll (Tensor rl rr))
                       (genGeneralWTypeMatchRightOne lr) ;
                liftGen2 general_match_2_wr
                         (genGeneralWTypeMatchRec step' lr (Tensor rl rr))
                         (genGeneralWTypeMatchRightOne ll) ;
                liftGen2 general_match_wl_1
                         (genGeneralWTypeMatchRec step' (Tensor ll lr) rl)
                         (genGeneralWTypeMatchLeftOne rr) ;
                liftGen2 general_match_wl_2
                         (genGeneralWTypeMatchRec step' (Tensor ll lr) rr)
                         (genGeneralWTypeMatchLeftOne rl) ;
                liftGen2 general_match_wl_wr
                         (genGeneralWTypeMatchRec step' ll rl)
                         (genGeneralWTypeMatchRec step' lr rr)
            ]
    end
  end.

Fixpoint count_pair_in_WType (w : WType) : nat :=
  match w with
  | Tensor l r => 1 + (count_pair_in_WType l) + (count_pair_in_WType r)
  | _ => O
  end.

Definition genGeneralWTypeMatch (w1 : WType) (w2 : WType) : G (GeneralWTypeMatch) :=
(*
 count_pair_in_WType (Tensor w1 w2) = 1 + (count_pair_in_WType w1) + (count_pair_in_WType w2)
 *)
  (genGeneralWTypeMatchRec (count_pair_in_WType (Tensor w1 w2)) w1 w2).

(* GeneralBox *)
Inductive GeneralBox :=
| general_box : forall {w1 w2 : WType}, Box w1 w2 -> GeneralBox.

Check GeneralBox.

Instance showGeneralBox : Show (GeneralBox) :=
  {| show := 
       let fix aux t := 
           match t with
           | general_box w1 w2 b => "general_box (" ++ (show) b ++ ")"
           end
       in aux
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
Fixpoint Box_to_GeneralBox {w1 w2 : WType} (b : Box w1 w2) : GeneralBox :=
  general_box b.
Check Box_to_GeneralBox.

(* Generator for GeneralBox composed of inPar and inSeq *)
Fixpoint genGeneralBoxFromGeneralWTypeMatchLeftOne
         (gwm : GeneralWTypeMatchLeftOne) : G GeneralBox :=
  match gwm with
  | general_match_left_one_none  => fmap (@Box_to_GeneralBox One One)
                                         (returnGen (box (fun (p : Pat One) => output unit)))
  | general_match_left_one_bit   => oneOf [ fmap (@Box_to_GeneralBox One Bit)
                                                 (returnGen new0) ;
                                              fmap (@Box_to_GeneralBox One Bit)
                                                   (returnGen new1)
                                          ] (* new0, new1 *)
  | general_match_left_one_qubit => oneOf [ fmap Box_to_GeneralBox
                                                 (returnGen init0) ;
                                              fmap Box_to_GeneralBox
                                                   (returnGen init1)
                                          ] (* init0, init1 *)
  | general_match_left_one_tensor m1 m2 =>
    (liftGen2 (fun (gc1 gc2 : GeneralBox) =>
                 let c1 := (GeneralBox_to_Box gc1) in
                 let c2 := (GeneralBox_to_Box gc2) in
                 (box_ _ ⇒ 
                       let_ p1'     ← unbox c1 unit;
                    let_ p2'     ← unbox c2 unit; 
                    (p1', p2')))
              (genGeneralBoxFromGeneralWTypeMatchLeftOne m1)
              (genGeneralBoxFromGeneralWTypeMatchLeftOne m2)
    )
  end.

Fixpoint genGeneralBoxFromGeneralWTypeMatchRightOne
         (gwm : GeneralWTypeMatchRightOne) : G GeneralBox :=
  match gwm with
  | general_match_right_one_none   : returnGen (box (fun (p : Pat One) => output unit))
  | general_match_right_one_bit    : returnGen (@boxed_gate Bit One discard)
  | general_match_right_one_qubit  : returnGen
                                       (box (fun (p0 : Pat Qubit) =>
                                               gate meas p0
                                                    (fun (p1 : Pat Bit) =>
                                                       gate discard p1
                                                            (fun (p2 : Pat One) =>
                                                               output unit))))
  | general_match_right_one_tensor m1 m2 :
      (bindGen2 (fun (gc1 gc2 : GeneralBox) =>
                   let c1 := (GeneralBox_to_Box gc1) in
                   let c2 := (GeneralBox_to_Box gc2) in
                   (box_ _ ⇒
                         let_ (p1,p2) ← output p12;
                      let_ p1'     ← unbox c1 p1;
                      let_ p2'     ← unbox c2 p2; 
                      (unit)))
                (genGeneralBoxFromGeneralWTypeMatchRightOne m1)
                (genGeneralBoxFromGeneralWTypeMatchRightOne m2)
      )
  end.

Fixpoint genGeneralBoxFromGeneralWTypeMatch (gwm : GeneralWTypeMatch) : G GeneralBox :=
  match gwm with
  | general_match_none        => returnGen (box (fun (p : Pat One) => output unit))
  | general_match_unitary uw  => let wt := (UnitaryWType_to_WType uw) in
                                 oneOf [ returnGen (fmap (fun (ug : Unitary wt) =>
                                                            (@boxed_gate wt wt ug))
                                                         (genUnitaryWTyped O uw)) ;
                                           returnGen (@id_circ wt)
                                       ] (* Unitary, id *)
  | general_match_bit_bit     : oneOf [ returnGen (box (fun (p : Pat Bit) =>
                                                          gate BNOT p (fun (p' : Pat Bit) =>
                                                                         output p'))) ;
                                          returnGen (@id_circ Bit)
                                      ] (* BNOT, id *)
  | general_match_one_qubit   : oneOf [ returnGen init0 ;
                                          returnGen init1
                                      ] (* init0, init1 *)
  | general_match_one_bit     : oneOf [ returnGen new0 ;
                                          returnGen new1
                                      ] (* new0, new1 *)
  | general_match_qubit_bit   : (@boxed_gate Bit Bit meas) (* meas *)
  | general_match_qubit_qubit : oneOf [ returnGen (@boxed_gate Qubit Qubit measQ) ;
                                          returnGen
                                            (fmap (fun (ug : Unitary Qubit) =>
                                                     (@boxed_gate Qubit Qubit ug))
                                                  (genUnitaryWTyped O Unitary_Qubit)) ;
                                          returnGen (@id_circ Qubit)
                                      ] (* measQ, Unitary, id *)
  | general_match_bit_one     : returnGen (@boxed_gate Bit One discard) (* discard *)
  | general_match_bit_qubit   : returnGen
                                  (box (fun (p0 : Pat Bit) =>
                                          gate init0 unit
                                               (fun (nv : Pat Qubit) =>
                                                  gate (U (bit_ctrl X) p0
                                                          (fun (nv' : Pat Qubit) =>
                                                             gate discard p0
                                                                  (fun (_ : Pat One =>
                                                                        output nv')))))))
  (* init0 nv -> bit_ctrl bit nv -> discard bit -> output nv' *)
  | general_match_qubit_one   : returnGen
                                  (box (fun (p0 : Pat Qubit) =>
                                          gate meas p0
                                               (fun (p1 : Pat Bit) =>
                                                  gate discard p1
                                                       (fun (p2 : Pat One) =>
                                                          output unit))))
  (* meas -> discard (or, assert0, assert1) *)
  | general_match_1_wr m1 m2  : (bindGen2 (fun (gc1 gc2 : GeneralBox) =>
                                             let c1 := (GeneralBox_to_Box gc1) in
                                             let c2 := (GeneralBox_to_Box gc2) in
                                             (box_ p12 ⇒ 
                                                   let_ (p1,p2) ← output p12; 
                                                let_ p1'     ← unbox c1 p1;
                                                let_ p2'     ← unbox c2 p2; 
                                                p1'))
                                          (genGeneralBoxFromGeneralWTypeMatch m1)
                                          (genGeneralBoxFromGeneralWTypeMatchRightOne m2)
                                )
  | general_match_2_wr m1 m2  : (bindGen2 (fun (gc1 gc2 : GeneralBox) =>
                                             let c1 := (GeneralBox_to_Box gc1) in
                                             let c2 := (GeneralBox_to_Box gc2) in
                                             (box_ p12 ⇒ 
                                                   let_ (p1,p2) ← output p12; 
                                                let_ p1'     ← unbox c1 p1;
                                                let_ p2'     ← unbox c2 p2; 
                                                p2'))
                                          (genGeneralBoxFromGeneralWTypeMatch m1)
                                          (genGeneralBoxFromGeneralWTypeMatchRightOne m2)
                                )
  | general_match_wl_1 m1 m2  : (bindGen2 (fun (gc1 gc2 : GeneralBox) =>
                                             let c1 := (GeneralBox_to_Box gc1) in
                                             let c2 := (GeneralBox_to_Box gc2) in
                                             (box_ p ⇒ 
                                                   let_ p1'     ← unbox c1 p;
                                                let_ p2'     ← unbox c2 unit; 
                                                (p1', p2')))
                                          (genGeneralBoxFromGeneralWTypeMatch m1)
                                          (genGeneralBoxFromGeneralWTypeMatchLeftOne m2)
                                )
  | general_match_wl_2 m1 m2  : (bindGen2 (fun (gc1 gc2 : GeneralBox) =>
                                             let c1 := (GeneralBox_to_Box gc1) in
                                             let c2 := (GeneralBox_to_Box gc2) in
                                             (box_ p ⇒ 
                                                   let_ p1'     ← unbox c1 unit;
                                                let_ p2'     ← unbox c2 p; 
                                                (p1', p2')))
                                          (genGeneralBoxFromGeneralWTypeMatch m1)
                                          (genGeneralBoxFromGeneralWTypeMatchLeftOne m2)
                                )
  | general_match_wl_wr m1 m2 : (bindGen2 (fun (gc1 gc2 : GeneralBox) =>
                                             let c1 := (GeneralBox_to_Box gc1) in
                                             let c2 := (GeneralBox_to_Box gc2) in
                                             (inPar c1 c2))
                                          (genGeneralBoxFromGeneralWTypeMatch m1)
                                          (genGeneralBoxFromGeneralWTypeMatch m2)
                                )
  end.

Definition genGeneralBoxWTypedAux (w1 : WType) (w2 : WType) : G GeneralBox :=
  bindGen genGeneralWTypeMatch genGeneralBoxFromGeneralWTypeMatch.

Fixpoint genGeneralBoxWTypedSized (w1 : WType) (w2 : WType) (len : nat)
  : G GeneralBox :=
  match len with
  | O => genBoxWTypedOne w1 w2
  | S len' => fmap (fun w : WType => liftGen2 inSeq (genGeneralBoxWTypedAux w1 w)
                                              (genBoxWTypedSized w w2 len'))
                   genWType
  end.








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
Eval compute in (show (auxiliary_box One One (fun (x : GeneralPat) => output x))).

Fixpoint AuxiliaryBox_to_WType (ab : AuxiliaryBox) : WType * WType :=
  match ab with
  | auxiliary_box w1 w2 b => Datatypes.pair w1 w2
  end.
Check AuxiliaryBox_to_WType.
Fixpoint AuxiliaryBox_to_Box (ab : AuxiliaryBox) :
  Box (fst (AuxiliaryBox_to_WType ab)) (snd (AuxiliaryBox_to_WType ab)) :=
  match ab with
  | auxiliary_box w1 w2 b =>
    (fun (p : Pat w1) => (GeneralCircuit_to_Circuit (b (Pat_to_GeneralPat p))))
  end.
Check AuxiliaryBox_to_Box.

(* GeneralBox *)
Inductive GeneralBox :=
| general_box : (GeneralPat -> GeneralCircuit) -> GeneralBox.

Check GeneralBox.

Instance showGeneralBox : Show (GeneralBox) :=
  {| show := 
       let fix aux_box t := 
           match t with
           | general_box b => "box (" ++ "fun (input : GeneralPat) => ("
                              ++ (show aux_circ sv (c (get_new_pat_of w1 0)))
                               ++ "))"
           end
       in aux_box
  |}.
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
Eval compute in (show (general_box One One (box (fun (x : Pat One) => output x)))).

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

