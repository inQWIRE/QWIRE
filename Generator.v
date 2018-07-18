From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Contexts.
Require Import HOASCircuits.
Require Import DBCircuits.

Require Import String. Open Scope string.
Require Import Reals.

Open Scope circ_scope.

(*
Require Import List.
Import ListNotations.
*)

(* WType
  Inductive WType := Qubit | Bit | One | Tensor : WType -> WType -> WType.
*)
Instance showWType : Show (WType) :=
  {| show := 
       let fix aux t :=
         match t with
           | Qubit => "Qubit"
           | Bit => "Bit"
           | One => "One"
           | Tensor l r => "Tensor (" ++ aux l ++ ") (" ++ aux r ++ ")"
         end
       in aux
  |}.

Eval compute in (show (Tensor Qubit Qubit)).

Check frequency.
Fixpoint genWTypeSized (sz : nat) : G WType :=
  match sz with
  | O => oneOf [returnGen Qubit ;
                  returnGen Bit ;
                  returnGen One
               ]
  | S sz' => freq [ (1, returnGen Qubit) ;
                      (1, returnGen Bit) ;
                      (1, returnGen One) ;
                      (3*sz, liftGen2 Tensor (genWTypeSized sz') (genWTypeSized sz'))
                  ]
  end.

Sample (genWTypeSized 3).

Definition genWType : G WType := bindGen arbitrary genWTypeSized.

Sample genWType.

(* Pat
  Inductive Pat : WType ->  Set :=
  | unit : Pat One
  | qubit : Var -> Pat Qubit
  | bit : Var -> Pat Bit
  | pair : forall {W1 W2}, Pat W1 -> Pat W2 -> Pat (W1 ⊗ W2).
*)

Require Import Ascii.
(* Nat to string converter *)
Definition natToDigit (n : nat) : ascii :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
  | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end.
Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match (n / 10)%nat with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.
Definition writeNat (n : nat) : string :=
  writeNatAux n n "".

Instance showNat : Show (nat) :=
  {| show := writeNat
  |}.

Eval compute in (show 10).

Instance showPat {w : WType} : Show (Pat w) :=
  {| show := 
       let fix aux {w} t :=
         match t with
           | unit => "unit"
           | qubit x => "qubit " ++ (writeNat x)
           | bit x => "bit " ++ (writeNat x)
           | pair W1 W2 l r => "pair (" ++ aux l ++ ") (" ++ aux r ++ ")"
         end
       in aux
  |}.

Eval compute in (show (pair (qubit 1) (bit 2))).

Fixpoint genPatWTyped (g : G Var) (w : WType) : G (Pat w) :=
  match w with
  | Qubit => liftGen qubit g
  | Bit => liftGen bit g
  | One => returnGen unit
  | Tensor l r => liftGen2 pair (genPatWTyped g l) (genPatWTyped g r)
  end.

Instance genPatW `{w : WType} : Gen (Pat w) :=
  { arbitrary := genPatWTyped arbitrary w }.

Fail Class Gen' {X : Type} `{Gen X} (Y : forall w : Type, w -> Type) := { arbitrary : G (Y X) }.

Sample (genPatWTyped (choose (0,3)) (Tensor (Tensor Qubit Bit) (One))).
Sample (genPatWTyped arbitrary (Tensor (Tensor Qubit Bit) (One))).

(*
Inductive GeneralPatType :=
| generalPatType : forall {w : WType} (pat : Pat w), GeneralPatType.

Instance showPatType : Show (GeneralPatType) :=
  {| show := 
       let fix aux t := 
         match t with
           | generalPatType _ p => "generalPatType (" ++ show p ++ ")"
         end
       in aux
  |}.

Eval compute in (show (generalPatType (pair (qubit 1) (bit 2)))).
*)

Inductive GeneralPat :=
| general_unit : GeneralPat
| general_qubit : Var -> GeneralPat
| general_bit : Var -> GeneralPat
| general_pair : GeneralPat -> GeneralPat -> GeneralPat.

Instance showGeneralPat : Show (GeneralPat) :=
  {| show := 
       let fix aux t := 
           match t with
           | general_unit => "general_unit"
           | general_qubit x => "general_qubit " ++ (writeNat x)
           | general_bit x => "general_bit " ++ (writeNat x)
           | general_pair l r => "general_pair (" ++ aux l ++ ") (" ++ aux r ++ ")"
           end
       in aux
  |}.

Eval compute in (show (general_pair (general_qubit 1) (general_bit 2))).

Fixpoint genGeneralPatWTyped (g : G Var) (w : WType) : G (GeneralPat) :=
  match w with
  | Qubit => liftGen general_qubit g
  | Bit => liftGen general_bit g
  | One => returnGen general_unit
  | Tensor l r => liftGen2 general_pair (genGeneralPatWTyped g l) (genGeneralPatWTyped g r)
  end.
Check genGeneralPatWTyped.

Definition genGeneralPat (g : G Var) : G GeneralPat :=
  bindGen genWType (genGeneralPatWTyped g).

Sample (genGeneralPat (choose (0,3))).

Derive GenSized for GeneralPat.

Fixpoint GeneralPat_to_WType (gp : GeneralPat) : WType :=
  match gp with
  | general_unit => One
  | general_qubit v => Qubit
  | general_bit v => Bit
  | general_pair l r => Tensor (GeneralPat_to_WType l) (GeneralPat_to_WType r)
  end.
Check GeneralPat_to_WType.
Fixpoint GeneralPat_to_Pat (gp : GeneralPat) : Pat (GeneralPat_to_WType gp) :=
  match gp with
  | general_unit => unit
  | general_qubit v => qubit v
  | general_bit v => bit v
  | general_pair l r => pair (GeneralPat_to_Pat l) (GeneralPat_to_Pat r)
  end.
Check GeneralPat_to_Pat.
Fixpoint Pat_to_GeneralPat {w : WType} (p : Pat w) : GeneralPat :=
  match p with
  | unit => general_unit
  | qubit v => general_qubit v
  | bit v => general_bit v
  | pair wl wr l r => general_pair (Pat_to_GeneralPat l) (Pat_to_GeneralPat r)
  end.
Check Pat_to_GeneralPat.

(* Unitary
  Inductive Unitary : WType -> Set := 
  | _H         : Unitary Qubit 
  | _X         : Unitary Qubit
  | _Y         : Unitary Qubit
  | _Z         : Unitary Qubit
  | _R_        : R -> Unitary Qubit 
  | ctrl      : forall {W} (U : Unitary W), Unitary (Qubit ⊗ W) 
  | bit_ctrl  : forall {W} (U : Unitary W), Unitary (Bit ⊗ W) 
*)

Inductive UnitaryWType :=
| Unitary_Qubit    : UnitaryWType
| Unitary_bit_ctrl : UnitaryWType -> UnitaryWType
| Unitary_ctrl     : UnitaryWType -> UnitaryWType.

Fixpoint UnitaryWType_to_WType (uw : UnitaryWType) : WType :=
  match uw with
  | Unitary_Qubit => Qubit
  | Unitary_bit_ctrl uw' => Tensor Bit (UnitaryWType_to_WType uw')
  | Unitary_ctrl uw' => Tensor Qubit (UnitaryWType_to_WType uw')
  end.

Instance showUnitaryWType : Show (UnitaryWType) :=
  {| show := 
       let fix aux t :=
         match t with
           | Unitary_Qubit => "Unitary_Qubit "
           | Unitary_bit_ctrl t' => "Unitary_bit_ctrl " ++ (aux t')
           | Unitary_ctrl t' => "Unitary_ctrl " ++ (aux t')
         end
       in aux
  |}.

Fixpoint genUnitaryWTypeSized (sz : nat) : G UnitaryWType :=
  match sz with
  | O => oneOf [returnGen Unitary_Qubit
               ]
  | S sz' => freq [ (2, returnGen Unitary_Qubit) ;
                      (sz, liftGen Unitary_bit_ctrl (genUnitaryWTypeSized sz')) ;
                      (sz, liftGen Unitary_ctrl (genUnitaryWTypeSized sz'))
                  ]
  end.

Sample (genUnitaryWTypeSized 3).

Definition genUnitaryWType : G UnitaryWType := bindGen arbitrary genUnitaryWTypeSized.

Sample (genUnitaryWType).

Definition print_real (r : R) : string := "(Real : To implement)" (* To implement *).

Instance showUnitary {w : WType} : Show (Unitary w) :=
  {| show := 
       let fix aux {w} t :=
         match t with
           | _H => "_H"
           | _X => "_X"
           | _Y => "_Y"
           | _Z => "_Z"
           | _R_ r => "_R_ " ++ (print_real r)
           | ctrl w u => "ctrl (" ++ (aux u) ++ ")"
           | bit_ctrl w u => "bit_ctrl (" ++ (aux u) ++ ")"
         end
       in aux
  |}.

Eval compute in (show (trans (bit_ctrl (ctrl _H)))).

Check frequency.

Fixpoint genUnitaryWTyped (uw : UnitaryWType) : G (Unitary (UnitaryWType_to_WType uw)) :=
  match uw with
  | Unitary_Qubit => oneOf [ returnGen _H ;
                               returnGen _X ;
                               returnGen _Y ;
                               returnGen _Z
(*
                               ; liftGen R_ (returnGen 1%R)
*)
                           ]
  | Unitary_bit_ctrl uw' => liftGen bit_ctrl (genUnitaryWTyped uw')
  | Unitary_ctrl uw' => liftGen ctrl (genUnitaryWTyped uw')
  end.

Sample (genUnitaryWTyped (Unitary_bit_ctrl (Unitary_ctrl Unitary_Qubit))).

Inductive GeneralUnitary :=
| general_H : GeneralUnitary
| general_X : GeneralUnitary
| general_Y : GeneralUnitary
| general_Z : GeneralUnitary
| general_R_ : R -> GeneralUnitary
| general_ctrl : GeneralUnitary -> GeneralUnitary
| general_bit_ctrl : GeneralUnitary -> GeneralUnitary.

Instance showGeneralUnitary : Show (GeneralUnitary) :=
  {| show := 
       let fix aux t := 
           match t with
           | general_H => "general_H"
           | general_X => "general_H"
           | general_Y => "general_H"
           | general_Z => "general_H"
           | general_R_ r => "general_R_ (" ++ (print_real r) ++ ")"
           | general_ctrl u => "general_ctrl (" ++ (aux u) ++ ")"
           | general_bit_ctrl u => "general_bit_ctrl (" ++ (aux u) ++ ")"
           end
       in aux
  |}.

Eval compute in (show (general_ctrl (general_H))).
(*
Eval compute in (show (general_trans (general_ctrl (general_H)))).
 *)

Fixpoint genGeneralUnitaryWTyped
         (uw : UnitaryWType) : G GeneralUnitary :=
  match uw with
  | Unitary_Qubit => oneOf [ returnGen general_H ;
                               returnGen general_X ;
                               returnGen general_Y ;
                               returnGen general_Z
(*
                               ; liftGen general_R_ (returnGen 1%R)
*)
                           ]
  | Unitary_bit_ctrl uw' =>
    liftGen general_bit_ctrl (genGeneralUnitaryWTyped uw')
  | Unitary_ctrl uw' =>
    liftGen general_ctrl (genGeneralUnitaryWTyped uw')
  end.

Sample (genGeneralUnitaryWTyped
          (Unitary_bit_ctrl (Unitary_ctrl Unitary_Qubit))).

Definition genGeneralUnitary (tn : nat) : G GeneralUnitary :=
  bindGen genUnitaryWType genGeneralUnitaryWTyped.

Sample (genGeneralUnitary 3).

Fixpoint GeneralUnitary_to_WType (gu : GeneralUnitary) : WType :=
  match gu with
  | general_H => Qubit
  | general_X => Qubit
  | general_Y => Qubit
  | general_Z => Qubit
  | general_R_ r => Qubit
  | general_ctrl gu' => Tensor Qubit (GeneralUnitary_to_WType gu')
  | general_bit_ctrl gu' => Tensor Bit (GeneralUnitary_to_WType gu')
  end.
Check GeneralUnitary_to_WType.
Fixpoint GeneralUnitary_to_Unitary
         (gu : GeneralUnitary) : Unitary (GeneralUnitary_to_WType gu) :=
  match gu with
  | general_H => _H
  | general_X => _X
  | general_Y => _Y
  | general_Z => _Z
  | general_R_ r => _R_ r
  | general_ctrl gu' => ctrl (GeneralUnitary_to_Unitary gu')
  | general_bit_ctrl gu' => bit_ctrl (GeneralUnitary_to_Unitary gu')
  end.
Check GeneralUnitary_to_Unitary.

(* Gate
  Inductive Gate : WType -> WType -> Set := 
  | U : forall {W} (u : Unitary W), Gate W W
  | BNOT     : Gate Bit Bit
  | init0   : Gate One Qubit
  | init1   : Gate One Qubit
  | new0    : Gate One Bit
  | new1    : Gate One Bit
  | meas    : Gate Qubit Bit
  | measQ   : Gate Qubit Qubit
  | discard : Gate Bit One
  | assert0 : Gate Qubit One
  | assert1 : Gate Qubit One.
 *)

Instance showGate {w1 w2 : WType} : Show (Gate w1 w2) :=
  {| show := 
       let fix aux t :=
         match t with
           | U _ u   => "U (" ++ (show u) ++ ")"
           | BNOT    => "BNOT"
           | init0   => "init0"
           | init1   => "init1"
           | new0    => "new0"
           | new1    => "new1"
           | meas    => "meas"
           | measQ   => "measQ"
           | discard => "discard"
           | assert0 => "assert0"
           | assert1 => "assert1"
         end
       in aux
  |}.

Eval compute in (show (U (trans (bit_ctrl (ctrl _H))))).
Eval compute in (show (measQ)).

Inductive GeneralGate :=
| general_U : forall (u : GeneralUnitary), GeneralGate
| general_BNOT    : GeneralGate
| general_init0   : GeneralGate
| general_init1   : GeneralGate
| general_new0    : GeneralGate
| general_new1    : GeneralGate
| general_meas    : GeneralGate
| general_measQ   : GeneralGate
| general_discard : GeneralGate
| general_assert0 : GeneralGate
| general_assert1 : GeneralGate.

Instance showGeneralGate : Show (GeneralGate) :=
  {| show := 
       let fix aux t := 
           match t with
           | general_U u => "general_U (" ++ (show u) ++ ")"
           | general_BNOT    => "general_BNOT"
           | general_init0   => "general_init0"
           | general_init1   => "general_init1"
           | general_new0    => "general_new0"
           | general_new1    => "general_new1"
           | general_meas    => "general_meas"
           | general_measQ   => "general_measQ"
           | general_discard => "general_discard"
           | general_assert0 => "general_assert0"
           | general_assert1 => "general_assert1"
           end
       in aux
  |}.

Eval compute in
    (show (general_U (general_bit_ctrl (general_ctrl general_H)))).
Eval compute in (show (general_measQ)).

Definition genGeneralGate (tn : nat) : G (GeneralGate) :=
  oneOf [ liftGen general_U (genGeneralUnitary tn) ;
            returnGen general_BNOT ;
            returnGen general_init0 ;
            returnGen general_init1 ;
            returnGen general_new0 ;
            returnGen general_new1 ;
            returnGen general_meas ;
            returnGen general_measQ ;
            returnGen general_discard ;
            returnGen general_assert0 ;
            returnGen general_assert1
        ].

Sample (genGeneralGate 3).

Fixpoint GeneralGate_to_WType (gg : GeneralGate) : (WType * WType) :=
  match gg with
  | general_U u => let w := (GeneralUnitary_to_WType u) in (w, w)
  | general_BNOT    => (Bit, Bit)
  | general_init0   => (One, Qubit)
  | general_init1   => (One, Qubit)
  | general_new0    => (One, Bit)
  | general_new1    => (One, Bit)
  | general_meas    => (Qubit, Bit)
  | general_measQ   => (Qubit, Qubit)
  | general_discard => (Bit, One)
  | general_assert0 => (Qubit, One)
  | general_assert1 => (Qubit, One)
  end.
Check GeneralGate_to_WType.
Definition GeneralGate_to_Gate (gg : GeneralGate) :
  Gate (fst (GeneralGate_to_WType gg)) (snd (GeneralGate_to_WType gg)) :=
  match gg with
  | general_U u => U (GeneralUnitary_to_Unitary u)
  | general_BNOT    => BNOT
  | general_init0   => init0
  | general_init1   => init1
  | general_new0    => new0
  | general_new1    => new1
  | general_meas    => meas
  | general_measQ   => measQ
  | general_discard => discard
  | general_assert0 => assert0
  | general_assert1 => assert1
  end.
Check GeneralGate_to_Gate.

(* Ctx 
Definition Ctx := list (option WType).
*)
Instance showCtx : Show (Ctx) :=
  {| show := 
       let fix aux t :=
           match t with
           | [] => ""
           | [e] => (show e)
           | h :: t' => (show h) ++ ", " ++ (aux t')
           end
       in (fun t => "Ctx (" ++ (aux t) ++ ")")
  |}.
Check ([Some Qubit; Some Bit; None]).
Definition ctx_example : Ctx := [Some Qubit; Some Bit; None].
Check ctx_example.
Eval compute in (show ctx_example).

(* Type for the selection of type [A] in Ctx *)
Inductive ChoiceInCtx (A : Type) :=
| choice_in_Ctx : A -> Ctx -> ChoiceInCtx A.
Check choice_in_Ctx.
Check choice_in_Ctx nat.
Instance showChoiceInCtx {A} `{Show A} : Show (ChoiceInCtx A) :=
  {| show := 
       let fix aux t :=
           match t with
           | choice_in_Ctx a ctx =>
             "choice_in_Ctx (" ++ (show a) ++ ", " ++ (show ctx) ++ ")"
           end
       in aux
  |}.
Eval simpl in (show (choice_in_Ctx nat O [Some Qubit])).

(* OCtx 
Inductive OCtx := 
| Invalid : OCtx 
| Valid : Ctx -> OCtx.
*)
Instance showOCtx : Show (OCtx) :=
  {| show := 
       let fix aux t :=
           match t with
           | Invalid => "Invalid"
           | Valid ctx => "Valid " ++ (show ctx)
           end
       in (fun t => "OCtx (" ++ (aux t) ++ ")")
  |}.
Check (Valid [Some Qubit; Some Bit; None]).
Definition octx_example : OCtx := Valid [Some Qubit; Some Bit; None].
Check octx_example.
Eval compute in (show octx_example).

(* Type for the selection of type [A] in OCtx *)
Inductive ChoiceInOCtx (A : Type) :=
| choice_in_OCtx (a : A) (octx : OCtx) : ChoiceInOCtx A.

Instance showChoiceInOCtx {A} `{Show A} : Show (ChoiceInOCtx A) :=
  {| show := 
       let fix aux t :=
         match t with
           | choice_in_OCtx a ctx => "choice_in_OCtx (" ++ show a ++ ") (" ++ show ctx ++ ")"
         end
       in aux
  |}.
Eval compute in (show (choice_in_OCtx nat O (Valid [Some Qubit]))).

Close Scope circ_scope.
