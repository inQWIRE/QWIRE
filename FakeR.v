(** Fake Reals **)
Require Import BinNums.

Local Open Scope Z_scope.

Inductive FakeR : Type :=
| fake_pi : FakeR
| fake_e : FakeR
| fake_mult : FakeR -> FakeR -> FakeR
| fake_div : FakeR -> FakeR -> FakeR
| fake_plus : FakeR -> FakeR -> FakeR
| fake_minus : FakeR -> FakeR -> FakeR
| fake_int : Z -> FakeR
| fake_pow : FakeR -> FakeR -> FakeR.

Infix "+" := fake_plus.
Infix "*" := fake_mult.
Notation "- x" := ((-1) * x).
Notation "/ x" := (fake_pow x (-1)).

(* FakeR to Real translation *)
Require Import Reals.

Fixpoint FakeRtoR (f : FakeR) : R :=
  match f with
  | fake_pi => PI
  | fake_e => exp 1
  | fake_mult f1 f2 => (FakeRtoR f1) * (FakeRtoR f2)
  | fake_div f1 f2 => (FakeRtoR f1) / (FakeRtoR f2)
  | fake_plus f1 f2 => (FakeRtoR f1) + (FakeRtoR f2)
  | fake_minus f1 f2 => (FakeRtoR f1) - (FakeRtoR f2)
  | fake_int z => IZR z
  | fake_pow f1 f2 => Rpower (FakeRtoR f1) (FakeRtoR f2)
  end.
