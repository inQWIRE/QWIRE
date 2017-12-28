Require Import Reals.
Require Import String.
Require Import Ascii.

(* auxiliary recursive function for successor of string representing nat *)
Fixpoint string_rS (s : string) : prod nat string :=
  match s with
  | EmptyString => (1, EmptyString)
  | String a ns => 
    match (nat_of_ascii a) with
    | 57 => let (c, ns_S) := (string_rS ns) in
                           match c with
                           | 1 => pair 1 (String (ascii_of_nat 48) ns_S)
                           | _ => pair 0 (String (ascii_of_nat ((nat_of_ascii a) + c)) ns_S)
                           end
    | _ => let (c, ns_S) := (string_rS ns) in
           pair 0 (String (ascii_of_nat ((nat_of_ascii a) + c)) ns_S)
    end
  end.
Example string_rS_test := string_rS EmptyString.
Eval compute in string_rS_test.
Example string_rS_test2 := string_rS (String (ascii_of_nat 57) EmptyString).
Eval compute in string_rS_test2.
(* successor function for string representing nat *)
Fixpoint string_S (s : string) : string :=
  let ns_S := (string_rS s) in match ns_S with
                                | (1, s') => String (ascii_of_nat 49) s'
                                | (_, s') => s'
                                end.
Example string_S_test := string_S EmptyString.
Eval compute in string_S_test.
Example string_S_test2 := string_S (String (ascii_of_nat 57) EmptyString).
Eval compute in string_S_test2.
(* conversion function from nat to string *)
Fixpoint string_of_nat (n : nat) : string :=
  match n with
  | 0 => String (ascii_of_nat 48) EmptyString
  | S n' => string_S (string_of_nat n')
  end.
Example string_of_3 := string_of_nat 3.
Eval compute in string_of_3.
Example string_of_9 := string_of_nat 9.
Eval compute in string_of_9.
Example string_of_10 := string_of_nat 10.
Eval compute in string_of_10.
Example string_of_11 := string_of_nat 11.
Eval compute in string_of_11.

(* Integers to strings *)
Definition natToDigit (n : nat) : ascii :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.
Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.
Definition writeNat (n : nat) : string :=
  writeNatAux n n "".
Eval compute in writeNat 11.
