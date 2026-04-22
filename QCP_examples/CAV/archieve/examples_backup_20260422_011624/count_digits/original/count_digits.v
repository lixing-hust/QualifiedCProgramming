Require Import ZArith.

Open Scope Z_scope.

Fixpoint count_digits_fuel (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S k =>
      if Z.leb n 0
      then 0
      else 1 + count_digits_fuel (Z.quot n 10) k
  end.

Definition count_digits_z (n : Z) : Z :=
  if Z.eqb n 0
  then 1
  else count_digits_fuel n (Z.to_nat n).
