Require Import ZArith.
Require Import reverse_digits.

Open Scope Z_scope.

Definition reverse_digits_acc_z (n acc : Z) : Z :=
  reverse_digits_fuel n acc (Z.to_nat n).
