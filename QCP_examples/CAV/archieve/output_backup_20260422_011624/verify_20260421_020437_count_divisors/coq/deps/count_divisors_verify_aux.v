Require Import ZArith.
Require Import count_divisors.

Open Scope Z_scope.

Definition count_divisors_prefix (n limit : Z) : Z :=
  count_divisors_upto n (Z.to_nat limit).
