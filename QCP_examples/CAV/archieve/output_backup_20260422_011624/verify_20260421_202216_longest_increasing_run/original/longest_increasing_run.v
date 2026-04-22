Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint longest_increasing_run_acc
  (cur best prev : Z) (l : list Z) : Z :=
  match l with
  | nil => best
  | x :: xs =>
      let cur' := if Z_lt_dec prev x then cur + 1 else 1 in
      longest_increasing_run_acc cur' (Z.max best cur') x xs
  end.

Definition longest_increasing_run_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => longest_increasing_run_acc 1 1 x xs
  end.
