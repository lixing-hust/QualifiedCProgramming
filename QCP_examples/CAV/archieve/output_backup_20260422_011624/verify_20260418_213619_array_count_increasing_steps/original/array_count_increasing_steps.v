Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_count_increasing_steps_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: nil => 0
  | x :: y :: xs =>
      (if Z_lt_dec x y then 1 else 0) +
      array_count_increasing_steps_spec (y :: xs)
  end.
