Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_count_increasing_steps_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      match xs with
      | nil => 0
      | y :: xs' =>
          (if Z_lt_dec x y then 1 else 0) +
          array_count_increasing_steps_spec xs
      end
  end.
