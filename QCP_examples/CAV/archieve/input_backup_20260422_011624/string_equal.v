Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint string_equal_spec (la lb : list Z) : Z :=
  match la, lb with
  | nil, nil => 1
  | x :: xs, y :: ys =>
      if Z.eq_dec x y then string_equal_spec xs ys else 0
  | _, _ => 0
  end.
