Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_contains_spec (l : list Z) (k : Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      if Z.eq_dec x k then 1 else array_contains_spec xs k
  end.
