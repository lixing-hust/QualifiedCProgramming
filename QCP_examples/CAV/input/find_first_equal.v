Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint find_first_equal_spec (l : list Z) (k : Z) : Z :=
  match l with
  | nil => -1
  | x :: xs =>
      if Z.eq_dec x k then 0
      else
        let r := find_first_equal_spec xs k in
        if Z.eq_dec r (-1) then -1 else r + 1
  end.
