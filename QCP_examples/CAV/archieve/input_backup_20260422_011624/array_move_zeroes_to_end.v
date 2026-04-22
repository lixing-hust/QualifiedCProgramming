Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint move_zeroes_nonzeroes (l : list Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs =>
      if Z.eq_dec x 0 then
        move_zeroes_nonzeroes xs
      else
        x :: move_zeroes_nonzeroes xs
  end.

Fixpoint move_zeroes_zeroes (l : list Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs =>
      if Z.eq_dec x 0 then
        0 :: move_zeroes_zeroes xs
      else
        move_zeroes_zeroes xs
  end.

Definition move_zeroes_to_end_spec (l : list Z) : list Z :=
  app (move_zeroes_nonzeroes l) (move_zeroes_zeroes l).
