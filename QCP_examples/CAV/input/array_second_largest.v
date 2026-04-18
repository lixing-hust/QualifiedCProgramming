Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint second_largest_acc (max1 max2 : Z) (l : list Z) : Z :=
  match l with
  | nil => max2
  | x :: xs =>
      if Z_gt_dec x max1 then
        second_largest_acc x max1 xs
      else if Z_gt_dec x max2 then
        second_largest_acc max1 x xs
      else
        second_largest_acc max1 max2 xs
  end.

Definition second_largest_list (l : list Z) : Z :=
  match l with
  | x1 :: x2 :: xs =>
      if Z_gt_dec x2 x1 then
        second_largest_acc x2 x1 xs
      else
        second_largest_acc x1 x2 xs
  | _ => 0
  end.
