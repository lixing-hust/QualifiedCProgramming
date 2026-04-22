Require Import ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

Open Scope Z_scope.

Fixpoint sorted_z (l : list Z) : Prop :=
  match l with
  | nil => True
  | x :: xs =>
      match xs with
      | nil => True
      | y :: ys => x <= y /\ sorted_z xs
      end
  end.
