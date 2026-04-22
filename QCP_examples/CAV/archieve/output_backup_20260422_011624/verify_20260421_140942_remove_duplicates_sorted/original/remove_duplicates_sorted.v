Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint remove_duplicates_sorted_from (prev : Z) (l : list Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs =>
      if Z.eq_dec x prev then
        remove_duplicates_sorted_from prev xs
      else
        x :: remove_duplicates_sorted_from x xs
  end.

Definition remove_duplicates_sorted_spec (l : list Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs => x :: remove_duplicates_sorted_from x xs
  end.
