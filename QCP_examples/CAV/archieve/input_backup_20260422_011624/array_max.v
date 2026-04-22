Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint max_list_nonempty (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: nil => x
  | x :: xs => Z.max x (max_list_nonempty xs)
  end.
