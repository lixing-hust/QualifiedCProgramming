Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint min_list_nonempty (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: nil => x
  | x :: xs => Z.min x (min_list_nonempty xs)
  end.
