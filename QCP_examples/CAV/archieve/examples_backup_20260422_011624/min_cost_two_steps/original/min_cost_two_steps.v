Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint min_cost_two_steps_acc (prev2 prev1 : Z) (l : list Z) : Z :=
  match l with
  | nil => prev1
  | x :: xs => min_cost_two_steps_acc prev1 (Z.min prev1 prev2 + x) xs
  end.

Definition min_cost_two_steps_z (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: nil => x
  | x :: y :: xs => min_cost_two_steps_acc x (x + y) xs
  end.
