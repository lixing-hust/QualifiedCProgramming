Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint house_robber_acc (prev2 prev1 : Z) (l : list Z) : Z :=
  match l with
  | nil => prev1
  | x :: xs =>
      let cur := Z.max (prev2 + x) prev1 in
      house_robber_acc prev1 cur xs
  end.

Definition house_robber_spec (l : list Z) : Z :=
  house_robber_acc 0 0 l.
