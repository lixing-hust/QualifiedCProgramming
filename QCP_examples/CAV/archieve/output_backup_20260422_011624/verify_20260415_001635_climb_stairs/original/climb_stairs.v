Require Import ZArith.

Open Scope Z_scope.

Fixpoint climb_stairs_nat (n : nat) : Z :=
  match n with
  | O => 1
  | S n' =>
      match n' with
      | O => 1
      | S k => climb_stairs_nat n' + climb_stairs_nat k
      end
  end.

Definition climb_stairs_z (n : Z) : Z :=
  climb_stairs_nat (Z.to_nat n).
