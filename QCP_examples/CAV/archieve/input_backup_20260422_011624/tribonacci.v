Require Import ZArith.

Open Scope Z_scope.

Fixpoint tribonacci_triple (n : nat) : Z * Z * Z :=
  match n with
  | O => (0, 1, 1)
  | S k =>
      let p := tribonacci_triple k in
      match p with
      | (a, b, c) => (b, c, a + b + c)
      end
  end.

Definition tribonacci_nat (n : nat) : Z :=
  match tribonacci_triple n with
  | (a, _, _) => a
  end.

Definition tribonacci_z (n : Z) : Z :=
  tribonacci_nat (Z.to_nat n).
