Load "../spec/39".

(* Z-typed wrappers for QCP (C int -> Z) *)
Definition problem_39_pre_z (n : Z) : Prop :=
  problem_39_pre (Z.to_nat n).

Definition prime_fib_spec (n r : Z) : Prop :=
  problem_39_spec (Z.to_nat n) (Z.to_nat r).
