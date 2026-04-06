Load "../spec/150".

Definition problem_150_spec_z (n x y r : Z) : Prop :=
  problem_150_spec (Z.to_nat n) (Z.to_nat x) (Z.to_nat y) (Z.to_nat r).
