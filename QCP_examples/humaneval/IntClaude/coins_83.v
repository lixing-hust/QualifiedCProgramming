Load "../spec/83".
Require Import Coq.ZArith.ZArith.

Definition problem_83_pre_z (n : Z) : Prop := problem_83_pre (Z.to_nat n).
Definition problem_83_spec_z (n r : Z) : Prop := problem_83_spec (Z.to_nat n) (Z.to_nat r).
