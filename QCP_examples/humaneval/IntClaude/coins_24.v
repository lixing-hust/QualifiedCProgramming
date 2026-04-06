Require Import Coq.ZArith.ZArith.
Load "../spec/24".

Definition problem_24_pre_z (n : Z) : Prop := problem_24_pre (Z.to_nat n).
Definition problem_24_spec_z (n r : Z) : Prop := problem_24_spec (Z.to_nat n) (Z.to_nat r).
