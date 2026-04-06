Require Import Coq.ZArith.ZArith.
Load "../spec/60".

Definition problem_60_pre_z (n : Z) : Prop := problem_60_pre (Z.to_nat n).
Definition problem_60_spec_z (n r : Z) : Prop := problem_60_spec (Z.to_nat n) (Z.to_nat r).
