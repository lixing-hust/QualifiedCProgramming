Load "../spec/139".

Definition problem_139_pre_z (n : Z) : Prop := problem_139_pre (Z.to_nat n).
Definition problem_139_spec_z (n r : Z) : Prop := problem_139_spec (Z.to_nat n) (Z.to_nat r).
