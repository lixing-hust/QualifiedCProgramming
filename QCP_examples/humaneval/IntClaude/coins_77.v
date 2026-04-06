Load "../spec/77".

(* Adapt bool result to Z: r <> 0 means true *)
Definition problem_77_spec_z (a r : Z) : Prop :=
  r <> 0 <-> (exists x : Z, a = x * x * x).
