Load "../spec/75".

(* Adapt bool result to Z: r <> 0 means true *)
Definition problem_75_spec_z (a r : Z) : Prop :=
  r <> 0 <-> exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ a = p1 * p2 * p3.
