Load "../spec/31".
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Adapt nat input + bool output to Z: r <> 0 means true *)
Definition problem_31_spec_z (n r : Z) : Prop :=
  r <> 0 <-> IsPrime (Z.to_nat n).
