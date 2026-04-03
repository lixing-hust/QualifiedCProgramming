Load "../../../../Coins/spec/human/input/41".
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition problem_41_spec_z (n r : Z) : Prop := problem_41_spec (Z.to_nat n) (Z.to_nat r).
