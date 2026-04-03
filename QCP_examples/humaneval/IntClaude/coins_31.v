Load "../../../../Coins/spec/human/input/31".

(* Adapt nat input + bool output to Z: r <> 0 means true *)
Definition problem_31_spec_z (n r : Z) : Prop :=
  r <> 0 <-> IsPrime (Z.to_nat n).
