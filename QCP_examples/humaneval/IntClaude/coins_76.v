Load "../../../../Coins/spec/human/input/76".

(* Adapt bool result to Z: r <> 0 means true *)
Definition is_simple_power_spec (x n r : Z) : Prop :=
  r <> 0 <-> (exists k : nat, x = n ^ Z.of_nat k).
