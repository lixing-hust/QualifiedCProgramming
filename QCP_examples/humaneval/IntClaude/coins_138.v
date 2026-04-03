Load "../../../../Coins/spec/human/input/138".

(* Adapt bool result to Z: r <> 0 means true *)
Definition problem_138_spec_z (n r : Z) : Prop :=
  r <> 0 <-> exists e1 e2 e3 e4 : Z,
    is_positive_even e1 /\ is_positive_even e2 /\ is_positive_even e3 /\ is_positive_even e4 /\
    n = e1 + e2 + e3 + e4.
