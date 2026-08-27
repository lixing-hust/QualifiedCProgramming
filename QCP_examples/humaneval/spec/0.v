(* Check if in given list of numbers, are any two numbers closer to each other than
given threshold.
>>> has_close_elements([1.0, 2.0, 3.0], 0.5)
False
>>> has_close_elements([1.0, 2.8, 3.0, 4.0, 5.0, 2.0], 0.3)
True
*)
Require Import List.
From SimpleC.SL Require Import SeparationLogic.
Import ListNotations.

Definition fp32_close_0 (x y threshold : fp32) : Prop :=
  let difference := fp32_sub x y in
  (fp32_lt difference fp32_zero /\
   fp32_lt (fp32_neg difference) threshold) \/
  (~ fp32_lt difference fp32_zero /\
   fp32_lt difference threshold).

Definition problem_0_pre (threshold : fp32) : Prop :=
  fp32_ge threshold fp32_zero.

Definition problem_0_spec
    (numbers : list fp32) (threshold : fp32) (output : bool) : Prop :=
  (exists (i j : nat),
    Nat.lt i j /\
    Nat.lt j (length numbers) /\
    fp32_close_0
      (nth i numbers fp32_zero)
      (nth j numbers fp32_zero)
      threshold) <->
    output = true.
