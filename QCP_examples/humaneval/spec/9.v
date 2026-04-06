(* """ From a given list of integers, generate a list of rolling maximum element found until given moment
in the sequence.
>>> rolling_max([1, 2, 3, 2, 3, 4, 2])
[1, 2, 3, 3, 3, 4, 4]
""" *)

(* Spec(input, output) :=

length(output) == length(input) ∧

∀i. 0 ≤ i < length(output) ∧
        (∀j. 0 ≤ j ≤ i → input[j] ≤ output[i]) ∧
        (∃j. 0 ≤ j ≤ i ∧ input[j] = output[i]) *)

Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

