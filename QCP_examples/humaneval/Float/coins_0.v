Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
From SimpleC.SL Require Import SeparationLogic.

Load "../spec/0".

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_0_pre_z (threshold : fp32) : Prop :=
  problem_0_pre threshold.

Definition problem_0_spec_z
    (numbers : list fp32) (threshold : fp32) (output : Z) : Prop :=
  problem_0_spec numbers threshold (Z.eqb output 1).

Definition no_close_before_i_0
    (numbers : list fp32) (threshold : fp32) (i : Z) : Prop :=
  forall (a b : nat),
    (Z.of_nat a < i)%Z ->
    Nat.lt a b ->
    Nat.lt b (length numbers) ->
    ~ fp32_close_0
        (nth a numbers fp32_zero)
        (nth b numbers fp32_zero)
        threshold.

Definition no_close_before_j_0
    (numbers : list fp32) (threshold : fp32) (i j : Z) : Prop :=
  forall (b : nat),
    (i < Z.of_nat b < j)%Z ->
    Nat.lt b (length numbers) ->
    ~ fp32_close_0
        (nth (Z.to_nat i) numbers fp32_zero)
        (nth b numbers fp32_zero)
        threshold.
