Load "../spec/159".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_159_pre_z (number need remaining : Z) : Prop :=
  problem_159_pre number need remaining.

Definition problem_159_spec_z (number need remaining : Z) (result : list Z) : Prop :=
  problem_159_spec number need remaining result.

Lemma problem_159_spec_need_gt_remaining : forall number need remaining,
  problem_159_pre_z number need remaining ->
  need > remaining ->
  problem_159_spec_z number need remaining [number + remaining; 0].
Proof.
  intros.
  unfold problem_159_spec_z, problem_159_spec.
  right.
  split; [lia | reflexivity].
Qed.

Lemma problem_159_spec_need_le_remaining : forall number need remaining,
  problem_159_pre_z number need remaining ->
  need <= remaining ->
  problem_159_spec_z number need remaining [number + need; remaining - need].
Proof.
  intros.
  unfold problem_159_spec_z, problem_159_spec.
  left.
  split; [lia | reflexivity].
Qed.
