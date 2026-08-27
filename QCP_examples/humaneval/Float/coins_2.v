Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
From SimpleC.SL Require Import SeparationLogic.

Load "../spec/2".

Local Open Scope R_scope.

Definition problem_2_pre_fp32 (x : fp32) : Prop :=
  fp32_isFinite x /\ problem_2_pre (fp32_to_R_total x).

Definition problem_2_spec_fp32 (x frac : fp32) : Prop :=
  fp32_isFinite frac /\
  problem_2_spec (fp32_to_R_total x) (fp32_to_R_total frac).

Definition problem_2_pre_bits (input_bits : Z) : Prop :=
  problem_2_pre_fp32 (fp32_of_bits input_bits).

Definition problem_2_spec_bits (input_bits result_bits : Z) : Prop :=
  problem_2_spec_fp32
    (fp32_of_bits input_bits) (fp32_of_bits result_bits).

Definition floorf_rel_bits_2 (input_bits floor_bits : Z) : Prop :=
  let x := fp32_of_bits input_bits in
  let integer_part := fp32_of_bits floor_bits in
  fp32_isFinite integer_part /\
  fp32_to_R_total integer_part =
    IZR (floor (fp32_to_R_total x)) /\
  fp32_isFinite (fp32_sub x integer_part) /\
  fp32_to_R_total (fp32_sub x integer_part) =
    fp32_to_R_total x - fp32_to_R_total integer_part.

Definition floorf_fraction_bits_2 (input_bits fraction_bits : Z) : Prop :=
  let x := fp32_of_bits input_bits in
  let frac := fp32_of_bits fraction_bits in
  fp32_isFinite frac /\
  fp32_to_R_total frac =
    fp32_to_R_total x - IZR (floor (fp32_to_R_total x)) /\
  0 <= fp32_to_R_total frac < 1.

Lemma floorf_fraction_bits_2_problem_2 :
  forall input_bits fraction_bits,
    floorf_fraction_bits_2 input_bits fraction_bits ->
    problem_2_spec_bits input_bits fraction_bits.
Proof.
  intros input_bits fraction_bits H.
  unfold floorf_fraction_bits_2 in H.
  unfold problem_2_spec_bits, problem_2_spec_fp32, problem_2_spec.
  exact H.
Qed.
