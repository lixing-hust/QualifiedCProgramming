From SimpleC.SL Require Import SeparationLogic.
From Flocq.Core Require Import Raux.

Load "../spec/45".

Lemma fp32_eq_refl_finite_45 :
  forall x,
    fp32_isFinite x ->
    fp32_eq x x.
Proof.
  intros x Hfinite.
  unfold fp32_eq, fp32_compare.
  rewrite Binary.Bcompare_correct; try exact Hfinite.
  rewrite Rcompare_Eq; reflexivity.
Qed.

Lemma triangle_area_contract_is_problem_45_spec :
  forall side high output,
    fp32_eq output (triangle_area_fp32 side high) ->
    problem_45_spec side high output.
Proof.
  intros side high output H.
  exact H.
Qed.
