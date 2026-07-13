Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_130_goal.
From SimpleC.EE Require Import C_130_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_130.
Local Open Scope sac.

Lemma proof_of_tri_safety_wit_12 : tri_safety_wit_12.
Proof.
  right; intros; entailer!;
    assert (0 <= i ÷ 2) by (apply Z.quot_pos; lia);
    assert (i ÷ 2 <= i) by (apply Z.quot_le_upper_bound; lia);
    lia.
Qed.

Lemma proof_of_tri_safety_wit_16 : tri_safety_wit_16.
Proof.
  right; intros.
  repeat rewrite tri_prefix_z_130_nth by lia.
  pose proof (tri_safe_z_130_odd_sum_range n0 i PreH7 ltac:(lia)) as Hrange.
  entailer!;
    replace (i - 1 - 0) with (i - 1) by lia;
    replace (i - 2 - 0) with (i - 2) by lia;
    try (rewrite Z.quot_div_nonneg by lia);
    lia.
Qed.

Lemma proof_of_tri_safety_wit_19 : tri_safety_wit_19.
Proof.
  right; intros.
  repeat rewrite tri_prefix_z_130_nth by lia.
  pose proof (tri_safe_z_130_step_value n0 (i - 1) PreH7 ltac:(lia)).
  pose proof (tri_safe_z_130_step_value n0 (i - 2) PreH7 ltac:(lia)).
  pose proof (tri_safe_z_130_odd_sum_range n0 i PreH7 ltac:(lia)).
  assert (0 <= (i + 1) / 2) by (apply Z.div_pos; lia).
  entailer!;
    replace (i - 1 - 0) with (i - 1) by lia;
    replace (i - 2 - 0) with (i - 2) by lia;
    lia.
Qed.

Lemma proof_of_tri_safety_wit_20 : tri_safety_wit_20.
Proof.
  right; intros.
  repeat rewrite tri_prefix_z_130_nth by lia.
  pose proof (tri_safe_z_130_step_value n0 (i - 1) PreH7 ltac:(lia)).
  pose proof (tri_safe_z_130_step_value n0 (i - 2) PreH7 ltac:(lia)).
  pose proof (tri_safe_z_130_odd_sum_range n0 i PreH7 ltac:(lia)).
  assert (0 <= (i + 1) / 2) by (apply Z.div_pos; lia).
  entailer!;
    replace (i - 1 - 0) with (i - 1) by lia;
    replace (i - 2 - 0) with (i - 2) by lia;
    lia.
Qed.

Lemma proof_of_tri_entail_wit_1 : tri_entail_wit_1.
Proof.
  right; intros.
  rewrite tri_prefix_z_130_1.
  unfold IntArray.seg, store_array, store_array_rec.
  simpl.
  entailer!.
Qed.

Lemma proof_of_tri_entail_wit_2 : tri_entail_wit_2.
Proof.
  left; intros; subst.
  assert (Hspec : problem_130_spec_z 0 (tri_prefix_z_130 (0 + 1))).
  { apply problem_130_spec_z_of_prefix; lia. }
  rewrite tri_prefix_z_130_1.
  unfold IntArray.full, IntArray.seg, IntArray.undef_seg.
  unfold store_array, store_array_rec, store_undef_array_rec.
  simpl.
  entailer!.
Qed.

Lemma proof_of_tri_entail_wit_3 : tri_entail_wit_3.
Proof.
  right; intros.
  rewrite tri_prefix_z_130_1, tri_prefix_z_130_2.
  entailer!.
Qed.

Lemma proof_of_tri_entail_wit_4_1 : tri_entail_wit_4_1.
Proof.
  right; intros.
  entailer!.
  rewrite tri_prefix_z_130_snoc by lia.
  rewrite tri_prefix_z_130_nth by lia.
  rewrite tri_prefix_z_130_nth by lia.
  replace (i - 1 - 0) with (i - 1) by lia.
  replace (i - 2 - 0) with (i - 2) by lia.
  rewrite (tri_safe_z_130_odd_step n0 i PreH7 ltac:(lia)).
  - rewrite Z.quot_div_nonneg by lia.
    reflexivity.
  - apply z_even_false_of_rem_nonzero_130; lia.
Qed.

Lemma proof_of_tri_entail_wit_4_2 : tri_entail_wit_4_2.
Proof.
  right; intros.
  entailer!.
  rewrite tri_prefix_z_130_snoc by lia.
  rewrite (tri_safe_z_130_even_step n0 i PreH7 ltac:(lia)).
  - rewrite Z.quot_div_nonneg by lia.
    reflexivity.
  - apply z_even_true_of_rem0_130; lia.
Qed.

Lemma proof_of_tri_entail_wit_6 : tri_entail_wit_6.
Proof.
  left; intros.
  assert (i = n0 + 1) by lia; subst i.
  subst size.
  assert (Hspec : problem_130_spec_z n0 (tri_prefix_z_130 (n0 + 1))).
  { apply problem_130_spec_z_of_prefix; lia. }
  unfold IntArray.full, IntArray.seg, IntArray.undef_seg.
  unfold store_array, store_array_rec, store_undef_array_rec.
  replace (Z.to_nat (n0 + 1 - (n0 + 1))) with O by lia.
  simpl.
  entailer!.
Qed.
