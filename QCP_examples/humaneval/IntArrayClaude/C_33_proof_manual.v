Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_33_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_33.
Local Open Scope sac.

Lemma proof_of_sort_third_entail_wit_1 : sort_third_entail_wit_1.
Proof.
  pre_process.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  - pose proof (third_count_nonneg_le l_size_pre ltac:(lia)) as [_ Hle].
    unfold third_count in Hle.
    exact Hle.
  - pose proof (third_count_nonneg_le l_size_pre ltac:(lia)) as [Hge _].
    unfold third_count in Hge.
    exact Hge.
  - pose proof (third_count_nonneg_le l_size_pre ltac:(lia)) as [Hge _].
    unfold third_count in Hge.
    exact Hge.
Qed. 

Lemma proof_of_sort_third_entail_wit_2 : sort_third_entail_wit_2.
Proof.
  pre_process.
  rewrite third_values_prefix_snoc by lia.
  replace (i * 3) with (3 * i) in * by lia.
  sep_apply (IntArray.seg_single third i (Znth (3 * i) input_l 0)).
  sep_apply (IntArray.seg_merge_to_seg third 0 i (i + 1)); [ | lia].
  entailer!.
  - rewrite Zlength_app.
    rewrite Zlength_cons, Zlength_nil.
    rewrite <- H13.
    lia.
  - subst third_size.
    apply third_count_after_hit; lia.
Qed. 

Lemma proof_of_sort_third_entail_wit_3 : sort_third_entail_wit_3.
Proof.
  pre_process.
  assert (Hi : i = third_size).
  {
    subst third_size.
    apply third_count_exit_index; lia.
  }
  subst i.
  entailer!.
Qed. 

Lemma proof_of_sort_third_entail_wit_5 : sort_third_entail_wit_5.
Proof.
  pre_process.
  Exists sorted_full_l_2 sorted_third_l_2.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
Qed. 

Lemma proof_of_sort_third_entail_wit_6_1 : sort_third_entail_wit_6_1.
Proof.
  pre_process.
  Exists sorted_full_l_2 sorted_third_l_2.
  assert (Hjquot : j = i ÷ 3).
  {
    subst j.
    apply third_count_mod0_quot; lia.
  }
  assert (Hjlt : j < third_size).
  {
    subst third_size j.
    rewrite third_count_mod0_quot by lia.
    assert (Hhit : (i ÷ 3) * 3 < l_size_pre).
    {
      pose proof (Z.quot_rem i 3 ltac:(lia)).
      lia.
    }
    pose proof (third_count_after_hit l_size_pre (i ÷ 3) ltac:(lia) ltac:(lia) Hhit).
    lia.
  }
  assert (Hz : Znth j sorted_full_l_2 0 = Znth j sorted_third_l_2 0).
  {
    rewrite <- H10.
    rewrite Znth_sublist by lia.
    replace (j + 0) with j by lia.
    reflexivity.
  }
  rewrite sort_third_output_prefix_snoc by lia.
  rewrite choose_sort_third_value_mod0 by lia.
  rewrite <- Hjquot.
  rewrite Hz.
  sep_apply (IntArray.seg_single data i (Znth j sorted_third_l_2 0)).
  sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)); [ | lia].
  entailer!.
  - subst j.
    rewrite third_count_step_mod0 by lia.
    lia.
Qed. 

Lemma proof_of_sort_third_entail_wit_6_2 : sort_third_entail_wit_6_2.
Proof.
  pre_process.
  Exists sorted_full_l_2 sorted_third_l_2.
  rewrite sort_third_output_prefix_snoc by lia.
  rewrite choose_sort_third_value_not_mod0 by lia.
  sep_apply (IntArray.seg_single data i (Znth i input_l 0)).
  sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)); [ | lia].
  entailer!.
  - subst j.
    rewrite third_count_step_not_mod0 by lia.
    reflexivity.
Qed. 

Lemma proof_of_sort_third_return_wit_1 : sort_third_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = l_size_pre) by lia.
  subst i.
  Exists (sort_third_output_prefix l_size_pre input_l sorted_third_l) l_size_pre data_2.
  sep_apply (IntArray.seg_to_full data_2 0 l_size_pre).
  replace (data_2 + 0 * sizeof (INT)) with data_2 by lia.
  replace (l_size_pre - 0) with l_size_pre by lia.
  entailer!.
  - rewrite H5.
    fold (sort_third_output input_l sorted_third_l).
    subst third_size.
    rewrite H5 in H7, H11.
    apply sort_third_output_problem_33_spec.
    + symmetry; assumption.
    + assumption.
    + assumption.
  - rewrite sort_third_output_prefix_Zlength by lia.
    lia.
Qed.
