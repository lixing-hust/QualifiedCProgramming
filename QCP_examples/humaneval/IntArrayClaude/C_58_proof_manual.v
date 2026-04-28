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
From SimpleC.EE Require Import C_58_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_58.
Local Open Scope sac.

Lemma proof_of_contains_entail_wit_2 : contains_entail_wit_2.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  intros k Hk.
  destruct (Z.eq_dec k i).
  - subst. replace (i - 0) with i in H by lia. exact H.
  - apply H4. lia.
Qed.

Lemma proof_of_contains_return_wit_1 : contains_return_wit_1.
Proof.
  pre_process.
  Right.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  unfold list_not_contains.
  intros Hin.
  destruct (In_Znth_exists _ _ Hin) as [j [? Hj]].
  specialize (H3 j ltac:(lia)).
  congruence.
Qed.

Lemma proof_of_contains_return_wit_2 : contains_return_wit_2.
Proof.
  pre_process.
  Left.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  unfold list_contains.
  rewrite <- H.
  replace (i - 0) with i by lia.
  apply Znth_In_range.
  lia.
Qed.

Lemma proof_of_common_entail_wit_1 : common_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  sep_apply (IntArray.full_to_seg l2_pre l2_size_pre input_l2).
  rewrite IntArray.seg_empty.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  unfold common_first_loop, common_values.
  simpl.
  repeat split; lia.
Qed.

Lemma proof_of_common_entail_wit_4_1 : common_entail_wit_4_1.
Proof.
  pre_process.
  Exists (output_l_2 ++ (Znth i input_l1 0 :: nil)).
  sep_apply (IntArray.seg_single data output_size (Znth i input_l1 0)).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size (output_size + 1)
               output_l_2 (Znth i input_l1 0 :: nil)).
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - apply common_first_loop_add with (x := Znth i input_l1 0);
      try reflexivity; try assumption; lia.
  - rewrite Zlength_app. change (Zlength (Znth i input_l1 0 :: nil)) with 1. lia.
  - lia.
Qed.

Lemma proof_of_common_entail_wit_4_2 : common_entail_wit_4_2.
Proof.
  pre_process.
  Exists output_l_2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply common_first_loop_skip_not_l2 with (x := Znth i input_l1 0);
    try reflexivity; try assumption; lia.
Qed.

Lemma proof_of_common_entail_wit_4_3 : common_entail_wit_4_3.
Proof.
  pre_process.
  Exists output_l_2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply common_first_loop_skip_seen with (x := Znth i input_l1 0);
    try reflexivity; try assumption; lia.
Qed.

Lemma proof_of_common_return_wit_1 : common_return_wit_1.
Proof.
  pre_process.
  Exists sorted_full_l sorted_l output_size_2 data_2.
  sep_apply (IntArray.seg_to_full l2_pre 0 l2_size_pre input_l2).
  replace (l2_pre + 0 * sizeof(INT)) with l2_pre by lia.
  replace (l2_size_pre - 0) with l2_size_pre by lia.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply problem_58_spec_from_sort with (common_l := output_l_2); try assumption.
  replace (Zlength input_l1) with i by lia.
  assumption.
Qed.
