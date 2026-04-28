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
From SimpleC.EE Require Import C_70_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_70.
Local Open Scope sac.

Lemma proof_of_strange_sort_list_entail_wit_1 : strange_sort_list_entail_wit_1.
Proof.
  pre_process.
  sep_apply IntArray.undef_full_to_undef_seg.
  change (copy_prefix 0 input_l) with (@nil Z).
  rewrite IntArray.seg_empty.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
Qed.

Lemma proof_of_strange_sort_list_entail_wit_2 : strange_sort_list_entail_wit_2.
Proof.
  pre_process.
  sep_apply (IntArray.seg_single sorted i (Znth i input_l 0)).
  sep_apply (IntArray.seg_merge_to_seg sorted 0 i (i + 1)
               (copy_prefix i input_l) (Znth i input_l 0 :: nil)).
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - rewrite copy_prefix_snoc by lia. reflexivity.
  - rewrite copy_prefix_Zlength by lia. lia.
  - lia.
Qed.

Lemma proof_of_strange_sort_list_entail_wit_3 : strange_sort_list_entail_wit_3.
Proof.
  pre_process.
  replace i with lst_size_pre in * by lia.
  assert (Hcopy : copy_prefix lst_size_pre input_l = input_l).
  { rewrite H5. apply copy_prefix_full. }
  rewrite Hcopy.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
Qed.

Lemma proof_of_strange_sort_list_entail_wit_4 : strange_sort_list_entail_wit_4.
Proof.
  pre_process.
  Exists sorted_full_l_2 sorted_l_2.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - intros Hlt. replace (0 ÷ 2) with 0 by reflexivity. split; lia.
  - intros Hlt. replace (0 ÷ 2) with 0 by reflexivity. split; lia.
Qed.

Lemma proof_of_strange_sort_list_entail_wit_5_1 : strange_sort_list_entail_wit_5_1.
Proof.
  pre_process.
  Exists sorted_full_l_2 sorted_l_2.
  sep_apply (IntArray.seg_single data i (Znth (i ÷ 2) sorted_full_l_2 0)).
  sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)
               (strange_output_prefix lst_size_pre i sorted_l_2)
               (Znth (i ÷ 2) sorted_full_l_2 0 :: nil)).
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - rewrite strange_output_prefix_snoc by lia.
    rewrite strange_index_even by assumption.
    rewrite (sorted_full_Znth sorted_full_l_2 sorted_l_2 lst_size_pre (i ÷ 2));
      [simpl_entail | lia | assumption].
  - rewrite strange_output_prefix_Zlength by lia. lia.
  - apply reverse_quot2_bounds; lia.
  - apply quot2_bounds; lia.
  - lia.
Qed.

Lemma proof_of_strange_sort_list_entail_wit_5_2 : strange_sort_list_entail_wit_5_2.
Proof.
  pre_process.
  Exists sorted_full_l_2 sorted_l_2.
  sep_apply (IntArray.seg_single data i (Znth ((lst_size_pre - 1) - (i ÷ 2)) sorted_full_l_2 0)).
  sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)
               (strange_output_prefix lst_size_pre i sorted_l_2)
               (Znth ((lst_size_pre - 1) - (i ÷ 2)) sorted_full_l_2 0 :: nil)).
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - rewrite strange_output_prefix_snoc by lia.
    rewrite strange_index_odd by assumption.
    rewrite (sorted_full_Znth sorted_full_l_2 sorted_l_2 lst_size_pre ((lst_size_pre - 1) - (i ÷ 2)));
      [simpl_entail | lia | assumption].
  - rewrite strange_output_prefix_Zlength by lia. lia.
  - apply reverse_quot2_bounds; lia.
  - apply quot2_bounds; lia.
  - lia.
Qed.

Lemma proof_of_strange_sort_list_return_wit_1 : strange_sort_list_return_wit_1.
Proof.
  pre_process.
  Exists (strange_output_prefix lst_size_pre i sorted_l) data_2.
  replace i with lst_size_pre in * by lia.
  sep_apply (IntArray.seg_to_full data_2 0 lst_size_pre (strange_output_prefix lst_size_pre lst_size_pre sorted_l)).
  replace (data_2 + 0 * sizeof(INT)) with data_2 by lia.
  replace (lst_size_pre - 0) with lst_size_pre by lia.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
Qed.
