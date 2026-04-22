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
From SimpleC.EE Require Import C_26_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_26.
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

Lemma proof_of_remove_duplicates_entail_wit_1 : remove_duplicates_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z) (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  rewrite IntArray.seg_empty.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  unfold remove_duplicates_first_loop, seen_values, duplicate_values.
  simpl.
  repeat split; lia.
Qed.

Lemma proof_of_remove_duplicates_entail_wit_6_1 : remove_duplicates_entail_wit_6_1.
Proof.
  pre_process.
  Exists (has2_l_2 ++ (Znth i input_l 0 :: nil)) has1_l_2.
  sep_apply (IntArray.seg_single has2 has2_size (Znth i input_l 0)).
  sep_apply (IntArray.seg_merge_to_seg has2 0 has2_size (has2_size + 1)
               has2_l_2 (Znth i input_l 0 :: nil)).
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - apply first_loop_add_duplicate with (x := Znth i input_l 0); try reflexivity; try assumption; lia.
  - rewrite Zlength_app. change (Zlength (Znth i input_l 0 :: nil)) with 1. rewrite <- H20. lia.
  - lia.
Qed.

Lemma proof_of_remove_duplicates_entail_wit_6_2 : remove_duplicates_entail_wit_6_2.
Proof.
  pre_process.
  Exists has2_l_2 (has1_l_2 ++ (Znth i input_l 0 :: nil)).
  sep_apply (IntArray.seg_single has1 has1_size (Znth i input_l 0)).
  sep_apply (IntArray.seg_merge_to_seg has1 0 has1_size (has1_size + 1)
               has1_l_2 (Znth i input_l 0 :: nil)).
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - apply first_loop_add_seen with (x := Znth i input_l 0); try reflexivity; try assumption; lia.
  - rewrite Zlength_app. change (Zlength (Znth i input_l 0 :: nil)) with 1. rewrite <- H19. lia.
  - lia.
Qed.

Lemma proof_of_remove_duplicates_entail_wit_6_3 : remove_duplicates_entail_wit_6_3.
Proof.
  pre_process.
  Exists has2_l_2 has1_l_2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply first_loop_skip_duplicate with (x := Znth i input_l 0); try reflexivity; try assumption; lia.
Qed.

Lemma proof_of_remove_duplicates_entail_wit_7 : remove_duplicates_entail_wit_7.
Proof.
  pre_process.
  Exists (@nil Z) has2_l_2 has1_l_2.
  rewrite IntArray.seg_empty.
  sep_apply IntArray.undef_full_to_undef_seg.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - unfold remove_duplicates_second_loop; simpl.
    split; [lia | reflexivity].
  - replace i with numbers_size_pre in H15 by lia.
    exact H15.
Qed.

Lemma proof_of_remove_duplicates_entail_wit_8_1 : remove_duplicates_entail_wit_8_1.
Proof.
  pre_process.
  Exists (output_l_2 ++ (Znth i input_l 0 :: nil)) has2_l_2 has1_l_2.
  sep_apply (IntArray.seg_single data output_size (Znth i input_l 0)).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size (output_size + 1)
               output_l_2 (Znth i input_l 0 :: nil)).
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - apply second_loop_add_output with (x := Znth i input_l 0); try reflexivity; try assumption; lia.
  - rewrite Zlength_app. change (Zlength (Znth i input_l 0 :: nil)) with 1.
    rewrite <- H21. lia.
  - lia.
Qed.

Lemma proof_of_remove_duplicates_entail_wit_8_2 : remove_duplicates_entail_wit_8_2.
Proof.
  pre_process.
  Exists output_l_2 has2_l_2 has1_l_2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply second_loop_skip_output with (x := Znth i input_l 0); try reflexivity; try assumption; lia.
Qed.

Lemma proof_of_remove_duplicates_return_wit_1 : remove_duplicates_return_wit_1.
Proof.
  pre_process.
  Exists data_2 output_l_2 output_size_2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply problem_26_spec_from_loops with (has1 := has1_l) (has2 := has2_l).
  - replace (Zlength input_l) with numbers_size_pre by lia.
    exact H18.
  - replace (Zlength input_l) with i by lia.
    exact H19.
Qed. 
