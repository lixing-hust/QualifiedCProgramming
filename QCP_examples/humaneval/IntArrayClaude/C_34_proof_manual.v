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
From SimpleC.EE Require Import C_34_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_34.
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

Lemma proof_of_unique_entail_wit_1 : unique_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  unfold unique_first_loop, seen_values.
  simpl.
  repeat split; lia.
Qed.

Lemma proof_of_unique_entail_wit_2_1 : unique_entail_wit_2_1.
Proof.
  pre_process.
  Exists (output_l_2 ++ (Znth i input_l 0 :: nil)).
  sep_apply (IntArray.seg_single data output_size (Znth i input_l 0)).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size (output_size + 1)
               output_l_2 (Znth i input_l 0 :: nil)).
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - apply unique_first_loop_add with (x := Znth i input_l 0); try reflexivity; try assumption; lia.
  - rewrite Zlength_app. change (Zlength (Znth i input_l 0 :: nil)) with 1. lia.
  - lia.
Qed.

Lemma proof_of_unique_entail_wit_2_2 : unique_entail_wit_2_2.
Proof.
  pre_process.
  Exists output_l_2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply unique_first_loop_skip with (x := Znth i input_l 0); try reflexivity; try assumption; lia.
Qed.

Lemma proof_of_unique_return_wit_1 : unique_return_wit_1.
Proof.
  pre_process.
  Exists sorted_full_l sorted_l output_size_2 data_2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply problem_34_spec_from_sort with (unique_l := output_l_2); try assumption.
  replace (Zlength input_l) with i by lia.
  assumption.
Qed.
