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
From SimpleC.EE Require Import C_146_goal.
From SimpleC.EE Require Import C_146_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_146.
Local Open Scope sac.

Lemma proof_of_specialFilter_entail_wit_1_split_goal_1 : specialFilter_entail_wit_1_split_goal_1.
Proof.
  unfold specialFilter_entail_wit_1_split_goal_1; intros.
  pre_process; entailer!.
  apply special_filter_prefix_init_146.
Qed.

Lemma proof_of_specialFilter_entail_wit_1 : specialFilter_entail_wit_1.
Proof.
  unfold specialFilter_entail_wit_1; right; intros.
  pre_process; entailer!.
  apply special_filter_prefix_init_146.
Qed.

Lemma proof_of_specialFilter_entail_wit_2_split_goal_1 : specialFilter_entail_wit_2_split_goal_1.
Proof.
  unfold specialFilter_entail_wit_2_split_goal_1; intros.
  pre_process; entailer!.
  pose proof (special_filter_safe_Znth_range_146 input_l i PreH6 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_specialFilter_entail_wit_2_split_goal_2 : specialFilter_entail_wit_2_split_goal_2.
Proof.
  unfold specialFilter_entail_wit_2_split_goal_2; intros.
  pre_process; entailer!.
  pose proof (special_filter_safe_Znth_range_146 input_l i PreH6 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_specialFilter_entail_wit_2_split_goal_3 : specialFilter_entail_wit_2_split_goal_3.
Proof.
  unfold specialFilter_entail_wit_2_split_goal_3; intros.
  pre_process; entailer!.
Qed.

Lemma proof_of_specialFilter_entail_wit_2 : specialFilter_entail_wit_2.
Proof.
  unfold specialFilter_entail_wit_2; right; intros.
  pre_process; entailer!;
    try pose proof (special_filter_safe_Znth_range_146 input_l i PreH6 ltac:(lia));
    lia.
Qed.

Lemma proof_of_specialFilter_entail_wit_3_split_goal_1 : specialFilter_entail_wit_3_split_goal_1.
Proof.
  unfold specialFilter_entail_wit_3_split_goal_1; intros.
  pre_process; entailer!.
  subst current.
  eapply special_filter_safe_Znth_first_init_146; eauto; lia.
Qed.

Lemma proof_of_specialFilter_entail_wit_3 : specialFilter_entail_wit_3.
Proof.
  unfold specialFilter_entail_wit_3; right; intros.
  pre_process; entailer!.
  subst current.
  eapply special_filter_safe_Znth_first_init_146; eauto; lia.
Qed.

Lemma proof_of_specialFilter_entail_wit_5_split_goal_1 : specialFilter_entail_wit_5_split_goal_1.
Proof.
  unfold specialFilter_entail_wit_5_split_goal_1; intros.
  pre_process; entailer!.
  pose proof (first_digit_state_step_146 current first PreH18 ltac:(lia)) as Hnext.
  exact Hnext.
Qed.

Lemma proof_of_specialFilter_entail_wit_5_split_goal_2 : specialFilter_entail_wit_5_split_goal_2.
Proof.
  unfold specialFilter_entail_wit_5_split_goal_2; intros.
  pre_process; entailer!.
  pose proof (first_digit_state_step_146 current first PreH18 ltac:(lia)) as Hnext.
  unfold first_digit_state_146 in Hnext.
  lia.
Qed.

Lemma proof_of_specialFilter_entail_wit_5_split_goal_3 : specialFilter_entail_wit_5_split_goal_3.
Proof.
  unfold specialFilter_entail_wit_5_split_goal_3; intros.
  pre_process; entailer!.
  pose proof (first_digit_state_step_146 current first PreH18 ltac:(lia)) as Hnext.
  unfold first_digit_state_146 in Hnext.
  lia.
Qed.

Lemma proof_of_specialFilter_entail_wit_5 : specialFilter_entail_wit_5.
Proof.
  unfold specialFilter_entail_wit_5; right; intros.
  pre_process; entailer!;
    pose proof (first_digit_state_step_146 current first PreH18 ltac:(lia)) as Hnext;
    try exact Hnext; unfold first_digit_state_146 in Hnext; lia.
Qed.

Lemma proof_of_specialFilter_entail_wit_7_split_goal_1 : specialFilter_entail_wit_7_split_goal_1.
Proof.
  unfold specialFilter_entail_wit_7_split_goal_1; intros.
  pre_process; entailer!.
  eapply special_filter_prefix_step_one_146; [lia | exact PreH20 |].
  replace (Znth i input_l 0) with current by lia.
  eapply (special_score_one_from_scan_146 input_l i current first last); eauto; lia.
Qed.

Lemma proof_of_specialFilter_entail_wit_7 : specialFilter_entail_wit_7.
Proof.
  unfold specialFilter_entail_wit_7; right; intros.
  pre_process; entailer!.
  eapply special_filter_prefix_step_one_146; [lia | exact PreH20 |].
  replace (Znth i input_l 0) with current by lia.
  eapply (special_score_one_from_scan_146 input_l i current first last); eauto; lia.
Qed.

Lemma proof_of_specialFilter_entail_wit_8_1 : specialFilter_entail_wit_8_1.
Proof.
  unfold specialFilter_entail_wit_8_1; intros.
  rewrite <- derivable1_orp_intros1.
  pre_process; entailer!.
  eapply special_filter_prefix_step_zero_146; [lia | exact PreH20 |].
  replace (Znth i input_l 0) with current by lia.
  eapply (special_score_zero_from_scan_last_146 input_l i current first last); eauto; lia.
Qed.

Lemma proof_of_specialFilter_entail_wit_8_2 : specialFilter_entail_wit_8_2.
Proof.
  unfold specialFilter_entail_wit_8_2; intros.
  rewrite <- derivable1_orp_intros2.
  pre_process; entailer!.
  eapply special_filter_prefix_step_zero_146; [lia | exact PreH19 |].
  replace (Znth i input_l 0) with current by lia.
  eapply (special_score_zero_from_scan_first_146 input_l i current first last); eauto; lia.
Qed.

Lemma proof_of_specialFilter_entail_wit_9_split_goal_1 : specialFilter_entail_wit_9_split_goal_1.
Proof.
  unfold specialFilter_entail_wit_9_split_goal_1; intros.
  pre_process; entailer!.
  eapply special_filter_prefix_step_zero_146; [lia | exact PreH14 |].
  subst current.
  eapply special_filter_safe_Znth_small_score_146; eauto; lia.
Qed.

Lemma proof_of_specialFilter_entail_wit_9 : specialFilter_entail_wit_9.
Proof.
  unfold specialFilter_entail_wit_9; right; intros.
  pre_process; entailer!.
  eapply special_filter_prefix_step_zero_146; [lia | exact PreH14 |].
  subst current.
  eapply special_filter_safe_Znth_small_score_146; eauto; lia.
Qed.

Lemma proof_of_specialFilter_return_wit_1_split_goal_1 : specialFilter_return_wit_1_split_goal_1.
Proof.
  unfold specialFilter_return_wit_1_split_goal_1; intros.
  pre_process; entailer!.
  apply special_filter_prefix_final_146.
  replace (Zlength input_l) with i by lia.
  exact PreH11.
Qed.

Lemma proof_of_specialFilter_return_wit_1 : specialFilter_return_wit_1.
Proof.
  unfold specialFilter_return_wit_1; right; intros.
  pre_process; entailer!.
  apply special_filter_prefix_final_146.
  replace (Zlength input_l) with i by lia.
  exact PreH11.
Qed.
