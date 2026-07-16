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
From SimpleC.EE Require Import C_161_goal.
From SimpleC.EE Require Import C_161_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_161.
Local Open Scope sac.

Lemma proof_of_solve_entail_wit_1_split_goal_1 : solve_entail_wit_1_split_goal_1.
Proof.
  unfold solve_entail_wit_1_split_goal_1.
  intros. entailer!.
  apply flip_scan_state_z_161_init.
Qed.

Lemma proof_of_solve_entail_wit_1_split_goal_2 : solve_entail_wit_1_split_goal_2.
Proof.
  unfold solve_entail_wit_1_split_goal_2.
  intros. entailer!.
  rewrite PreH3. apply string_length_nonneg.
Qed.

Lemma proof_of_solve_entail_wit_1_split_goal_spatial : solve_entail_wit_1_split_goal_spatial.
Proof. unfold solve_entail_wit_1_split_goal_spatial. intros. entailer!. Qed.

Lemma proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Proof.
  unfold solve_entail_wit_1.
  right. intros. entailer!.
  - rewrite PreH3. apply string_length_nonneg.
  - apply flip_scan_state_z_161_init.
Qed.

Lemma proof_of_solve_entail_wit_2_1_split_goal_1 : solve_entail_wit_2_1_split_goal_1.
Proof.
  unfold solve_entail_wit_2_1_split_goal_1.
  intros. entailer!.
  assert (Hi : 0 <= i < Zlength input).
  { unfold string_length in PreH7. lia. }
  assert (Hc : 0 <= Znth i (c_string input) 0 <= 127).
  { apply c_string_char_bound; [exact PreH16 |]. unfold string_length. lia. }
  rewrite signed_last_nbits_8_eq_161 by exact Hc.
  rewrite c_string_inside_eq_161 by exact Hi.
  eapply flip_scan_state_z_161_step_nonletter; try eassumption.
  - reflexivity.
  - unfold upper_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
  - unfold lower_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
Qed.

Lemma proof_of_solve_entail_wit_2_1_split_goal_2 : solve_entail_wit_2_1_split_goal_2.
Proof.
  unfold solve_entail_wit_2_1_split_goal_2.
  intros. entailer!.
  pose proof (c_string_char_bound input i PreH16) as Hc.
  specialize (Hc ltac:(unfold string_length in PreH7 |- *; lia)). lia.
Qed.

Lemma proof_of_solve_entail_wit_2_1 : solve_entail_wit_2_1.
Proof.
  unfold solve_entail_wit_2_1. right. intros. entailer!.
  - pose proof (c_string_char_bound input i PreH16) as Hc.
    specialize (Hc ltac:(unfold string_length in PreH7 |- *; lia)). lia.
  - assert (Hi : 0 <= i < Zlength input).
    { unfold string_length in PreH7. lia. }
    assert (Hc : 0 <= Znth i (c_string input) 0 <= 127).
    { apply c_string_char_bound; [exact PreH16 |]. unfold string_length. lia. }
    rewrite signed_last_nbits_8_eq_161 by exact Hc.
    rewrite c_string_inside_eq_161 by exact Hi.
    eapply flip_scan_state_z_161_step_nonletter; try eassumption.
    + reflexivity.
    + unfold upper_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
    + unfold lower_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
Qed.

Lemma proof_of_solve_entail_wit_2_2_split_goal_1 : solve_entail_wit_2_2_split_goal_1.
Proof.
  unfold solve_entail_wit_2_2_split_goal_1.
  intros. entailer!.
  assert (Hi : 0 <= i < Zlength input).
  { unfold string_length in PreH5. lia. }
  assert (Hc : 0 <= Znth i (c_string input) 0 <= 127).
  { apply c_string_char_bound; [exact PreH14 |]. unfold string_length. lia. }
  rewrite signed_last_nbits_8_eq_161 by exact Hc.
  rewrite c_string_inside_eq_161 by exact Hi.
  eapply flip_scan_state_z_161_step_nonletter; try eassumption.
  - reflexivity.
  - unfold upper_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
  - unfold lower_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
Qed.

Lemma proof_of_solve_entail_wit_2_2_split_goal_2 : solve_entail_wit_2_2_split_goal_2.
Proof.
  unfold solve_entail_wit_2_2_split_goal_2.
  intros. entailer!.
  pose proof (c_string_char_bound input i PreH14) as Hc.
  specialize (Hc ltac:(unfold string_length in PreH5 |- *; lia)). lia.
Qed.

Lemma proof_of_solve_entail_wit_2_2 : solve_entail_wit_2_2.
Proof.
  unfold solve_entail_wit_2_2. right. intros. entailer!.
  - pose proof (c_string_char_bound input i PreH14) as Hc.
    specialize (Hc ltac:(unfold string_length in PreH5 |- *; lia)). lia.
  - assert (Hi : 0 <= i < Zlength input).
    { unfold string_length in PreH5. lia. }
    assert (Hc : 0 <= Znth i (c_string input) 0 <= 127).
    { apply c_string_char_bound; [exact PreH14 |]. unfold string_length. lia. }
    rewrite signed_last_nbits_8_eq_161 by exact Hc.
    rewrite c_string_inside_eq_161 by exact Hi.
    eapply flip_scan_state_z_161_step_nonletter; try eassumption.
    + reflexivity.
    + unfold upper_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
    + unfold lower_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
Qed.

Lemma proof_of_solve_entail_wit_2_3_split_goal_1 : solve_entail_wit_2_3_split_goal_1.
Proof.
  unfold solve_entail_wit_2_3_split_goal_1.
  intros. entailer!.
  assert (Hi : 0 <= i < Zlength input).
  { unfold string_length in PreH6. lia. }
  rewrite c_string_inside_eq_161 by exact Hi.
  eapply flip_scan_state_z_161_step_nonletter; try eassumption.
  - reflexivity.
  - unfold upper_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
  - unfold lower_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
Qed.

Lemma proof_of_solve_entail_wit_2_3 : solve_entail_wit_2_3.
Proof.
  unfold solve_entail_wit_2_3. right. intros. entailer!.
  assert (Hi : 0 <= i < Zlength input).
  { unfold string_length in PreH6. lia. }
  rewrite c_string_inside_eq_161 by exact Hi.
  eapply flip_scan_state_z_161_step_nonletter; try eassumption.
  - reflexivity.
  - unfold upper_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
  - unfold lower_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
Qed.

Lemma proof_of_solve_entail_wit_2_4_split_goal_1 : solve_entail_wit_2_4_split_goal_1.
Proof.
  unfold solve_entail_wit_2_4_split_goal_1.
  intros. entailer!.
  assert (Hi : 0 <= i < Zlength input).
  { unfold string_length in PreH7. lia. }
  rewrite c_string_inside_eq_161 by exact Hi.
  eapply flip_scan_state_z_161_step_lower; try eassumption.
  - reflexivity.
  - unfold upper_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
  - unfold lower_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
Qed.

Lemma proof_of_solve_entail_wit_2_4 : solve_entail_wit_2_4.
Proof.
  unfold solve_entail_wit_2_4. right. intros. entailer!.
  assert (Hi : 0 <= i < Zlength input).
  { unfold string_length in PreH7. lia. }
  rewrite c_string_inside_eq_161 by exact Hi.
  eapply flip_scan_state_z_161_step_lower; try eassumption.
  - reflexivity.
  - unfold upper_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
  - unfold lower_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
Qed.

Lemma proof_of_solve_entail_wit_2_5_split_goal_1 : solve_entail_wit_2_5_split_goal_1.
Proof.
  unfold solve_entail_wit_2_5_split_goal_1.
  intros. entailer!.
  assert (Hi : 0 <= i < Zlength input).
  { unfold string_length in PreH5. lia. }
  rewrite c_string_inside_eq_161 by exact Hi.
  eapply flip_scan_state_z_161_step_upper; try eassumption.
  - reflexivity.
  - unfold upper_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
Qed.

Lemma proof_of_solve_entail_wit_2_5 : solve_entail_wit_2_5.
Proof.
  unfold solve_entail_wit_2_5. right. intros. entailer!.
  assert (Hi : 0 <= i < Zlength input).
  { unfold string_length in PreH5. lia. }
  rewrite c_string_inside_eq_161 by exact Hi.
  eapply flip_scan_state_z_161_step_upper; try eassumption.
  - reflexivity.
  - unfold upper_z_161. rewrite <- c_string_inside_eq_161 by exact Hi. lia.
Qed.

Lemma proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Proof.
  unfold solve_entail_wit_4. right. intros.
  assert (i = n) by lia. subst i.
  Exists output_2. entailer!.
Qed.

Lemma proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Proof.
  unfold solve_entail_wit_5. right. intros.
  subst nletter.
  destruct (flip_scan_state_z_161_finish_no_letter
    input output_2 n PreH4 PreH9) as [Hnone Hflip].
  assert (Hflipout : flip_output_z_161 input output_2).
  { exact Hflip. }
  assert (Hvalidout : valid_string output_2).
  { rewrite Hflip. apply flip_output_valid_161. exact PreH10. }
  Exists output_2. unfold c_string. entailer!.
Qed.

Lemma proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Proof.
  unfold solve_entail_wit_6. right. intros.
  Exists output_2. entailer!.
  apply reverse_scan_state_z_161_init.
  rewrite PreH5. apply string_length_nonneg.
Qed.

Lemma proof_of_solve_entail_wit_7 : solve_entail_wit_7.
Proof.
  unfold solve_entail_wit_7. right. intros.
  Exists output_2. entailer!.
  assert (Hj : 0 <= j < Zlength input).
  { unfold string_length in PreH4. lia. }
  assert (Hk : 0 <= (n - 1) - j < Zlength input).
  { unfold string_length in PreH4. lia. }
  rewrite c_string_inside_eq_161 by exact Hk.
  eapply reverse_scan_state_z_161_step; try eassumption.
  unfold string_length in PreH4. rewrite PreH4. reflexivity.
Qed.

Lemma proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Proof.
  unfold solve_entail_wit_9. right. intros.
  assert (j = n) by lia. subst j.
  assert (Hnlen : n = Zlength input).
  { unfold string_length in PreH3. exact PreH3. }
  pose proof (reverse_scan_state_z_161_finish
    input rev_output_2 n Hnlen PreH12) as Hrev.
  assert (Hrevout : reverse_output_z_161 input rev_output_2).
  { exact Hrev. }
  assert (Hvalidrev : valid_string rev_output_2).
  { rewrite Hrev. apply rev_valid_161. exact PreH13. }
  assert (Hspec : problem_161_spec_z input rev_output_2).
  { eapply problem_161_spec_z_intro_rev; eauto. }
  Exists rev_output_2 output_2. entailer!.
Qed.

Lemma proof_of_solve_entail_wit_10 : solve_entail_wit_10.
Proof.
  unfold solve_entail_wit_10. right. intros.
  assert (Hnlen : n = Zlength input).
  { unfold string_length in PreH4. exact PreH4. }
  destruct (flip_scan_state_z_161_finish_has_letter
    input output_2 n nletter Hnlen PreH1 PreH9) as [Hhas Hflip].
  assert (Hflipout : flip_output_z_161 input output_2).
  { exact Hflip. }
  assert (Hvalidout : valid_string output_2).
  { rewrite Hflip. apply flip_output_valid_161. exact PreH10. }
  assert (Hspec : problem_161_spec_z input output_2).
  { eapply problem_161_spec_z_intro_flip; eauto. }
  Exists output_2. unfold c_string. entailer!.
Qed.

Lemma proof_of_solve_return_wit_1 : solve_return_wit_1.
Proof.
  unfold solve_return_wit_1. right. intros.
  Exists output_2. unfold string_length.
  rewrite (flip_output_z_161_length input output_2 PreH8).
  unfold string_length in PreH3. entailer!.
  rewrite <- PreH3. entailer!.
Qed.

Lemma proof_of_solve_return_wit_2 : solve_return_wit_2.
Proof.
  unfold solve_return_wit_2. right. intros.
  Exists rev_output. unfold string_length.
  rewrite (reverse_output_z_161_length input rev_output PreH12).
  unfold string_length in PreH4. entailer!.
  rewrite <- PreH4. entailer!.
Qed.

Lemma proof_of_solve_partial_solve_wit_2_pure_split_goal_1 : solve_partial_solve_wit_2_pure_split_goal_1.
Proof.
  unfold solve_partial_solve_wit_2_pure_split_goal_1.
  intros. entailer!.
  rewrite PreH5. pose proof (string_length_nonneg input). lia.
Qed.

Lemma proof_of_solve_partial_solve_wit_2_pure : solve_partial_solve_wit_2_pure.
Proof.
  unfold solve_partial_solve_wit_2_pure. right. intros. entailer!.
  rewrite PreH5. pose proof (string_length_nonneg input). lia.
Qed.

Lemma proof_of_solve_partial_solve_wit_9_pure_split_goal_1 : solve_partial_solve_wit_9_pure_split_goal_1.
Proof.
  unfold solve_partial_solve_wit_9_pure_split_goal_1.
  intros. entailer!.
  rewrite PreH11. pose proof (string_length_nonneg input). lia.
Qed.

Lemma proof_of_solve_partial_solve_wit_9_pure : solve_partial_solve_wit_9_pure.
Proof.
  unfold solve_partial_solve_wit_9_pure. right. intros. entailer!.
  rewrite PreH11. pose proof (string_length_nonneg input). lia.
Qed.

Lemma proof_of_solve_partial_solve_wit_12_pure_split_goal_1 : solve_partial_solve_wit_12_pure_split_goal_1.
Proof.
  unfold solve_partial_solve_wit_12_pure_split_goal_1.
  intros. entailer!.
  rewrite Zlength_c_string_161.
  rewrite (flip_output_z_161_length input output PreH21).
  unfold string_length in PreH14. lia.
Qed.

Lemma proof_of_solve_partial_solve_wit_12_pure : solve_partial_solve_wit_12_pure.
Proof.
  unfold solve_partial_solve_wit_12_pure. right. intros. entailer!.
  rewrite Zlength_c_string_161.
  rewrite (flip_output_z_161_length input output PreH21).
  unfold string_length in PreH14. lia.
Qed.
