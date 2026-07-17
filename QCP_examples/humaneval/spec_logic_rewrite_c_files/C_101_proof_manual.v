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
From SimpleC.EE Require Import C_101_goal.
From SimpleC.EE Require Import C_101_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.coins_101.
Local Open Scope sac.

Lemma proof_of_words_string_entail_wit_1 : words_string_entail_wit_1.
Proof.
  unfold words_string_entail_wit_1; left; intros.
  subst input_ptr.
  Exists (@nil Z) (@nil (list Z)).
  rewrite PtrArray.seg_empty by lia.
  unfold words_rows_heap_101, store_string.
  pose proof (split_prefix_state_init_101 input) as Hstate.
  entailer!.
Qed.

Lemma proof_of_words_string_entail_wit_2_1 : words_string_entail_wit_2_1.
Proof.
  unfold words_string_entail_wit_2_1; left; intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH10. exact PreH10. }
  pose proof (split_prefix_state_open_101 input i start output_words_2
    PreH21 ltac:(lia) ltac:(lia)) as [Hbounds Hopen].
  assert (Hwordlen : Zlength (sublist start i input) = i - start)
    by (rewrite Zlength_sublist by lia; lia).
  assert (Hascii : all_ascii (sublist start i input)).
  { exact (problem_pre_valid_sublist_ascii_101 input start i
      PreH22 PreH23 ltac:(lia) ltac:(lia)). }
  assert (Hclosing : closing_delimiter_101 input i n).
  { unfold closing_delimiter_101. right. split; [lia|].
    right. exact PreH4. }
  sep_apply (prepare_word_copy_heap_101 input input_ptr retval start i n
    Hbounds PreH7 PreH10).
  Exists output_ptrs_2 output_words_2
    (sublist i (n + 1) (c_string input))
    (sublist 0 start (c_string input)).
  entailer!.
Qed.

Lemma proof_of_words_string_entail_wit_2_2 : words_string_entail_wit_2_2.
Proof.
  unfold words_string_entail_wit_2_2; left; intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH9. exact PreH9. }
  pose proof (split_prefix_state_open_101 input i start output_words_2
    PreH20 ltac:(lia) ltac:(lia)) as [Hbounds Hopen].
  assert (Hwordlen : Zlength (sublist start i input) = i - start)
    by (rewrite Zlength_sublist by lia; lia).
  assert (Hascii : all_ascii (sublist start i input)).
  { exact (problem_pre_valid_sublist_ascii_101 input start i
      PreH21 PreH22 ltac:(lia) ltac:(lia)). }
  assert (Hclosing : closing_delimiter_101 input i n).
  { unfold closing_delimiter_101. right. split; [lia|].
    left. exact PreH4. }
  sep_apply (prepare_word_copy_heap_101 input input_ptr retval start i n
    Hbounds PreH6 PreH9).
  Exists output_ptrs_2 output_words_2
    (sublist i (n + 1) (c_string input))
    (sublist 0 start (c_string input)).
  entailer!.
Qed.

Lemma proof_of_words_string_entail_wit_2_3 : words_string_entail_wit_2_3.
Proof.
  unfold words_string_entail_wit_2_3; left; intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH8. exact PreH8. }
  pose proof (split_prefix_state_open_101 input i start output_words_2
    PreH19 ltac:(lia) ltac:(lia)) as [Hbounds Hopen].
  assert (Hwordlen : Zlength (sublist start i input) = i - start)
    by (rewrite Zlength_sublist by lia; lia).
  assert (Hascii : all_ascii (sublist start i input)).
  { exact (problem_pre_valid_sublist_ascii_101 input start i
      PreH20 PreH21 ltac:(lia) ltac:(lia)). }
  assert (Hclosing : closing_delimiter_101 input i n).
  { unfold closing_delimiter_101. left. lia. }
  sep_apply (prepare_word_copy_heap_101 input input_ptr retval start i n
    Hbounds PreH5 PreH8).
  Exists output_ptrs_2 output_words_2
    (sublist i (n + 1) (c_string input))
    (sublist 0 start (c_string input)).
  entailer!.
Qed.

Lemma proof_of_words_string_entail_wit_3 : words_string_entail_wit_3.
Proof.
  unfold words_string_entail_wit_3; left; intros; subst len.
  assert (Hlen : Zlength input = n).
  { unfold string_length in PreH11. lia. }
  rewrite CharArray.undef_seg_empty by lia.
  sep_apply_l_atomic (CharArray.full_to_seg
    (input_ptr + start * sizeof(CHAR)) (i - start) (sublist start i input)).
  rewrite <- (CharArray.seg_0_shift input_ptr start i (sublist start i input)).
  rewrite PreH9, PreH10.
  sep_apply (CharArray.seg_merge_to_seg input_ptr 0 start i
    (sublist 0 start (c_string input)) (sublist start i input) ltac:(lia)).
  sep_apply (CharArray.seg_merge_to_full input_ptr 0 i (n + 1)
    (sublist 0 start (c_string input) ++ sublist start i input)
    (sublist i (n + 1) (c_string input)) ltac:(lia)).
  rewrite split_c_string_contents_101 by lia.
  replace (input_ptr + 0 * sizeof(CHAR)) with input_ptr by lia.
  replace (n + 1 - 0) with (n + 1) by lia.
  Exists output_ptrs_2 output_words_2.
  rewrite (c_string_sublist_shape_101 input start i (i - start)
    eq_refl PreH7).
  unfold store_string, string_length.
  entailer!.
  unfold string_lib.c_string, naive_C_Rules.c_string.
  rewrite Hlen.
  entailer!.
Qed.

Lemma proof_of_words_string_entail_wit_4_1 : words_string_entail_wit_4_1.
Proof.
  unfold words_string_entail_wit_4_1; left; intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH7. exact PreH7. }
  pose proof (split_prefix_state_close_with_closing_101
    input i start output_words_2 n PreH20 PreH3 PreH5 Hlen PreH19) as Hstate.
  assert (Hrows :
    CharArray.full w (Zlength (c_string (sublist start i input)))
      (c_string (sublist start i input)) **
    words_rows_heap_101 output_ptrs_2 output_words_2 |--
    words_rows_heap_101 (output_ptrs_2 ++ (w :: nil))
      (output_words_2 ++ (sublist start i input :: nil))).
  { rewrite derivable1_sepcon_comm.
    apply words_rows_heap_101_app. lia. }
  sep_apply Hrows.
  Exists (output_ptrs_2 ++ (w :: nil))
    (output_words_2 ++ (sublist start i input :: nil)).
  unfold store_string.
  repeat rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!.
Qed.

Lemma proof_of_words_string_entail_wit_4_2 : words_string_entail_wit_4_2.
Proof.
  unfold words_string_entail_wit_4_2; left; intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH6. exact PreH6. }
  pose proof (split_prefix_state_finish_closed_101 input i start
    output_words_2 PreH17 PreH1 ltac:(lia)) as Hstate.
  Exists output_ptrs_2 output_words_2.
  entailer!.
Qed.

Lemma proof_of_words_string_entail_wit_4_3 : words_string_entail_wit_4_3.
Proof.
  unfold words_string_entail_wit_4_3; left; intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH7. exact PreH7. }
  rewrite (Znth_c_string_input_101 input i) in PreH2 by lia.
  pose proof (split_prefix_state_closed_step_101 input i start
    output_words_2 PreH18 PreH1 ltac:(lia) ltac:(
      rewrite PreH2; apply is_delimiter_z_32_101)) as Hstate.
  Exists output_ptrs_2 output_words_2.
  entailer!.
Qed.

Lemma proof_of_words_string_entail_wit_4_4 : words_string_entail_wit_4_4.
Proof.
  unfold words_string_entail_wit_4_4; left; intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH8. exact PreH8. }
  rewrite (Znth_c_string_input_101 input i) in PreH2 by lia.
  pose proof (split_prefix_state_closed_step_101 input i start
    output_words_2 PreH19 PreH1 ltac:(lia) ltac:(
      rewrite PreH2; apply is_delimiter_z_44_101)) as Hstate.
  Exists output_ptrs_2 output_words_2.
  entailer!.
Qed.

Lemma proof_of_words_string_entail_wit_4_5 : words_string_entail_wit_4_5.
Proof.
  unfold words_string_entail_wit_4_5; left; intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH8. exact PreH8. }
  rewrite (Znth_c_string_input_101 input i) in PreH2 by lia.
  rewrite (Znth_c_string_input_101 input i) in PreH3 by lia.
  pose proof (split_prefix_state_start_step_101 input i start
    output_words_2 PreH19 PreH1 PreH21 ltac:(lia)
      (is_delimiter_z_false_101 _ PreH3 PreH2)) as Hstate.
  Exists output_ptrs_2 output_words_2.
  entailer!.
Qed.

Lemma proof_of_words_string_entail_wit_4_6 : words_string_entail_wit_4_6.
Proof.
  unfold words_string_entail_wit_4_6; left; intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH8. exact PreH8. }
  rewrite (Znth_c_string_input_101 input i) in PreH2 by lia.
  rewrite (Znth_c_string_input_101 input i) in PreH3 by lia.
  pose proof (split_prefix_state_open_step_101 input i start
    output_words_2 PreH19 ltac:(lia) PreH21 ltac:(lia)
      (is_delimiter_z_false_101 _ PreH3 PreH2)) as Hstate.
  Exists output_ptrs_2 output_words_2.
  entailer!.
Qed.

Lemma proof_of_words_string_return_wit_1 : words_string_return_wit_1.
Proof.
  unfold words_string_return_wit_1; left; intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH4. exact PreH4. }
  pose proof (split_prefix_state_problem_spec_101 input i start
    output_words_2 PreH15 ltac:(lia) ltac:(lia)) as Hspec.
  Exists cap_2 output_ptrs_2 output_words_2 output_size_2 data_2.
  unfold store_string.
  entailer!.
Qed.

Lemma proof_of_words_string_partial_solve_wit_4_pure_split_goal_1 : words_string_partial_solve_wit_4_pure_split_goal_1.
Proof.
  unfold words_string_partial_solve_wit_4_pure_split_goal_1.
  intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH19. exact PreH19. }
  pose proof (split_prefix_state_open_101 input i start output_words
    PreH30 ltac:(lia) ltac:(lia)) as [Hbounds Hopen].
  entailer!.
Qed.

Lemma proof_of_words_string_partial_solve_wit_4_pure : words_string_partial_solve_wit_4_pure.
Proof.
  unfold words_string_partial_solve_wit_4_pure; left; intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH6. exact PreH6. }
  pose proof (split_prefix_state_open_101 input i start output_words
    PreH17 ltac:(lia) ltac:(lia)) as [Hbounds Hopen].
  entailer!.
Qed.

Lemma proof_of_words_string_partial_solve_wit_5_pure_split_goal_1 : words_string_partial_solve_wit_5_pure_split_goal_1.
Proof.
  unfold words_string_partial_solve_wit_5_pure_split_goal_1.
  intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH20. exact PreH20. }
  pose proof (split_prefix_state_open_101 input i start output_words
    PreH31 ltac:(lia) ltac:(lia)) as [Hbounds Hopen].
  entailer!.
Qed.

Lemma proof_of_words_string_partial_solve_wit_5_pure : words_string_partial_solve_wit_5_pure.
Proof.
  unfold words_string_partial_solve_wit_5_pure; left; intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH7. exact PreH7. }
  pose proof (split_prefix_state_open_101 input i start output_words
    PreH18 ltac:(lia) ltac:(lia)) as [Hbounds Hopen].
  entailer!.
Qed.

Lemma proof_of_words_string_partial_solve_wit_6_pure_split_goal_1 : words_string_partial_solve_wit_6_pure_split_goal_1.
Proof.
  unfold words_string_partial_solve_wit_6_pure_split_goal_1.
  intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH21. exact PreH21. }
  pose proof (split_prefix_state_open_101 input i start output_words
    PreH32 ltac:(lia) ltac:(lia)) as [Hbounds Hopen].
  entailer!.
Qed.

Lemma proof_of_words_string_partial_solve_wit_6_pure : words_string_partial_solve_wit_6_pure.
Proof.
  unfold words_string_partial_solve_wit_6_pure; left; intros.
  assert (Hlen : n = Zlength input).
  { unfold string_length in PreH8. exact PreH8. }
  pose proof (split_prefix_state_open_101 input i start output_words
    PreH19 ltac:(lia) ltac:(lia)) as [Hbounds Hopen].
  entailer!.
Qed.
