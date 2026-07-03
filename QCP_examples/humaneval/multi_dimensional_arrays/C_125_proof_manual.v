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
From SimpleC.EE Require Import C_125_goal.
From SimpleC.EE Require Import C_125_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_125.
Local Open Scope sac.

Ltac c125_entailer :=
  constructor; pre_process_default; entailer!; try lia.

Ltac solve_rem10_bound :=
  match goal with
  | H : 0 <= ?tmp |- context[?tmp % 10] =>
      pose proof (Z.rem_bound_pos tmp 10 ltac:(lia) ltac:(lia)); lia
  end.

Ltac solve_contains_zb_125 :=
  match goal with
  | Hres : strchr_result ?s ?c ?ret ?p,
    Hnz : ?ret <> 0
    |- contains_zb_125 ?s ?c = true =>
      eapply strchr_result_nonzero_contains_zb_125;
      [lia | exact Hnz | exact Hres]
  | Hres : strchr_result ?s ?c ?ret ?p,
    Hz : ?ret = 0
    |- contains_zb_125 ?s ?c = false =>
      subst ret;
      eapply strchr_result_zero_contains_zb_125;
      [lia | exact Hres]
  end.

Ltac split_words_entailer_125 :=
  unfold store_string;
  entailer!;
  try solve [assumption | solve_contains_zb_125 | lia].

Ltac split_words_scan_init_125 :=
  Exists (@nil Z) (@nil (list Z));
  repeat match goal with
  | H : ?x = _ |- _ => subst x
  end;
  unfold split_scan_state_125, split_completed_rows_125,
    split_completed_payloads_125, split_scan_current_125,
    split_words_rows_heap_125;
  simpl;
  rewrite ?PtrArray.seg_empty;
  match goal with
  | |- ?P |-- _ =>
      match P with
      | context [PtrArray.undef_full ?p ?m] =>
          sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg p m)
      end
  end;
  entailer!;
  try solve [
    assumption
  | lia
  | apply string_length_nonneg
  | match goal with
    | s : list Z |- _ =>
        pose proof (string_length_nonneg s);
        lia
    end
  ].

Lemma c125_orp_intros_4_2 : forall A B C D,
  B |-- A || B || C || D.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_orp_intros2.
  - eapply derivable1_trans.
    + apply derivable1_orp_intros1.
    + apply derivable1_orp_intros1.
Qed.

Lemma c125_orp_intros_4_3 : forall A B C D,
  C |-- A || B || C || D.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_orp_intros2.
  - apply derivable1_orp_intros1.
Qed.

Lemma c125_orp_intros_3_2 : forall A B C,
  B |-- A || B || C.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_orp_intros2.
  - apply derivable1_orp_intros1.
Qed.

Lemma c125_orp_intros_3_3 : forall A B C,
  C |-- A || B || C.
Proof.
  intros.
  apply derivable1_orp_intros2.
Qed.

Lemma c125_orp_intros_3_mid : forall A B C,
  B |-- A || B || C.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_orp_intros2.
  - apply derivable1_orp_intros1.
Qed.

Lemma c125_orp_intros_3_second : forall A B C,
  B |-- A || B || C.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_orp_intros2.
  - apply derivable1_orp_intros1.
Qed.

Lemma char_undef_missing_i_tail_pos_125 : forall x pos,
  0 <= pos ->
  CharArray.undef_missing_i x pos 0 (pos + 1) |--
  CharArray.undef_seg x 0 pos.
Proof.
  intros.
  replace (CharArray.undef_missing_i x pos 0 (pos + 1))
    with (CharArray.undef_missing_i x (pos + 1 - 1) 0 (pos + 1))
    by (f_equal; lia).
  replace (CharArray.undef_seg x 0 pos)
    with (CharArray.undef_seg x 0 (pos + 1 - 1))
    by (f_equal; lia).
  apply CharArray.undef_missing_i_to_undef_seg_tail.
  lia.
Qed.

Lemma char_full_cons_merge_125 : forall buf pos len v done,
  0 <= len ->
  (buf + pos * sizeof(CHAR)) # Char |-> v **
  CharArray.full (buf + (pos + 1) * sizeof(CHAR)) len done
  |-- CharArray.full (buf + pos * sizeof(CHAR)) (len + 1) (v :: done).
Proof.
  intros.
  sep_apply_l_atomic (CharArray.seg_single buf pos v).
  sep_apply_l_atomic (CharArray.seg_to_full buf pos (pos + 1) (v :: nil)).
  replace (pos + 1 - pos) with 1 by lia.
  replace (buf + (pos + 1) * sizeof(CHAR))
    with (buf + pos * sizeof(CHAR) + 1 * sizeof(CHAR)) by lia.
  replace (CharArray.full (buf + pos * sizeof(CHAR) + 1 * sizeof(CHAR)) len done)
    with (CharArray.full (buf + pos * sizeof(CHAR) + 1 * sizeof(CHAR)) (len + 1 - 1) done)
    by (f_equal; lia).
  sep_apply_l_atomic (CharArray.full_merge_to_full
    (buf + pos * sizeof(CHAR)) 1 (len + 1) (v :: nil) done ltac:(lia)).
  simpl.
  cancel.
Qed.

Lemma char_full_snoc_zero_125 : forall buf len done,
  Zlength done = len ->
  CharArray.full buf len done **
  (buf + len * sizeof(CHAR)) # Char |-> 0
  |-- CharArray.full buf (len + 1) (c_string done).
Proof.
  intros buf len done Hlen.
  unfold c_string.
  apply helper_chararray_full_snoc.
  rewrite <- Hlen.
  apply Zlength_nonneg.
Qed.

Lemma word_payload_125_empty_manual : forall s start,
  word_payload_125 s start start = @nil Z.
Proof.
  intros s start.
  unfold word_payload_125.
  apply sublist_nil.
  lia.
Qed.

Lemma proof_of_write_decimal_safety_wit_4_split_goal_1 : write_decimal_safety_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_write_decimal_safety_wit_4_split_goal_2 : write_decimal_safety_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_write_decimal_safety_wit_4 : write_decimal_safety_wit_4.
Proof.
  c125_entailer; solve_rem10_bound.
Qed.

Lemma proof_of_write_decimal_entail_wit_1_split_goal_1 : write_decimal_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_write_decimal_entail_wit_1_split_goal_spatial : write_decimal_entail_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_write_decimal_entail_wit_1 : write_decimal_entail_wit_1.
Proof.
  right.
  pre_process_default.
  entailer!.
  - sep_apply_l_atomic
      (CharArray.undef_full_split_to_undef_seg buf_pre digits_pre (digits_pre + 1)
         ltac:(lia)).
    sep_apply_l_atomic (CharArray.undef_seg_to_undef_full buf_pre 0 digits_pre).
    replace (buf_pre + 0 * sizeof(CHAR)) with buf_pre by lia.
    replace (digits_pre - 0) with (digits_pre - 1 + 1) by lia.
    cancel.
  - unfold decimal_write_state_125.
    split; [lia | rewrite Zlength_nil; lia].
Qed.

Lemma proof_of_write_decimal_entail_wit_2 : write_decimal_entail_wit_2.
Proof.
  left.
  pre_process_default.
  Exists (signed_last_nbits (48 + tmp % 10) 8 :: done_2).
  entailer!.
  - sep_apply_l_atomic (char_undef_missing_i_tail_pos_125 buf_pre pos ltac:(lia)).
    replace (pos - 1 + 1) with pos by lia.
    replace (digits_pre - (pos - 1) - 1) with ((digits_pre - pos - 1) + 1) by lia.
    sep_apply_l_atomic (char_full_cons_merge_125
      buf_pre pos (digits_pre - pos - 1) (signed_last_nbits (48 + tmp % 10) 8) done_2
      ltac:(lia)).
    cancel.
  - unfold decimal_write_state_125 in *.
    destruct PreH9 as [? ?].
    split; [lia | rewrite Zlength_cons; lia].
  - apply Z.quot_le_upper_bound; lia.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_write_decimal_return_wit_1 : write_decimal_return_wit_1.
Proof.
  left.
  pre_process_default.
  Exists done.
  entailer!.
  - unfold decimal_write_state_125 in PreH9.
    destruct PreH9 as [? Hlen].
    replace pos with (-1) in * by lia.
    replace (-1 + 1) with 0 by lia.
    replace (digits_pre - -1 - 1) with digits_pre by lia.
    replace (buf_pre + 0 * sizeof(CHAR)) with buf_pre by lia.
    assert (Hdone_len : Zlength done = digits_pre).
    { replace digits_pre with (digits_pre - -1 - 1) by lia.
      exact Hlen. }
    sep_apply (char_full_snoc_zero_125 buf_pre digits_pre done Hdone_len).
    rewrite (CharArray.undef_seg_empty buf_pre (digits_pre + 1)).
    entailer!.
  - unfold decimal_write_state_125 in PreH9.
    destruct PreH9 as [? Hlen].
    replace pos with (-1) in * by lia.
    lia.
Qed.

Lemma proof_of_split_words_entail_wit_1_1 : split_words_entail_wit_1_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply derivable1_orp_intros2.
  split_words_entailer_125.
Qed.

Lemma proof_of_split_words_entail_wit_1_2 : split_words_entail_wit_1_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply derivable1_orp_intros1.
  split_words_entailer_125.
Qed.

Lemma proof_of_split_words_entail_wit_2_1 : split_words_entail_wit_2_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_3.
  split_words_scan_init_125.
Qed.

Lemma proof_of_split_words_entail_wit_2_2 : split_words_entail_wit_2_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  split_words_scan_init_125.
Qed.

Lemma proof_of_split_words_entail_wit_3_1 : split_words_entail_wit_3_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((i - start) + 1)).
  replace (word_payload_125 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia;
        symmetry; apply word_payload_125_empty_manual).
  rewrite CharArray.full_empty.
  unfold split_scan_state_125 in PreH30.
  destruct PreH30 as [Hscan_range [Hscan_rows Hscan_cur]].
  destruct Hscan_cur as [[Hcur_empty Hstart_neg] | [Hstart_range Hcur_payload]];
    [lia |].
  unfold store_string.
  entailer!;
  try solve [assumption | lia | exact Hcur_payload].
  - unfold word_payload_125.
    unfold string_length in *.
    rewrite Zlength_sublist by lia.
    lia.
  - unfold split_scan_state_125.
    repeat split; try lia; auto.
Qed.

Lemma proof_of_split_words_entail_wit_3_2 : split_words_entail_wit_3_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_3_2.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((i - start) + 1)).
  replace (word_payload_125 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia;
        symmetry; apply word_payload_125_empty_manual).
  rewrite CharArray.full_empty.
  unfold split_scan_state_125 in PreH29.
  destruct PreH29 as [Hscan_range [Hscan_rows Hscan_cur]].
  destruct Hscan_cur as [[Hcur_empty Hstart_neg] | [Hstart_range Hcur_payload]];
    [lia |].
  unfold store_string.
  entailer!;
  try solve [assumption | lia | exact Hcur_payload].
  - unfold word_payload_125.
    unfold string_length in *.
    rewrite Zlength_sublist by lia.
    lia.
  - unfold split_scan_state_125.
    repeat split; try lia; auto.
Qed.

Lemma proof_of_split_words_entail_wit_4_1 : split_words_entail_wit_4_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [assumption | lia].
  rewrite word_payload_125_step_offset_c_string by (unfold string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_split_words_entail_wit_4_2 : split_words_entail_wit_4_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_3_2.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [assumption | lia].
  rewrite word_payload_125_step_offset_c_string by (unfold string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_split_words_entail_wit_5_1 : split_words_entail_wit_5_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_3_2.
  replace k with len in * by lia.
  Exists (output_ptrs_2 ++ (w :: nil))
    (output_rows_2 ++ (word_row_125 str_l start i :: nil)).
  assert (Hrow_len : Zlength (word_row_125 str_l start i) = len + 1).
  {
    rewrite word_row_125_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_word_payload_125 by (unfold string_length in *; lia).
    lia.
  }
  rewrite <- word_row_125_unfold.
  replace (word_row_125 str_l start (start + len))
    with (word_row_125 str_l start i) by (f_equal; lia).
  replace (len + 1) with (Zlength (word_row_125 str_l start i)) by lia.
  sep_apply (split_words_rows_heap_125_app_single
    output_ptrs_2 output_rows_2 w (word_row_125 str_l start i) ltac:(lia)).
  unfold store_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!;
  try solve [assumption | lia | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia].
  apply split_scan_state_125_step_delim_nonempty.
  - assumption.
  - lia.
  - rewrite PreH17 in PreH18.
    rewrite c_string_Znth_before_125 in PreH18 by (unfold string_length in *; lia).
    exact PreH18.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_5_2 : split_words_entail_wit_5_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  replace k with len in * by lia.
  Exists (output_ptrs_2 ++ (w :: nil))
    (output_rows_2 ++ (word_row_125 str_l start i :: nil)).
  assert (Hrow_len : Zlength (word_row_125 str_l start i) = len + 1).
  {
    rewrite word_row_125_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_word_payload_125 by (unfold string_length in *; lia).
    lia.
  }
  rewrite <- word_row_125_unfold.
  replace (word_row_125 str_l start (start + len))
    with (word_row_125 str_l start i) by (f_equal; lia).
  replace (len + 1) with (Zlength (word_row_125 str_l start i)) by lia.
  sep_apply (split_words_rows_heap_125_app_single
    output_ptrs_2 output_rows_2 w (word_row_125 str_l start i) ltac:(lia)).
  unfold store_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!;
  try solve [assumption | lia | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia].
  apply split_scan_state_125_step_delim_nonempty.
  - assumption.
  - lia.
  - rewrite PreH17 in PreH18.
    rewrite c_string_Znth_before_125 in PreH18 by (unfold string_length in *; lia).
    exact PreH18.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_6_1 : split_words_entail_wit_6_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_3.
  replace start with (-1) in * by lia.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [lia | exact PreH27].
  apply split_scan_state_125_step_delim_empty.
  - exact PreH27.
  - rewrite <- c_string_Znth_before_125 by (unfold string_length in *; lia).
    exact PreH2.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_6_2 : split_words_entail_wit_6_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  replace start with (-1) in * by lia.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [lia | exact PreH28].
  apply split_scan_state_125_step_delim_empty.
  - exact PreH28.
  - rewrite <- c_string_Znth_before_125 by (unfold string_length in *; lia).
    exact PreH2.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_7_1 : split_words_entail_wit_7_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_3.
  Exists output_ptrs_2 output_rows_2.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125; [exact PreH23 | unfold string_length in *; lia]).
  unfold store_string.
  entailer!;
  try solve [lia | exact PreH27].
  apply split_scan_state_125_step_nondelim_continue.
  - exact PreH27.
  - lia.
  - intro Hbad.
    apply PreH2.
    rewrite c_string_Znth_before_125 by (unfold string_length in *; lia).
    exact Hbad.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_7_2 : split_words_entail_wit_7_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  Exists output_ptrs_2 output_rows_2.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125; [exact PreH24 | unfold string_length in *; lia]).
  unfold store_string.
  entailer!;
  try solve [lia | exact PreH28].
  apply split_scan_state_125_step_nondelim_continue.
  - exact PreH28.
  - lia.
  - intro Hbad.
    apply PreH2.
    rewrite c_string_Znth_before_125 by (unfold string_length in *; lia).
    exact Hbad.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_7_3 : split_words_entail_wit_7_3.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_3.
  replace start with (-1) in * by lia.
  Exists output_ptrs_2 output_rows_2.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125; [exact PreH23 | unfold string_length in *; lia]).
  unfold store_string.
  entailer!;
  try solve [lia | exact PreH27].
  apply split_scan_state_125_step_nondelim_start.
  - exact PreH27.
  - intro Hbad.
    apply PreH2.
    rewrite c_string_Znth_before_125 by (unfold string_length in *; lia).
    exact Hbad.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_7_4 : split_words_entail_wit_7_4.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  replace start with (-1) in * by lia.
  Exists output_ptrs_2 output_rows_2.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125; [exact PreH24 | unfold string_length in *; lia]).
  unfold store_string.
  entailer!;
  try solve [lia | exact PreH28].
  apply split_scan_state_125_step_nondelim_start.
  - exact PreH28.
  - intro Hbad.
    apply PreH2.
    rewrite c_string_Znth_before_125 by (unfold string_length in *; lia).
    exact Hbad.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_9_1 : split_words_entail_wit_9_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  replace i with n in * by lia.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((n - start) + 1)).
  replace (word_payload_125 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia;
        symmetry; apply word_payload_125_empty_manual).
  rewrite CharArray.full_empty.
  unfold store_string.
  entailer!;
  try solve [assumption | lia].
  - apply Zlength_word_payload_125; unfold string_length in *; lia.
  - unfold split_scan_state_125 in PreH29.
    destruct PreH29 as [Hrange [Hrows Hcur]].
    destruct Hcur as [[Hempty Hbad] | [Hstart Hcur]];
      [lia | exact Hcur].
Qed.

Lemma proof_of_split_words_entail_wit_9_2 : split_words_entail_wit_9_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_3_2.
  replace i with n in * by lia.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((n - start) + 1)).
  replace (word_payload_125 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia;
        symmetry; apply word_payload_125_empty_manual).
  rewrite CharArray.full_empty.
  unfold store_string.
  entailer!;
  try solve [assumption | lia].
  - apply Zlength_word_payload_125; unfold string_length in *; lia.
  - unfold split_scan_state_125 in PreH28.
    destruct PreH28 as [Hrange [Hrows Hcur]].
    destruct Hcur as [[Hempty Hbad] | [Hstart Hcur]];
      [lia | exact Hcur].
Qed.

Lemma proof_of_split_words_entail_wit_10_1 : split_words_entail_wit_10_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [assumption | lia].
  rewrite word_payload_125_step_offset_c_string by (unfold string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_split_words_entail_wit_10_2 : split_words_entail_wit_10_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_3_2.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [assumption | lia].
  rewrite word_payload_125_step_offset_c_string by (unfold string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_split_words_entail_wit_11_1 : split_words_entail_wit_11_1.
Proof.
  pre_process_default.
  assert (Hi : i = n) by lia.
  assert (Hs : start = -1) by lia.
  subst i start.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [assumption | apply problem_125_spec_z_any | lia].
  unfold string_length in *.
  rewrite PreH5 in PreH26.
  apply split_scan_state_125_final_empty.
  exact PreH26.
Qed.

Lemma proof_of_split_words_entail_wit_11_2 : split_words_entail_wit_11_2.
Proof.
  pre_process_default.
  assert (Hi : i = n) by lia.
  assert (Hs : start = -1) by lia.
  subst i start.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_3.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [assumption | apply problem_125_spec_z_any | lia].
  unfold string_length in *.
  rewrite PreH5 in PreH27.
  apply split_scan_state_125_final_empty.
  exact PreH27.
Qed.

Lemma proof_of_split_words_entail_wit_11_3 : split_words_entail_wit_11_3.
Proof.
  pre_process_default.
  assert (Hk : k = len) by lia.
  subst k.
  assert (Hstop : start + len = n) by lia.
  replace (word_payload_125 str_l start (start + len) ++ 0 :: nil)
    with (word_row_125 str_l start n).
  2:{
    rewrite Hstop.
    unfold word_row_125, c_string.
    reflexivity.
  }
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  Exists (output_ptrs_2 ++ cons w nil)
    (output_rows_2 ++ cons (word_row_125 str_l start n) nil).
  replace (len + 1) with (Zlength (word_row_125 str_l start n)).
  2:{
    rewrite word_row_125_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_word_payload_125 by (unfold string_length in *; lia).
    lia.
  }
  sep_apply (split_words_rows_heap_125_app_single output_ptrs_2 output_rows_2 w
    (word_row_125 str_l start n) ltac:(lia)).
  unfold store_string.
  entailer!;
  try solve [
    assumption
  | apply problem_125_spec_z_any
  | rewrite Zlength_app, !Zlength_cons, !Zlength_nil; lia
  ].
  unfold string_length in *.
  rewrite PreH4 in PreH27.
  rewrite PreH4.
  apply split_scan_state_125_final_nonempty; try lia.
  exact PreH27.
Qed.

Lemma proof_of_split_words_entail_wit_11_4 : split_words_entail_wit_11_4.
Proof.
  pre_process_default.
  assert (Hk : k = len) by lia.
  subst k.
  assert (Hstop : start + len = n) by lia.
  replace (word_payload_125 str_l start (start + len) ++ 0 :: nil)
    with (word_row_125 str_l start n).
  2:{
    rewrite Hstop.
    unfold word_row_125, c_string.
    reflexivity.
  }
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_3.
  Exists (output_ptrs_2 ++ cons w nil)
    (output_rows_2 ++ cons (word_row_125 str_l start n) nil).
  replace (len + 1) with (Zlength (word_row_125 str_l start n)).
  2:{
    rewrite word_row_125_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_word_payload_125 by (unfold string_length in *; lia).
    lia.
  }
  sep_apply (split_words_rows_heap_125_app_single output_ptrs_2 output_rows_2 w
    (word_row_125 str_l start n) ltac:(lia)).
  unfold store_string.
  entailer!;
  try solve [
    assumption
  | apply problem_125_spec_z_any
  | rewrite Zlength_app, !Zlength_cons, !Zlength_nil; lia
  ].
  unfold string_length in *.
  rewrite PreH4 in PreH28.
  rewrite PreH4.
  apply split_scan_state_125_final_nonempty; try lia.
  exact PreH28.
Qed.

Lemma proof_of_split_words_entail_wit_12_split_goal_1 : split_words_entail_wit_12_split_goal_1.
Proof. Abort.

Lemma proof_of_split_words_entail_wit_12_split_goal_2 : split_words_entail_wit_12_split_goal_2.
Proof. Abort.

Lemma proof_of_split_words_entail_wit_12_split_goal_3 : split_words_entail_wit_12_split_goal_3.
Proof. Abort.

Lemma proof_of_split_words_entail_wit_12_split_goal_4 : split_words_entail_wit_12_split_goal_4.
Proof. Abort.

Lemma proof_of_split_words_entail_wit_12_split_goal_spatial : split_words_entail_wit_12_split_goal_spatial.
Proof. Abort.

Lemma proof_of_split_words_entail_wit_12 : split_words_entail_wit_12.
Proof.
  left.
  pre_process_default.
  unfold store_string.
  entailer!;
  try solve [
    assumption
  | solve_contains_zb_125
  | unfold odd_lower_prefix_125, odd_lower_count_125;
    rewrite sublist_nil by lia; reflexivity
  | pose proof (string_length_nonneg str_l); lia
  ].
Qed.

Lemma proof_of_split_words_entail_wit_13_1_split_goal_1 : split_words_entail_wit_13_1_split_goal_1.
Proof. Abort.

Lemma proof_of_split_words_entail_wit_13_1_split_goal_spatial : split_words_entail_wit_13_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_split_words_entail_wit_13_1 : split_words_entail_wit_13_1.
Proof.
  left.
  pre_process_default.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125;
        [match goal with H : all_ascii str_l |- _ => exact H end
        | unfold string_length in *; lia]).
  entailer!;
  try solve [assumption | lia].
  rewrite PreH10.
  symmetry.
  apply odd_lower_prefix_125_step_hit.
  - unfold string_length in *; lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    exact PreH1.
Qed.

Lemma proof_of_split_words_entail_wit_13_2_split_goal_1 : split_words_entail_wit_13_2_split_goal_1.
Proof. Abort.

Lemma proof_of_split_words_entail_wit_13_2_split_goal_spatial : split_words_entail_wit_13_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_split_words_entail_wit_13_2 : split_words_entail_wit_13_2.
Proof.
  left.
  pre_process_default.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125;
        [match goal with H : all_ascii str_l |- _ => exact H end
        | unfold string_length in *; lia]).
  entailer!;
  try solve [assumption | lia].
  rewrite PreH9.
  symmetry.
  apply odd_lower_prefix_125_step_high.
  - unfold string_length in *; lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    lia.
Qed.

Lemma proof_of_split_words_entail_wit_13_3_split_goal_1 : split_words_entail_wit_13_3_split_goal_1.
Proof. Abort.

Lemma proof_of_split_words_entail_wit_13_3_split_goal_spatial : split_words_entail_wit_13_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_split_words_entail_wit_13_3 : split_words_entail_wit_13_3.
Proof.
  left.
  pre_process_default.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125;
        [match goal with H : all_ascii str_l |- _ => exact H end
        | unfold string_length in *; lia]).
  entailer!;
  try solve [assumption | lia].
  rewrite PreH8.
  symmetry.
  apply odd_lower_prefix_125_step_low.
  - unfold string_length in *; lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    lia.
Qed.

Lemma proof_of_split_words_entail_wit_13_4_split_goal_1 : split_words_entail_wit_13_4_split_goal_1.
Proof. Abort.

Lemma proof_of_split_words_entail_wit_13_4_split_goal_spatial : split_words_entail_wit_13_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_split_words_entail_wit_13_4 : split_words_entail_wit_13_4.
Proof.
  left.
  pre_process_default.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125;
        [match goal with H : all_ascii str_l |- _ => exact H end
        | unfold string_length in *; lia]).
  entailer!;
  try solve [assumption | lia].
  rewrite PreH10.
  symmetry.
  apply odd_lower_prefix_125_step_rem_nonzero.
  - unfold string_length in *; lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    exact PreH1.
Qed.

Lemma proof_of_split_words_entail_wit_14 : split_words_entail_wit_14.
Proof.
  left.
  pre_process_default.
  Exists (cons retval_2 nil) out_l.
  sep_apply_l_atomic (PtrArray.seg_single data 0 retval_2).
  sep_apply_l_atomic (PtrArray.undef_missing_i_to_undef_seg_head data 0 (n + 1) ltac:(lia)).
  unfold store_string.
  entailer!;
  try solve [
    assumption
  | apply problem_125_spec_z_any
  | rewrite !Zlength_cons, !Zlength_nil; lia
  ].
  - replace (0 + 1) with 1 by lia.
    simpl.
    replace (Zlength (c_string out_l)) with (retval + 1) by (
      unfold c_string, string_length;
      rewrite Zlength_app, Zlength_cons, Zlength_nil;
      lia
    ).
    cancel.
    entailer!.
  - unfold string_length in *.
    rewrite PreH13.
    apply odd_lower_prefix_125_final.
    lia.
Qed.

Lemma proof_of_split_words_return_wit_1 : split_words_return_wit_1.
Proof.
  left.
  pre_process_default.
  subst output_ptrs_2 n.
  Exists (cons (c_string digit_l) nil) (cons w nil) data_2.
  rewrite !Zlength_cons, !Zlength_nil.
  entailer!;
  try solve [assumption | pose proof (string_length_nonneg str_l); lia].
Qed.

Lemma proof_of_split_words_return_wit_3 : split_words_return_wit_3.
Proof.
  left.
  pre_process_default.
  subst n.
  rewrite PreH8.
  Exists output_rows_2 output_ptrs_2 data_2.
  entailer!;
  try solve [
    assumption
  | pose proof (string_length_nonneg str_l); lia
  | subst output_rows_2; apply Zlength_split_output_rows_125_le
  | match goal with
    | H : output_rows_2 = split_output_rows_125 str_l _ |- _ =>
        rewrite H; apply Zlength_split_output_rows_125_le
    end].
Qed.

Lemma proof_of_split_words_return_wit_4 : split_words_return_wit_4.
Proof.
  left.
  pre_process_default.
  subst n.
  rewrite PreH8.
  Exists output_rows_2 output_ptrs_2 data_2.
  entailer!;
  try solve [
    assumption
  | pose proof (string_length_nonneg str_l); lia
  | subst output_rows_2; apply Zlength_split_output_rows_125_le
  | match goal with
    | H : output_rows_2 = split_output_rows_125 str_l _ |- _ =>
        rewrite H; apply Zlength_split_output_rows_125_le
    end].
Qed.
