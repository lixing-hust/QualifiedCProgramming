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
From SimpleC.EE Require Import C_15_goal.
From SimpleC.EE Require Import C_15_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_15.
Local Open Scope sac.

Ltac normalize_num_15 :=
  repeat match goal with
  | |- context[?x ÷ 10] =>
      rewrite (Z.quot_div_nonneg x 10) by lia
  | H : context[?x ÷ 10] |- _ =>
      rewrite (Z.quot_div_nonneg x 10) in H by lia
  | |- context[?x % 10] =>
      rewrite (Z.rem_mod_nonneg x 10) by lia
  | H : context[?x % 10] |- _ =>
      rewrite (Z.rem_mod_nonneg x 10) in H by lia
  end.

Ltac normalize_equalities_15 :=
  repeat match goal with
  | H : ?x = ?x |- _ => clear H
  | H : ?x = ?y |- _ => subst x || subst y
  end.

Ltac solve_pure_step_15 :=
  normalize_num_15;
  match goal with
  | |- decimal_count_state_z ?x ?x 0 =>
      apply decimal_count_state_init_15; lia
  | H : decimal_count_state_z ?orig ?tmp ?digits |- decimal_count_state_z ?orig (?tmp / 10) (?digits + 1) =>
      apply decimal_count_state_step_15; lia || exact H
  | H : decimal_count_state_z ?orig 0 ?digits |- ?digits = Zlength (decimal_digits_z ?orig) =>
      apply decimal_count_state_done_15; lia || exact H
  | H : decimal_count_state_z ?orig 0 ?digits |- 1 <= ?digits =>
      rewrite (decimal_count_state_done_15 orig digits) by (lia || exact H);
      apply decimal_digits_z_length_pos_15
  | H : decimal_count_state_z ?orig ?tmp ?digits |- ?digits + 1 < INT_MAX =>
      eapply decimal_count_state_next_lt_int_15; eauto; lia
  | |- decimal_fill_full_state_z ?orig ?orig (Zlength (decimal_digits_z ?orig))
        (repeat_Z 0 (Zlength (decimal_digits_z ?orig))) =>
      apply decimal_fill_full_state_init_15; lia
  | H : decimal_fill_full_state_z ?orig ?tmp (?fill + 1) ?out_l |-
      decimal_fill_full_state_z ?orig (?tmp / 10) ?fill
        (replace_Znth ?fill (signed_last_nbits (48 + ?tmp mod 10) 8) ?out_l) =>
      apply decimal_fill_full_state_step_15; lia || exact H
  | H : decimal_fill_full_state_z ?orig 0 0 ?out_l |- ?out_l = decimal_digits_z ?orig =>
      apply decimal_fill_full_state_done_15; lia || exact H
  | H : decimal_fill_full_state_z ?orig 0 ?fill ?out_l |- ?out_l = decimal_digits_z ?orig =>
      apply decimal_fill_full_state_zero_done_15; exact H
  | H : decimal_fill_full_state_z ?orig ?tmp ?fill ?out_l |- 1 <= ?fill =>
      eapply decimal_fill_full_state_fill_pos_15; eauto; lia
  | |- repeat_Z 0 0 = @nil Z =>
      reflexivity
  | |- app (repeat_Z 0 ?i) (cons 0 (@nil Z)) = repeat_Z 0 (?i + 1) =>
      rewrite repeat_Z_tail by lia; reflexivity
  | |- Zlength (string_sequence_prefix_z 1) = 1 =>
      apply string_sequence_prefix_one_len_15
  | |- 1 <= sequence_len_z ?n =>
      apply sequence_len_pos_15; lia
  | |- Zlength (string_sequence_prefix_z ?i) + 1 + Zlength (decimal_digits_z ?i) <= sequence_len_z ?n =>
      apply string_sequence_next_len_le_15; lia
  | |- Zlength (string_sequence_prefix_z ?i) <= sequence_len_z ?n =>
      unfold sequence_len_z; apply string_sequence_prefix_len_le_15; lia
  | |- ?k + ?len = Zlength (string_sequence_prefix_z (?i + 1)) =>
      rewrite string_sequence_prefix_succ_len_15 by lia;
      rewrite sequence_piece_pos_len_15 by lia; lia
  | |- ?k + 1 + ?len = Zlength (string_sequence_prefix_z (?i + 1)) =>
      rewrite string_sequence_prefix_succ_len_15 by lia;
      rewrite sequence_piece_pos_len_15 by lia; lia
  | |- problem_15_spec_z ?n (string_sequence_prefix_z (?n + 1)) =>
      apply problem_15_spec_z_sequence_prefix_15; lia
  | |- 48 + ?x mod 10 <= INT_MAX =>
      pose proof (Z.mod_pos_bound x 10 ltac:(lia)); lia
  | |- INT_MIN <= 48 + ?x mod 10 =>
      pose proof (Z.mod_pos_bound x 10 ltac:(lia)); lia
  | |- _ => lia
  end.

Ltac solve_15_core :=
  pre_process;
  normalize_equalities_15;
  repeat normalize_num_15;
  try match goal with
  | |- context[CharArray.undef_seg ?b (0 + 1) 1] =>
      rewrite (CharArray.undef_seg_empty b 1);
      rewrite <- (CharArray.seg_single b 0 48);
      cancel ((b + 0 * sizeof(CHAR)) # Char |-> 48);
      entailer!
  end;
  try match goal with
  | |- ((?out + 0 * sizeof(CHAR)) # Char |-> 48) |--
       CharArray.full ?out 1 (string_sequence_prefix_z 1) =>
      rewrite string_sequence_prefix_one_15;
      unfold CharArray.full, CharArray.seg;
      rewrite <- (CharArray.seg_single out 0 48);
      entailer!
  end;
  try match goal with
  | Hge : ?i >= ?d, Hle : ?i <= ?d |- _ |-- EX _ : list Z, _ =>
      assert (i = d) by lia; subst i; Exists (repeat_Z 0 d)
  end;
  try entailer!;
  repeat solve_pure_step_15;
  try entailer!;
  repeat solve_pure_step_15.

Ltac solve_15 :=
  first [right; solve_15_core | left; solve_15_core | solve_15_core].

Lemma proof_of_decimal_len_entail_wit_1_split_goal_1 : decimal_len_entail_wit_1_split_goal_1.
Proof. solve_15. Qed.

Lemma proof_of_decimal_len_entail_wit_1 : decimal_len_entail_wit_1.
Proof. solve_15. Qed.
Lemma proof_of_decimal_len_entail_wit_2_split_goal_1 : decimal_len_entail_wit_2_split_goal_1.
Proof. solve_15. Qed.

Lemma proof_of_decimal_len_entail_wit_2_split_goal_2 : decimal_len_entail_wit_2_split_goal_2.
Proof.
  pre_process; entailer!.
  normalize_num_15.
  eapply decimal_count_state_next_lt_int_15 with (orig := value_pre) (t := tmp);
    eauto; lia.
Qed.

Lemma proof_of_decimal_len_entail_wit_2_split_goal_3 : decimal_len_entail_wit_2_split_goal_3.
Proof.
  pre_process; entailer!.
  normalize_num_15.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_decimal_len_entail_wit_2 : decimal_len_entail_wit_2.
Proof.
  right.
  pre_process; entailer!; normalize_num_15.
  - apply Z.div_pos; lia.
  - eapply decimal_count_state_next_lt_int_15 with (orig := value_pre) (t := tmp);
      eauto; lia.
  - apply decimal_count_state_step_15; lia || assumption.
Qed.
Lemma proof_of_decimal_len_return_wit_1_split_goal_1 : decimal_len_return_wit_1_split_goal_1.
Proof.
  pre_process; entailer!.
  assert (tmp = 0) by lia; subst tmp.
  rewrite (decimal_count_state_done_15 value_pre digits) by (lia || assumption).
  apply decimal_digits_z_length_pos_15.
Qed.

Lemma proof_of_decimal_len_return_wit_1_split_goal_2 : decimal_len_return_wit_1_split_goal_2.
Proof.
  pre_process; entailer!.
  assert (tmp = 0) by lia; subst tmp.
  apply decimal_count_state_done_15; lia || assumption.
Qed.

Lemma proof_of_decimal_len_return_wit_1 : decimal_len_return_wit_1.
Proof.
  right.
  pre_process; entailer!.
  - assert (tmp = 0) by lia; subst tmp.
    apply decimal_count_state_done_15; lia || assumption.
  - assert (tmp = 0) by lia; subst tmp.
    rewrite (decimal_count_state_done_15 value_pre digits) by (lia || assumption).
    apply decimal_digits_z_length_pos_15.
Qed.
Lemma proof_of_decimal_len_return_wit_2_split_goal_1 : decimal_len_return_wit_2_split_goal_1.
Proof. solve_15. Qed.

Lemma proof_of_decimal_len_return_wit_2 : decimal_len_return_wit_2.
Proof. solve_15. Qed.
Lemma proof_of_write_decimal_safety_wit_11_split_goal_1 : write_decimal_safety_wit_11_split_goal_1.
Proof. solve_15. Qed.

Lemma proof_of_write_decimal_safety_wit_11_split_goal_2 : write_decimal_safety_wit_11_split_goal_2.
Proof. solve_15. Qed.

Lemma proof_of_write_decimal_safety_wit_11 : write_decimal_safety_wit_11.
Proof. solve_15. Qed.
Lemma proof_of_write_decimal_entail_wit_1_split_goal_1 : write_decimal_entail_wit_1_split_goal_1.
Proof. solve_15. Qed.

Lemma proof_of_write_decimal_entail_wit_1_split_goal_spatial : write_decimal_entail_wit_1_split_goal_spatial.
Proof. solve_15. Qed.

Lemma proof_of_write_decimal_entail_wit_1 : write_decimal_entail_wit_1.
Proof. solve_15. Qed.
Lemma proof_of_write_decimal_entail_wit_2_split_goal_1 : write_decimal_entail_wit_2_split_goal_1.
Proof. solve_15. Qed.

Lemma proof_of_write_decimal_entail_wit_2 : write_decimal_entail_wit_2.
Proof. solve_15. Qed.
Lemma proof_of_write_decimal_entail_wit_3 : write_decimal_entail_wit_3.
Proof.
  right.
  pre_process.
  assert (i = digits_pre) by lia; subst i.
  Exists (repeat_Z 0 digits_pre).
  entailer!.
  - subst tmp fill.
    rewrite PreH4.
    apply decimal_fill_full_state_init_15; lia.
  - rewrite Zlength_repeat_Z; lia.
Qed.
Lemma proof_of_write_decimal_entail_wit_5_split_goal_1 : write_decimal_entail_wit_5_split_goal_1.
Proof.
  pre_process; entailer!.
  replace (fill - 1 + 1) with fill by lia.
  assumption.
Qed.

Lemma proof_of_write_decimal_entail_wit_5_split_goal_2 : write_decimal_entail_wit_5_split_goal_2.
Proof.
  pre_process; entailer!.
  pose proof (decimal_fill_full_state_fill_pos_15 value_pre tmp fill out_l_2 ltac:(lia) PreH12).
  lia.
Qed.

Lemma proof_of_write_decimal_entail_wit_5 : write_decimal_entail_wit_5.
Proof.
  right.
  pre_process; entailer!.
  - pose proof (decimal_fill_full_state_fill_pos_15 value_pre tmp fill out_l_2 ltac:(lia) PreH12).
    lia.
  - replace (fill - 1 + 1) with fill by lia.
    assumption.
Qed.
Lemma proof_of_write_decimal_entail_wit_6_split_goal_1 : write_decimal_entail_wit_6_split_goal_1.
Proof. solve_15. Qed.

Lemma proof_of_write_decimal_entail_wit_6_split_goal_2 : write_decimal_entail_wit_6_split_goal_2.
Proof.
  pre_process; entailer!.
  rewrite Zlength_replace_Znth.
  assumption.
Qed.

Lemma proof_of_write_decimal_entail_wit_6_split_goal_3 : write_decimal_entail_wit_6_split_goal_3.
Proof.
  pre_process; entailer!.
  normalize_num_15.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_write_decimal_entail_wit_6 : write_decimal_entail_wit_6.
Proof.
  right.
  pre_process.
  entailer!; normalize_num_15.
  - apply Z.div_pos; lia.
  - rewrite Zlength_replace_Znth. assumption.
  - apply decimal_fill_full_state_step_15; lia || assumption.
Qed.
Lemma proof_of_write_decimal_return_wit_1_split_goal_spatial : write_decimal_return_wit_1_split_goal_spatial.
Proof.
  pre_process.
  subst value_pre.
  assert (digits_pre = 1).
  { rewrite PreH4. rewrite decimal_digits_z_zero_15. reflexivity. }
  subst digits_pre.
  rewrite decimal_digits_z_zero_15.
  rewrite (CharArray.undef_seg_empty buf_pre 1).
  unfold CharArray.full, CharArray.seg.
  rewrite <- (CharArray.seg_single buf_pre 0 48).
  entailer!.
Qed.

Lemma proof_of_write_decimal_return_wit_1 : write_decimal_return_wit_1.
Proof.
  right.
  pre_process.
  subst value_pre.
  assert (digits_pre = 1).
  { rewrite PreH4. rewrite decimal_digits_z_zero_15. reflexivity. }
  subst digits_pre.
  rewrite decimal_digits_z_zero_15.
  rewrite (CharArray.undef_seg_empty buf_pre 1).
  unfold CharArray.full, CharArray.seg.
  rewrite <- (CharArray.seg_single buf_pre 0 48).
  entailer!.
Qed.
Lemma proof_of_write_decimal_return_wit_2_split_goal_1 : write_decimal_return_wit_2_split_goal_1.
Proof.
  pre_process; entailer!.
  assert (tmp = 0) by lia; subst tmp.
  exact (decimal_fill_full_state_zero_done_15 value_pre fill out_l PreH12).
Qed.

Lemma proof_of_write_decimal_return_wit_2 : write_decimal_return_wit_2.
Proof.
  right.
  pre_process; entailer!.
  assert (tmp = 0) by lia; subst tmp.
  exact (decimal_fill_full_state_zero_done_15 value_pre fill out_l PreH12).
Qed.
Lemma proof_of_string_sequence_safety_wit_6_split_goal_1 : string_sequence_safety_wit_6_split_goal_1.
Proof.
  pre_process; entailer!.
  subst retval total.
  pose proof (string_sequence_next_len_le_15 n_pre i ltac:(lia) ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_string_sequence_safety_wit_6_split_goal_2 : string_sequence_safety_wit_6_split_goal_2.
Proof.
  pre_process; entailer!.
  subst retval total.
  pose proof (Zlength_nonneg (string_sequence_prefix_z i)).
  pose proof (decimal_digits_z_length_pos_15 i).
  lia.
Qed.

Lemma proof_of_string_sequence_safety_wit_6 : string_sequence_safety_wit_6.
Proof.
  right.
  pre_process; entailer!.
  - subst retval total.
    pose proof (Zlength_nonneg (string_sequence_prefix_z i)).
    pose proof (decimal_digits_z_length_pos_15 i).
    lia.
  - subst retval total.
    pose proof (string_sequence_next_len_le_15 n_pre i ltac:(lia) ltac:(lia) ltac:(lia)).
    lia.
Qed.
Lemma proof_of_string_sequence_safety_wit_20_split_goal_1 : string_sequence_safety_wit_20_split_goal_1.
Proof.
  pre_process; entailer!.
  subst k len out_l total.
  pose proof (string_sequence_next_len_le_15 n_pre i ltac:(lia) ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_string_sequence_safety_wit_20_split_goal_2 : string_sequence_safety_wit_20_split_goal_2.
Proof.
  pre_process; entailer!.
Qed.

Lemma proof_of_string_sequence_safety_wit_20 : string_sequence_safety_wit_20.
Proof.
  right.
  pre_process; entailer!.
  - subst k len out_l total.
    pose proof (string_sequence_next_len_le_15 n_pre i ltac:(lia) ltac:(lia) ltac:(lia)).
    lia.
Qed.
Lemma proof_of_string_sequence_entail_wit_1_split_goal_1 : string_sequence_entail_wit_1_split_goal_1.
Proof. solve_15. Qed.

Lemma proof_of_string_sequence_entail_wit_1_split_goal_2 : string_sequence_entail_wit_1_split_goal_2.
Proof. solve_15. Qed.

Lemma proof_of_string_sequence_entail_wit_1 : string_sequence_entail_wit_1.
Proof. solve_15. Qed.
Lemma proof_of_string_sequence_entail_wit_2_split_goal_1 : string_sequence_entail_wit_2_split_goal_1.
Proof. solve_15. Qed.

Lemma proof_of_string_sequence_entail_wit_2_split_goal_2 : string_sequence_entail_wit_2_split_goal_2.
Proof. solve_15. Qed.

Lemma proof_of_string_sequence_entail_wit_2 : string_sequence_entail_wit_2.
Proof. solve_15. Qed.
Lemma proof_of_string_sequence_entail_wit_3_split_goal_1 : string_sequence_entail_wit_3_split_goal_1.
Proof.
  pre_process; entailer!.
  assert (i = n_pre + 1) by lia; subst i.
  subst total.
  unfold sequence_len_z.
  apply Zlength_nonneg.
Qed.

Lemma proof_of_string_sequence_entail_wit_3_split_goal_2 : string_sequence_entail_wit_3_split_goal_2.
Proof.
  pre_process; entailer!.
  assert (i = n_pre + 1) by lia; subst i.
  subst total.
  unfold sequence_len_z.
  reflexivity.
Qed.

Lemma proof_of_string_sequence_entail_wit_3_split_goal_spatial : string_sequence_entail_wit_3_split_goal_spatial.
Proof. solve_15. Qed.

Lemma proof_of_string_sequence_entail_wit_3 : string_sequence_entail_wit_3.
Proof.
  right.
  pre_process; entailer!.
  - assert (i = n_pre + 1) by lia; subst i.
    subst total. unfold sequence_len_z. reflexivity.
  - assert (i = n_pre + 1) by lia; subst i.
    subst total. unfold sequence_len_z. apply Zlength_nonneg.
Qed.
Lemma proof_of_string_sequence_entail_wit_4_split_goal_1 : string_sequence_entail_wit_4_split_goal_1.
Proof. solve_15. Qed.

Lemma proof_of_string_sequence_entail_wit_4_split_goal_2 : string_sequence_entail_wit_4_split_goal_2.
Proof. solve_15. Qed.

Lemma proof_of_string_sequence_entail_wit_4_split_goal_spatial : string_sequence_entail_wit_4_split_goal_spatial.
Proof. solve_15. Qed.

Lemma proof_of_string_sequence_entail_wit_4 : string_sequence_entail_wit_4.
Proof.
  right.
  pre_process; entailer!.
  - rewrite string_sequence_prefix_one_15.
    unfold CharArray.full, CharArray.seg.
    rewrite <- (CharArray.seg_single out 0 48).
    entailer!.
  - subst total. apply sequence_len_pos_15; lia.
Qed.
Lemma proof_of_string_sequence_entail_wit_5_split_goal_spatial : string_sequence_entail_wit_5_split_goal_spatial.
Proof.
  pre_process.
  assert (Hnext:
    k + 1 + retval <= total + 1).
  {
    rewrite PreH1, PreH10, PreH15, PreH16.
    eapply Z.le_trans with (m := sequence_len_z n_pre).
    - apply string_sequence_next_len_le_15; lia.
    - lia.
  }
  sep_apply (CharArray.undef_seg_split_to_undef_seg
    out (k + 1) ((k + 1) + retval) (total + 1)); try lia.
  sep_apply CharArray.undef_seg_to_undef_full.
  replace (((k + 1) + retval) - (k + 1)) with retval by lia.
  entailer!.
Qed.

Lemma proof_of_string_sequence_entail_wit_5 : string_sequence_entail_wit_5.
Proof.
  right.
  apply proof_of_string_sequence_entail_wit_5_split_goal_spatial.
Qed.
Lemma proof_of_string_sequence_entail_wit_6_split_goal_1 : string_sequence_entail_wit_6_split_goal_1.
Proof. solve_15. Qed.

Lemma proof_of_string_sequence_entail_wit_6_split_goal_spatial : string_sequence_entail_wit_6_split_goal_spatial.
Proof.
  pre_process.
  replace (string_sequence_prefix_z (i + 1)) with
    (app (app out_l_2 (cons 32 (@nil Z))) (decimal_digits_z i)).
  2:{
    rewrite PreH14.
    rewrite string_sequence_prefix_succ_15 by lia.
    rewrite sequence_piece_pos_15 by lia.
    rewrite app_assoc.
    reflexivity.
  }
  replace len with ((k + len) - k) at 1 by lia.
  sep_apply (CharArray.full_merge_to_full out k (k + len)
    (app out_l_2 (cons 32 (@nil Z))) (decimal_digits_z i)); try lia.
  entailer!.
Qed.

Lemma proof_of_string_sequence_entail_wit_6 : string_sequence_entail_wit_6.
Proof.
  left.
  pre_process.
  Exists (string_sequence_prefix_z (i + 1)).
  entailer!.
  - replace (string_sequence_prefix_z (i + 1)) with
      (app (app out_l_2 (cons 32 (@nil Z))) (decimal_digits_z i)).
    2:{
      rewrite PreH13.
      rewrite string_sequence_prefix_succ_15 by lia.
      rewrite sequence_piece_pos_15 by lia.
      rewrite app_assoc.
      reflexivity.
    }
    replace len with ((k + len) - k) at 1 by lia.
    sep_apply (CharArray.full_merge_to_full out k (k + len)
      (app out_l_2 (cons 32 (@nil Z))) (decimal_digits_z i)); try lia.
    entailer!.
  - rewrite string_sequence_prefix_succ_len_15 by lia.
    rewrite sequence_piece_pos_len_15 by lia.
    rewrite PreH12, PreH13, PreH9.
    lia.
Qed.
Lemma proof_of_string_sequence_entail_wit_7_split_goal_1 : string_sequence_entail_wit_7_split_goal_1.
Proof. solve_15. Qed.

Lemma proof_of_string_sequence_entail_wit_7_split_goal_2 : string_sequence_entail_wit_7_split_goal_2.
Proof.
  pre_process; entailer!.
  subst k.
  apply Zlength_nonneg.
Qed.

Lemma proof_of_string_sequence_entail_wit_7 : string_sequence_entail_wit_7.
Proof.
  left.
  pre_process.
  Exists out_l_2.
  entailer!.
  - rewrite PreH5, PreH8, PreH9.
    unfold sequence_len_z.
    apply string_sequence_prefix_len_le_15; lia.
  - subst k.
    apply Zlength_nonneg.
Qed.
Lemma proof_of_string_sequence_return_wit_1 : string_sequence_return_wit_1.
Proof.
  right.
  pre_process.
  assert (Hi : i = n_pre + 1) by lia; subst i.
  assert (Hk_total : k = total).
  {
    rewrite PreH12, PreH13, PreH7.
    unfold sequence_len_z.
    reflexivity.
  }
  Exists out_l_2.
  entailer!.
  - rewrite Hk_total.
    rewrite CharArray.undef_seg_empty.
    replace total with (Zlength out_l_2) by lia.
    entailer!.
  - rewrite PreH13.
    apply problem_15_spec_z_sequence_prefix_15; lia.
Qed.
Lemma proof_of_string_sequence_partial_solve_wit_2_pure_split_goal_1 : string_sequence_partial_solve_wit_2_pure_split_goal_1.
Proof.
  pre_process; entailer!.
  rewrite PreH18.
  pose proof (Zlength_nonneg (string_sequence_prefix_z i)).
  lia.
Qed.

Lemma proof_of_string_sequence_partial_solve_wit_2_pure : string_sequence_partial_solve_wit_2_pure.
Proof.
  right.
  pre_process; entailer!.
  rewrite PreH18.
  pose proof (Zlength_nonneg (string_sequence_prefix_z i)).
  lia.
Qed.
