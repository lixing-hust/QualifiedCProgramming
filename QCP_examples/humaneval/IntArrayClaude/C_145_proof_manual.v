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
From SimpleC.EE Require Import C_145_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_145.
Local Open Scope sac.

Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof. pre_process. Qed.

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof. pre_process. Qed.

Lemma proof_of_signed_digit_score_safety_wit_22 : signed_digit_score_safety_wit_22.
Proof.
  pre_process.
  entailer!.
  - rewrite Z.rem_mod_nonneg by lia.
    pose proof (Z.mod_pos_bound t 10 ltac:(lia)).
    lia.
  - rewrite Z.rem_mod_nonneg by lia.
    pose proof (Z.mod_pos_bound t 10 ltac:(lia)).
    lia.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_1 : signed_digit_score_entail_wit_1.
Proof.
  pre_process.
  subst retval.
  entailer!.
  apply first_digit_state_145_init.
  unfold Zabs in *.
  split; [apply Z.abs_nonneg|assumption].
Qed.

Lemma proof_of_signed_digit_score_entail_wit_2 : signed_digit_score_entail_wit_2.
Proof.
  pre_process.
  unfold Zabs in *.
  match goal with
  | Hs: first_digit_state_145 (Z.abs x_pre) t |- _ =>
      pose proof (first_digit_state_145_step (Z.abs x_pre) t Hs ltac:(lia)) as Hnext
  end.
  entailer!.
  - rewrite Z.quot_div_nonneg by lia.
    assert (t / 10 <= t).
    { apply Z.div_le_upper_bound; lia. }
    lia.
  - rewrite Z.quot_div_nonneg by lia.
    apply Z.div_pos; lia.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_3_1 : signed_digit_score_entail_wit_3_1.
Proof.
  pre_process.
  unfold Zabs in *.
  match goal with
  | Hs: first_digit_state_145 (Z.abs x_pre) t |- _ =>
      pose proof (highest_power10_state_init_nonneg
                    x_pre retval t (sum + t)
                    ltac:(lia) ltac:(lia) ltac:(lia)
                    Hs ltac:(lia) ltac:(lia)) as Hnext
  end.
  entailer!.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_3_2 : signed_digit_score_entail_wit_3_2.
Proof.
  pre_process.
  unfold Zabs in *.
  match goal with
  | Hs: first_digit_state_145 (Z.abs x_pre) t |- _ =>
      pose proof (highest_power10_state_init_neg
                    x_pre retval t (sum + - t)
                    ltac:(lia) ltac:(lia) ltac:(lia)
                    Hs ltac:(lia) ltac:(lia)) as Hnext
  end.
  entailer!.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_4 : signed_digit_score_entail_wit_4.
Proof.
  pre_process.
  match goal with
  | Hs: highest_power10_state x_pre t p sum |- _ =>
      pose proof (highest_power10_state_step x_pre t p sum Hs ltac:(lia)) as Hnext
  end.
  entailer!.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_5_1 : signed_digit_score_entail_wit_5_1.
Proof.
  pre_process.
  unfold Zabs in *.
  match goal with
  | Hs: first_digit_state_145 (Z.abs x_pre) t |- _ =>
      pose proof (first_digit_state_145_final (Z.abs x_pre) t Hs ltac:(lia)) as Hfirst
  end.
  rewrite first_digit_value_145_small in Hfirst by lia.
  assert (Ht: t = Z.abs x_pre) by lia.
  assert (Hx: Z.abs x_pre = x_pre) by (apply Z.abs_eq; lia).
  assert (Hsum: sum + t = sum_digits x_pre).
  {
    rewrite Ht, Hx.
    rewrite sum_digits_small_nonneg_145 by lia.
    lia.
  }
  entailer!.
  rewrite Hsum.
  apply signed_digit_tail_state_zero; lia.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_5_2 : signed_digit_score_entail_wit_5_2.
Proof.
  pre_process.
  unfold Zabs in *.
  match goal with
  | Hs: first_digit_state_145 (Z.abs x_pre) t |- _ =>
      pose proof (first_digit_state_145_final (Z.abs x_pre) t Hs ltac:(lia)) as Hfirst
  end.
  rewrite first_digit_value_145_small in Hfirst by lia.
  assert (Ht: t = Z.abs x_pre) by lia.
  assert (Hx: Z.abs x_pre = - x_pre) by (apply Z.abs_neq; lia).
  assert (Hsum: sum + - t = sum_digits x_pre).
  {
    rewrite Ht, Hx.
    rewrite sum_digits_small_neg_145 by lia.
    lia.
  }
  entailer!.
  rewrite Hsum.
  apply signed_digit_tail_state_zero; lia.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_5_3 : signed_digit_score_entail_wit_5_3.
Proof.
  pre_process.
  match goal with
  | Hs: highest_power10_state x_pre t p sum |- _ =>
      pose proof (highest_power10_state_final x_pre t p sum Hs ltac:(lia)) as Htail
  end.
  pose proof (signed_digit_tail_state_bounds _ _ _ Htail) as [Htrem Hsumlo].
  pose proof (signed_digit_tail_state_sum_upper _ _ _ Htail) as Hsumhi.
  entailer!.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_6 : signed_digit_score_entail_wit_6.
Proof.
  pre_process.
  match goal with
  | Hs: signed_digit_tail_state x_pre t sum |- _ =>
      pose proof (signed_digit_tail_state_step x_pre t sum Hs ltac:(lia)) as Hnext
  end.
  pose proof (signed_digit_tail_state_bounds _ _ _ Hnext) as [Htrem Hsumlo].
  pose proof (signed_digit_tail_state_sum_upper _ _ _ Hnext) as Hsumhi.
  entailer!.
Qed.

Lemma proof_of_signed_digit_score_return_wit_1 : signed_digit_score_return_wit_1.
Proof.
  pre_process.
  unfold Zabs in *.
  assert (t = 0) by lia.
  subst t.
  pose proof (signed_digit_tail_state_final x_pre sum ltac:(lia) ltac:(lia) H7) as Hret.
  entailer!.
Qed.

Lemma proof_of_order_by_points_entail_wit_1 : order_by_points_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z) (@nil Z).
  entailer!.
  - sep_apply (IntArray.undef_full_to_undef_seg retval_2 nums_size_pre).
    sep_apply (IntArray.undef_full_to_undef_seg retval_3 nums_size_pre).
    rewrite IntArray.seg_empty.
    rewrite IntArray.seg_empty.
    entailer!.
  - apply order_copy_prefix_init.
Qed.

Lemma proof_of_order_by_points_entail_wit_2 : order_by_points_entail_wit_2.
Proof.
  pre_process.
  Exists (score_l_2 ++ retval :: nil) (output_l_2 ++ Znth i input_l 0 :: nil).
  entailer!.
  - sep_apply (IntArray.seg_single score i retval).
    sep_apply (IntArray.seg_single data i (Znth i input_l 0)).
    sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)); [ | lia].
    sep_apply (IntArray.seg_merge_to_seg score 0 i (i + 1)); [ | lia].
    entailer!.
  - unfold signed_digit_score_result in H.
    destruct H as [_ [_ [_ Hscore_res]]].
    apply order_copy_prefix_step; try assumption; lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_order_by_points_entail_wit_4 : order_by_points_entail_wit_4.
Proof.
  pre_process.
  replace i with nums_size_pre in * by lia.
  Exists score_l_2 output_l_2.
  entailer!.
  - sep_apply (IntArray.seg_to_full data 0 nums_size_pre).
    replace (nums_size_pre - 0) with nums_size_pre by lia.
    rewrite (IntArray.undef_seg_empty data nums_size_pre).
    sep_apply (IntArray.seg_to_full score 0 nums_size_pre).
    replace (nums_size_pre - 0) with nums_size_pre by lia.
    rewrite (IntArray.undef_seg_empty score nums_size_pre).
    replace (data + 0 * sizeof(INT)) with data by lia.
    replace (score + 0 * sizeof(INT)) with score by lia.
    entailer!.
  - apply order_sort_outer_state_init.
    replace (Zlength input_l) with nums_size_pre by lia.
    assumption.
Qed.

Lemma proof_of_order_by_points_entail_wit_5 : order_by_points_entail_wit_5.
Proof.
  pre_process.
  Exists score_l_2 output_l_2.
  entailer!.
  apply order_sort_inner_state_init; try assumption; lia.
Qed.

Lemma proof_of_order_by_points_entail_wit_6 : order_by_points_entail_wit_6.
Proof.
  pre_process.
  replace j with nums_size_pre in * by lia.
  Exists score_l_2 output_l_2.
  entailer!.
  apply order_sort_outer_state_step; try lia.
  replace (Zlength input_l) with nums_size_pre by lia.
  assumption.
Qed.

Lemma proof_of_order_by_points_entail_wit_7_1 : order_by_points_entail_wit_7_1.
Proof.
  pre_process.
  Exists (replace_Znth (j - 1) (Znth j score_l_2 0)
           (replace_Znth j (Znth (j - 1) score_l_2 0) score_l_2))
         (replace_Znth (j - 1) (Znth j output_l_2 0)
           (replace_Znth j (Znth (j - 1) output_l_2 0) output_l_2)).
  entailer!.
  - apply order_sort_inner_state_step_swap; try assumption; lia.
  - repeat rewrite (@replace_Znth_length_145 Z). lia.
  - repeat rewrite (@replace_Znth_length_145 Z). lia.
Qed.

Lemma proof_of_order_by_points_entail_wit_7_2 : order_by_points_entail_wit_7_2.
Proof.
  pre_process.
  Exists score_l_2 output_l_2.
  entailer!.
  apply order_sort_inner_state_step_keep; try assumption; lia.
Qed.

Lemma proof_of_order_by_points_entail_wit_9 : order_by_points_entail_wit_9.
Proof.
  pre_process.
  replace i with nums_size_pre in * by lia.
  Exists score_l_2 output_l_2.
  entailer!.
  apply order_sort_outer_state_final_spec with (scores := score_l_2).
  replace (Zlength input_l) with nums_size_pre by lia.
  assumption.
Qed.

Lemma proof_of_order_by_points_partial_solve_wit_7_pure : order_by_points_partial_solve_wit_7_pure.
Proof.
  pre_process.
  destruct (order_by_points_int_range_at input_l i H7 ltac:(lia)) as [Hrange Habs].
  entailer!.
Qed.
