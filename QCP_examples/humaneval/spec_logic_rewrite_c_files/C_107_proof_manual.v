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
From SimpleC.EE Require Import C_107_goal.
From SimpleC.EE Require Import C_107_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_107.
Local Open Scope sac.

Lemma rem2_nonneg_cases_107 : forall i,
  0 < i ->
  i % 2 = 0 \/ i % 2 = 1.
Proof.
  intros i Hi.
  pose proof (Z.rem_bound_pos i 2 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma zeven_rem0_107 : forall i,
  i % 2 = 0 ->
  Z.even i = true.
Proof.
  intros i Hrem.
  apply Z.even_spec.
  exists (i ÷ 2).
  pose proof (Z.quot_rem' i 2) as Hqr.
  rewrite Hrem in Hqr.
  lia.
Qed.

Lemma zeven_rem1_107 : forall i,
  i % 2 = 1 ->
  Z.even i = false.
Proof.
  intros i Hrem.
  destruct (Z.even i) eqn:Heven; [| reflexivity].
  apply Z.even_spec in Heven.
  destruct Heven as [k Hk].
  subst i.
  replace (2 * k) with (k * 2) in Hrem by lia.
  rewrite Z.rem_mul in Hrem by lia.
  discriminate.
Qed.

Lemma is_pal_result_nonzero_107 : forall i retval,
  retval <> 0 ->
  retval = is_pal_result_107 i ->
  is_pal_bool_107 i = true.
Proof.
  intros i retval Hnz Hret.
  unfold is_pal_bool_107, is_pal_result_107 in *.
  destruct (Z.eqb (reverse_digits_value_107 i) i); subst; cbn; try lia.
Qed.

Lemma is_pal_result_zero_107 : forall i retval,
  retval = 0 ->
  retval = is_pal_result_107 i ->
  is_pal_bool_107 i = false.
Proof.
  intros i retval Hz Hret.
  unfold is_pal_bool_107, is_pal_result_107 in *.
  destruct (Z.eqb (reverse_digits_value_107 i) i); subst; cbn; try lia.
Qed.

Lemma odd_prefix_step_pal_107 : forall i num1 retval,
  1 <= i ->
  retval <> 0 ->
  retval = is_pal_result_107 i ->
  i % 2 = 1 ->
  num1 = count_odd_pal_prefix_107 (i - 1) ->
  num1 + 1 = count_odd_pal_prefix_107 i.
Proof.
  intros i num1 retval Hi Hnz Hret Hrem Hnum.
  replace (count_odd_pal_prefix_107 i)
    with (count_odd_pal_prefix_107 ((i - 1) + 1)) by (f_equal; lia).
  rewrite count_odd_pal_prefix_step_107 by lia.
  rewrite <- Hnum.
  replace ((i - 1) + 1) with i by lia.
  unfold odd_pal_term_107.
  rewrite (is_pal_result_nonzero_107 i retval Hnz Hret).
  rewrite (zeven_rem1_107 i Hrem).
  cbn. lia.
Qed.

Lemma odd_prefix_step_skip_107 : forall i num1 retval,
  1 <= i ->
  (retval = 0 \/ i % 2 <> 1) ->
  retval = is_pal_result_107 i ->
  num1 = count_odd_pal_prefix_107 (i - 1) ->
  num1 = count_odd_pal_prefix_107 i.
Proof.
  intros i num1 retval Hi Hskip Hret Hnum.
  replace (count_odd_pal_prefix_107 i)
    with (count_odd_pal_prefix_107 ((i - 1) + 1)) by (f_equal; lia).
  rewrite count_odd_pal_prefix_step_107 by lia.
  rewrite <- Hnum.
  replace ((i - 1) + 1) with i by lia.
  unfold odd_pal_term_107.
  destruct Hskip as [Hz | Hrem].
  - rewrite (is_pal_result_zero_107 i retval Hz Hret). cbn. lia.
  - destruct (rem2_nonneg_cases_107 i ltac:(lia)) as [H0 | H1]; [| contradiction].
    rewrite (zeven_rem0_107 i H0). destruct (is_pal_bool_107 i); cbn; lia.
Qed.

Lemma even_prefix_step_pal_107 : forall i num2 retval,
  1 <= i ->
  retval <> 0 ->
  retval = is_pal_result_107 i ->
  i % 2 = 0 ->
  num2 = count_even_pal_prefix_107 (i - 1) ->
  num2 + 1 = count_even_pal_prefix_107 i.
Proof.
  intros i num2 retval Hi Hnz Hret Hrem Hnum.
  replace (count_even_pal_prefix_107 i)
    with (count_even_pal_prefix_107 ((i - 1) + 1)) by (f_equal; lia).
  rewrite count_even_pal_prefix_step_107 by lia.
  rewrite <- Hnum.
  replace ((i - 1) + 1) with i by lia.
  unfold even_pal_term_107.
  rewrite (is_pal_result_nonzero_107 i retval Hnz Hret).
  rewrite (zeven_rem0_107 i Hrem).
  cbn. lia.
Qed.

Lemma even_prefix_step_skip_107 : forall i num2 retval,
  1 <= i ->
  (retval = 0 \/ i % 2 <> 0) ->
  retval = is_pal_result_107 i ->
  num2 = count_even_pal_prefix_107 (i - 1) ->
  num2 = count_even_pal_prefix_107 i.
Proof.
  intros i num2 retval Hi Hskip Hret Hnum.
  replace (count_even_pal_prefix_107 i)
    with (count_even_pal_prefix_107 ((i - 1) + 1)) by (f_equal; lia).
  rewrite count_even_pal_prefix_step_107 by lia.
  rewrite <- Hnum.
  replace ((i - 1) + 1) with i by lia.
  unfold even_pal_term_107.
  destruct Hskip as [Hz | Hrem].
  - rewrite (is_pal_result_zero_107 i retval Hz Hret). cbn. lia.
  - destruct (rem2_nonneg_cases_107 i ltac:(lia)) as [H0 | H1]; [contradiction |].
    rewrite (zeven_rem1_107 i H1). destruct (is_pal_bool_107 i); cbn; lia.
Qed.

Lemma proof_of_is_pal_safety_wit_3_split_goal_1 : is_pal_safety_wit_3_split_goal_1.
Proof.
  pre_process; entailer!.
  unfold int_range_107 in *.
  pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_is_pal_safety_wit_3_split_goal_2 : is_pal_safety_wit_3_split_goal_2.
Proof.
  pre_process; entailer!.
  pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_is_pal_safety_wit_3 : is_pal_safety_wit_3.
Proof.
  right. intros. entailer!.
  - unfold int_range_107 in *.
    pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)).
    lia.
  - pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)).
    lia.
Qed.

Lemma proof_of_is_pal_entail_wit_1_split_goal_1 : is_pal_entail_wit_1_split_goal_1.
Proof.
  pre_process; entailer!.
  apply pal_scan_init_107.
  unfold int_range_107 in *; lia.
Qed.

Lemma proof_of_is_pal_entail_wit_1_split_goal_2 : is_pal_entail_wit_1_split_goal_2.
Proof.
  pre_process; entailer!.
  unfold int_range_107 in *; lia.
Qed.

Lemma proof_of_is_pal_entail_wit_1 : is_pal_entail_wit_1.
Proof.
  right. intros. entailer!.
  - unfold int_range_107 in *; lia.
  - apply pal_scan_init_107. unfold int_range_107 in *; lia.
Qed.

Lemma proof_of_is_pal_entail_wit_2_split_goal_1 : is_pal_entail_wit_2_split_goal_1.
Proof.
  intros r t x Ht Hrng Ht0 Htle Hr0 Hrle Hstate.
  entailer!.
  eapply pal_scan_step_quot_107.
  - exact Hstate.
  - lia.
Qed.

Lemma proof_of_is_pal_entail_wit_2_split_goal_2 : is_pal_entail_wit_2_split_goal_2.
Proof.
  intros orig rr tt Ht Hrng Ht0 Htle Hr0 Hrle Hstate.
  entailer!.
  pose proof (pal_scan_step_quot_107 orig tt rr Hstate ltac:(lia)) as Hstep.
  pose proof (pal_scan_state_value_bound_107 orig (tt ÷ 10) (rr * 10 + tt % 10)
    ltac:(unfold int_range_107 in *; lia) Hstep).
  lia.
Qed.

Lemma proof_of_is_pal_entail_wit_2_split_goal_3 : is_pal_entail_wit_2_split_goal_3.
Proof.
  pre_process; entailer!.
  pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_is_pal_entail_wit_2_split_goal_4 : is_pal_entail_wit_2_split_goal_4.
Proof.
  pre_process; entailer!.
  replace (t ÷ 10) with (t / 10) by (symmetry; apply Z.quot_div_nonneg; lia).
  assert (t / 10 <= t) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_is_pal_entail_wit_2_split_goal_5 : is_pal_entail_wit_2_split_goal_5.
Proof.
  pre_process; entailer!.
  replace (t ÷ 10) with (t / 10) by (symmetry; apply Z.quot_div_nonneg; lia).
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_is_pal_entail_wit_2 : is_pal_entail_wit_2.
Proof.
  right. intros. entailer!.
  - replace (t ÷ 10) with (t / 10) by (symmetry; apply Z.quot_div_nonneg; lia).
    apply Z.div_pos; lia.
  - replace (t ÷ 10) with (t / 10) by (symmetry; apply Z.quot_div_nonneg; lia).
    assert (t / 10 <= t) by (apply Z.div_le_upper_bound; lia). lia.
  - pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)). lia.
  - pose proof (pal_scan_step_quot_107 x_pre t r PreH7 ltac:(lia)) as Hstep.
    pose proof (pal_scan_state_value_bound_107 x_pre (t ÷ 10) (r * 10 + t % 10)
      ltac:(unfold int_range_107 in *; lia) Hstep). lia.
  - apply pal_scan_step_quot_107; try exact PreH7; lia.
Qed.

Lemma proof_of_is_pal_return_wit_1_split_goal_1 : is_pal_return_wit_1_split_goal_1.
Proof.
  pre_process; entailer!.
  pose proof (pal_scan_exit_107 x_pre t r PreH8 PreH2) as Hr.
  unfold is_pal_result_107.
  destruct (Z.eqb (reverse_digits_value_107 x_pre) x_pre) eqn:Heq.
  - apply Z.eqb_eq in Heq. lia.
  - reflexivity.
Qed.

Lemma proof_of_is_pal_return_wit_1 : is_pal_return_wit_1.
Proof.
  right. intros. entailer!.
  pose proof (pal_scan_exit_107 x_pre t r PreH8 PreH2) as Hr.
  unfold is_pal_result_107.
  destruct (Z.eqb (reverse_digits_value_107 x_pre) x_pre) eqn:Heq.
  - apply Z.eqb_eq in Heq. lia.
  - reflexivity.
Qed.

Lemma proof_of_is_pal_return_wit_2_split_goal_1 : is_pal_return_wit_2_split_goal_1.
Proof.
  pre_process; entailer!.
  pose proof (pal_scan_exit_107 x_pre t r PreH8 PreH2) as Hr.
  unfold is_pal_result_107.
  destruct (Z.eqb (reverse_digits_value_107 x_pre) x_pre) eqn:Heq.
  - reflexivity.
  - apply Z.eqb_neq in Heq. lia.
Qed.

Lemma proof_of_is_pal_return_wit_2 : is_pal_return_wit_2.
Proof.
  right. intros. entailer!.
  pose proof (pal_scan_exit_107 x_pre t r PreH8 PreH2) as Hr.
  unfold is_pal_result_107.
  destruct (Z.eqb (reverse_digits_value_107 x_pre) x_pre) eqn:Heq.
  - reflexivity.
  - apply Z.eqb_neq in Heq. lia.
Qed.

Lemma proof_of_even_odd_palindrome_safety_wit_26_split_goal_1 : even_odd_palindrome_safety_wit_26_split_goal_1.
Proof.
  pre_process; entailer!.
  unfold int_range_107 in *; lia.
Qed.

Lemma proof_of_even_odd_palindrome_safety_wit_26_split_goal_2 : even_odd_palindrome_safety_wit_26_split_goal_2.
Proof.
  pre_process; entailer!.
Qed.

Lemma proof_of_even_odd_palindrome_safety_wit_26 : even_odd_palindrome_safety_wit_26.
Proof.
  right. intros. entailer!.
  unfold int_range_107 in *; lia.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_1_split_goal_1 : even_odd_palindrome_entail_wit_1_split_goal_1.
Proof.
  pre_process; entailer!.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_1_split_goal_2 : even_odd_palindrome_entail_wit_1_split_goal_2.
Proof.
  pre_process; entailer!.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_1_split_goal_3 : even_odd_palindrome_entail_wit_1_split_goal_3.
Proof.
  pre_process; entailer!.
  unfold int_range_107 in *; lia.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_1_split_goal_spatial : even_odd_palindrome_entail_wit_1_split_goal_spatial.
Proof.
  pre_process; entailer!.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_1 : even_odd_palindrome_entail_wit_1.
Proof.
  right. intros. entailer!.
  all: unfold int_range_107 in *; cbn; try reflexivity; lia.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_3_1 : even_odd_palindrome_entail_wit_3_1.
Proof.
  right. intros. exfalso.
  destruct (rem2_nonneg_cases_107 i ltac:(lia)); lia.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_3_2 : even_odd_palindrome_entail_wit_3_2.
Proof.
  right. intros. entailer!.
  - apply odd_prefix_step_pal_107 with (retval := retval); auto; lia.
  - apply even_prefix_step_skip_107 with (retval := retval); auto; lia.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_3_3 : even_odd_palindrome_entail_wit_3_3.
Proof.
  right. intros. entailer!.
  - apply odd_prefix_step_skip_107 with (retval := retval); auto; lia.
  - apply even_prefix_step_skip_107 with (retval := retval); auto; lia.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_3_4 : even_odd_palindrome_entail_wit_3_4.
Proof.
  right. intros. entailer!.
  - apply odd_prefix_step_skip_107 with (retval := retval); auto; lia.
  - apply even_prefix_step_pal_107 with (retval := retval); auto; lia.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_4_split_goal_1 : even_odd_palindrome_entail_wit_4_split_goal_1.
Proof.
  pre_process; entailer!.
  replace ((i + 1) - 1) with i by lia.
  assumption.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_4_split_goal_2 : even_odd_palindrome_entail_wit_4_split_goal_2.
Proof.
  pre_process; entailer!.
  replace ((i + 1) - 1) with i by lia.
  assumption.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_4_split_goal_spatial : even_odd_palindrome_entail_wit_4_split_goal_spatial.
Proof.
  pre_process; entailer!.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_4 : even_odd_palindrome_entail_wit_4.
Proof.
  right. intros. entailer!.
  - replace ((i + 1) - 1) with i by lia. assumption.
  - replace ((i + 1) - 1) with i by lia. assumption.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_5_split_goal_1 : even_odd_palindrome_entail_wit_5_split_goal_1.
Proof.
  pre_process; entailer!.
  replace n0 with (i - 1) by lia.
  assumption.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_5_split_goal_2 : even_odd_palindrome_entail_wit_5_split_goal_2.
Proof.
  pre_process; entailer!.
  replace n0 with (i - 1) by lia.
  assumption.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_5_split_goal_spatial : even_odd_palindrome_entail_wit_5_split_goal_spatial.
Proof.
  pre_process; entailer!.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_5 : even_odd_palindrome_entail_wit_5.
Proof.
  right. intros. entailer!.
  - replace n0 with (i - 1) by lia. assumption.
  - replace n0 with (i - 1) by lia. assumption.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_6_split_goal_spatial : even_odd_palindrome_entail_wit_6_split_goal_spatial.
Proof.
  pre_process; unfold IntArray.full, store_array, store_array_rec; simpl; entailer!.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_6 : even_odd_palindrome_entail_wit_6.
Proof.
  right. intros.
  unfold IntArray.full, store_array, store_array_rec; simpl; entailer!.
Qed.

Lemma proof_of_even_odd_palindrome_return_wit_1 : even_odd_palindrome_return_wit_1.
Proof.
  left. intros. subst num1 num2. Exists data_2. entailer!.
  apply problem_107_spec_z_of_counts. assumption.
Qed.

Lemma proof_of_even_odd_palindrome_partial_solve_wit_3_pure_split_goal_1 : even_odd_palindrome_partial_solve_wit_3_pure_split_goal_1.
Proof.
  pre_process; entailer!.
  unfold int_range_107 in *; lia.
Qed.

Lemma proof_of_even_odd_palindrome_partial_solve_wit_3_pure : even_odd_palindrome_partial_solve_wit_3_pure.
Proof.
  right. intros. entailer!.
  unfold int_range_107 in *; lia.
Qed.

Lemma proof_of_even_odd_palindrome_partial_solve_wit_4_pure_split_goal_1 : even_odd_palindrome_partial_solve_wit_4_pure_split_goal_1.
Proof.
  pre_process; entailer!.
  unfold int_range_107 in *; lia.
Qed.

Lemma proof_of_even_odd_palindrome_partial_solve_wit_4_pure : even_odd_palindrome_partial_solve_wit_4_pure.
Proof.
  right. intros. entailer!.
  unfold int_range_107 in *; lia.
Qed.

Lemma proof_of_even_odd_palindrome_partial_solve_wit_5_pure_split_goal_1 : even_odd_palindrome_partial_solve_wit_5_pure_split_goal_1.
Proof.
  pre_process; entailer!.
  unfold int_range_107 in *; lia.
Qed.

Lemma proof_of_even_odd_palindrome_partial_solve_wit_5_pure : even_odd_palindrome_partial_solve_wit_5_pure.
Proof.
  right. intros. entailer!.
  unfold int_range_107 in *; lia.
Qed.

Lemma proof_of_even_odd_palindrome_partial_solve_wit_6_pure_split_goal_1 : even_odd_palindrome_partial_solve_wit_6_pure_split_goal_1.
Proof.
  pre_process; entailer!.
  unfold int_range_107 in *; lia.
Qed.

Lemma proof_of_even_odd_palindrome_partial_solve_wit_6_pure : even_odd_palindrome_partial_solve_wit_6_pure.
Proof.
  right. intros. entailer!.
  unfold int_range_107 in *; lia.
Qed.
