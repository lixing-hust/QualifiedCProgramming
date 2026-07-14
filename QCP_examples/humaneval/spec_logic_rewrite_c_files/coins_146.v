Load "../spec/146".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_146_pre_z (nums : list Z) : Prop :=
  problem_146_pre nums.

Definition problem_146_spec_z (nums : list Z) (out : Z) : Prop :=
  problem_146_spec nums out.

Definition first_digit_state_146 (x first : Z) : Prop :=
  0 <= first <= x /\
  0 < x /\
  1 <= first /\
  exists k tail,
    0 <= k /\
    0 <= tail < 10 ^ k /\
    x = first * 10 ^ k + tail.

Definition special_filter_safe_146 (nums : list Z) : Prop :=
  Forall
    (fun x =>
      INT_MIN <= x <= INT_MAX /\
      (x <= 10 -> special_number_score x 0) /\
      (10 < x -> first_digit_state_146 x x) /\
      (forall first last_digit score,
        first_digit_state_146 x first ->
        first < 10 ->
        last_digit = Z.rem x 10 ->
        ((10 < x /\
          Z.odd first = true /\
          Z.odd last_digit = true /\
          score = 1) \/
         ((x <= 10 \/
           Z.odd first = false \/
           Z.odd last_digit = false) /\
          score = 0)) ->
        special_number_score x score))
    nums.

Definition special_filter_prefix_146 (nums : list Z) (i count : Z) : Prop :=
  exists scores,
    0 <= i <= Zlength nums /\
    Forall2 special_number_score (sublist 0 i nums) scores /\
    count = fold_left Z.add scores 0.

Lemma special_filter_safe_Znth_range_146 : forall nums i,
  special_filter_safe_146 nums ->
  0 <= i < Zlength nums ->
  INT_MIN <= Znth i nums 0 <= INT_MAX.
Proof.
  intros nums i Hsafe Hi.
  unfold special_filter_safe_146 in Hsafe.
  rewrite Forall_forall in Hsafe.
  specialize (Hsafe (Znth i nums 0)).
  assert (In (Znth i nums 0) nums).
  { unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia. }
  specialize (Hsafe H).
  tauto.
Qed.

Lemma special_filter_safe_Znth_small_score_146 : forall nums i,
  special_filter_safe_146 nums ->
  0 <= i < Zlength nums ->
  Znth i nums 0 <= 10 ->
  special_number_score (Znth i nums 0) 0.
Proof.
  intros nums i Hsafe Hi Hsmall.
  unfold special_filter_safe_146 in Hsafe.
  rewrite Forall_forall in Hsafe.
  specialize (Hsafe (Znth i nums 0)).
  assert (In (Znth i nums 0) nums).
  { unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia. }
  specialize (Hsafe H) as [_ [Hscore _]].
  apply Hscore; lia.
Qed.

Lemma special_filter_safe_Znth_first_init_146 : forall nums i,
  special_filter_safe_146 nums ->
  0 <= i < Zlength nums ->
  10 < Znth i nums 0 ->
  first_digit_state_146 (Znth i nums 0) (Znth i nums 0).
Proof.
  intros nums i Hsafe Hi Hgt.
  unfold special_filter_safe_146 in Hsafe.
  rewrite Forall_forall in Hsafe.
  specialize (Hsafe (Znth i nums 0)).
  assert (In (Znth i nums 0) nums).
  { unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia. }
  specialize (Hsafe H) as [_ [_ [Hinit _]]].
  apply Hinit; lia.
Qed.

Lemma special_filter_safe_Znth_scan_score_146 : forall nums i first last_digit score,
  special_filter_safe_146 nums ->
  0 <= i < Zlength nums ->
  first_digit_state_146 (Znth i nums 0) first ->
  first < 10 ->
  last_digit = Z.rem (Znth i nums 0) 10 ->
  ((10 < Znth i nums 0 /\
    Z.odd first = true /\
    Z.odd last_digit = true /\
    score = 1) \/
   ((Znth i nums 0 <= 10 \/
     Z.odd first = false \/
     Z.odd last_digit = false) /\
    score = 0)) ->
  special_number_score (Znth i nums 0) score.
Proof.
  intros nums i first last_digit score Hsafe Hi Hstate Hfirst Hlast Hcase.
  unfold special_filter_safe_146 in Hsafe.
  rewrite Forall_forall in Hsafe.
  specialize (Hsafe (Znth i nums 0)).
  assert (In (Znth i nums 0) nums).
  { unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia. }
  specialize (Hsafe H) as [_ [_ [_ Hscore]]].
  eapply Hscore; eauto.
Qed.

Lemma first_digit_state_step_146 : forall x first,
  first_digit_state_146 x first ->
  10 <= first ->
  first_digit_state_146 x (Z.quot first 10).
Proof.
  intros x first Hstate Hfirst.
  unfold first_digit_state_146 in *.
  destruct Hstate as [Hbounds [Hxpos [Hfirst_pos [k [tail [Hk [Htail Hx]]]]]]].
  repeat split.
  - rewrite Z.quot_div_nonneg by lia.
    apply Z.div_pos; lia.
  - rewrite Z.quot_div_nonneg by lia.
    apply Z.div_le_upper_bound; lia.
  - lia.
  - rewrite Z.quot_div_nonneg by lia.
    apply Z.div_le_lower_bound; lia.
  - exists (k + 1), (Z.rem first 10 * 10 ^ k + tail).
    assert (Hrem_bounds : 0 <= Z.rem first 10 < 10).
    { rewrite Z.rem_mod_nonneg by lia.
      apply Z.mod_pos_bound; lia. }
    assert (Hpow_pos : 0 < 10 ^ k).
    { apply Z.pow_pos_nonneg; lia. }
    repeat split.
    + lia.
    + nia.
    + replace (10 ^ (k + 1)) with (10 * 10 ^ k)
        by (replace (k + 1) with (Z.succ k) by lia;
            rewrite Z.pow_succ_r by lia; ring).
      nia.
    + replace (10 ^ (k + 1)) with (10 * 10 ^ k)
        by (replace (k + 1) with (Z.succ k) by lia;
            rewrite Z.pow_succ_r by lia; ring).
      rewrite Hx.
      assert (Hfirst_decomp :
        first = Z.quot first 10 * 10 + Z.rem first 10).
      {
        rewrite Z.quot_div_nonneg by lia.
        rewrite Z.rem_mod_nonneg by lia.
        pose proof (Z.div_mod first 10 ltac:(lia)).
        lia.
      }
      rewrite Hfirst_decomp at 1.
      ring.
Qed.

Lemma special_filter_prefix_init_146 : forall nums,
  special_filter_prefix_146 nums 0 0.
Proof.
  intro nums.
  unfold special_filter_prefix_146.
  exists (@nil Z).
  split; [pose proof (Zlength_nonneg nums); lia|].
  split.
  - replace (sublist 0 0 nums) with (@nil Z)
      by (symmetry; apply sublist_nil; lia).
    constructor.
  - reflexivity.
Qed.

Lemma fold_left_Zadd_app_single_146 : forall scores score,
  fold_left Z.add (scores ++ [score]) 0 =
  fold_left Z.add scores 0 + score.
Proof.
  intros scores score.
  rewrite fold_left_app.
  simpl.
  lia.
Qed.

Lemma special_filter_prefix_step_146 : forall nums i count score,
  0 <= i < Zlength nums ->
  special_filter_prefix_146 nums i count ->
  special_number_score (Znth i nums 0) score ->
  score = 0 \/ score = 1 ->
  special_filter_prefix_146 nums (i + 1) (count + score).
Proof.
  intros nums i count score Hi Hprefix Hscore Hscore01.
  unfold special_filter_prefix_146 in *.
  destruct Hprefix as [scores [Hbounds [Hfor Hcount]]].
  exists (scores ++ [score]).
  split; [lia|].
  split.
  - rewrite (sublist_split 0 (i + 1) i nums)
      by (try rewrite <- Zlength_correct; lia).
    rewrite (sublist_single 0 i nums) by lia.
    apply Forall2_app; [assumption|].
    constructor; [assumption|constructor].
  - rewrite fold_left_Zadd_app_single_146.
    lia.
Qed.

Lemma special_filter_prefix_step_zero_146 : forall nums i count,
  0 <= i < Zlength nums ->
  special_filter_prefix_146 nums i count ->
  special_number_score (Znth i nums 0) 0 ->
  special_filter_prefix_146 nums (i + 1) count.
Proof.
  intros nums i count Hi Hprefix Hscore.
  replace count with (count + 0) by lia.
  eapply special_filter_prefix_step_146; eauto.
Qed.

Lemma special_filter_prefix_step_one_146 : forall nums i count,
  0 <= i < Zlength nums ->
  special_filter_prefix_146 nums i count ->
  special_number_score (Znth i nums 0) 1 ->
  special_filter_prefix_146 nums (i + 1) (count + 1).
Proof.
  intros nums i count Hi Hprefix Hscore.
  eapply special_filter_prefix_step_146; eauto.
Qed.

Lemma special_filter_prefix_final_146 : forall nums count,
  special_filter_prefix_146 nums (Zlength nums) count ->
  problem_146_spec_z nums count.
Proof.
  intros nums count Hprefix.
  unfold problem_146_spec_z, problem_146_spec.
  unfold special_filter_prefix_146 in Hprefix.
  destruct Hprefix as [scores [Hbounds [Hfor Hcount]]].
  exists scores.
  split; [|assumption].
  replace (sublist 0 (Zlength nums) nums) with nums in Hfor
    by (symmetry; apply sublist_self; lia).
  exact Hfor.
Qed.

Lemma rem10_bounds_146 : forall x,
  10 < x ->
  0 <= Z.rem x 10 < 10.
Proof.
  intros x Hx.
  rewrite Z.rem_mod_nonneg by lia.
  apply Z.mod_pos_bound; lia.
Qed.

Lemma odd_true_of_rem2_eq1_146 : forall x,
  0 <= x < 10 ->
  Z.rem x 2 = 1 ->
  Z.odd x = true.
Proof.
  intros x Hx Hrem.
  assert (x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/
          x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9) by lia.
  repeat (destruct H as [H | H]; [subst; cbn in *; try lia; reflexivity |]);
    subst; cbn in *; try lia; reflexivity.
Qed.

Lemma odd_false_of_rem2_neq1_146 : forall x,
  0 <= x < 10 ->
  Z.rem x 2 <> 1 ->
  Z.odd x = false.
Proof.
  intros x Hx Hrem.
  assert (x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/
          x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9) by lia.
  repeat (destruct H as [H | H]; [subst; cbn in *; try lia; reflexivity |]);
    subst; cbn in *; try lia; reflexivity.
Qed.

Lemma special_score_one_from_scan_146 : forall nums i current first last_digit,
  special_filter_safe_146 nums ->
  0 <= i < Zlength nums ->
  current = Znth i nums 0 ->
  10 < current ->
  first_digit_state_146 current first ->
  first < 10 ->
  last_digit = Z.rem current 10 ->
  Z.rem first 2 = 1 ->
  Z.rem last_digit 2 = 1 ->
  special_number_score current 1.
Proof.
  intros nums i current first last_digit Hsafe Hi Hcur Hgt Hstate Hfirst Hlast Hodd_first Hodd_last.
  subst current.
  eapply special_filter_safe_Znth_scan_score_146; eauto.
  left.
  repeat split; try lia.
  - apply odd_true_of_rem2_eq1_146; try lia.
    destruct Hstate as [Hbounds _]. lia.
  - apply odd_true_of_rem2_eq1_146; [|assumption].
    subst last_digit.
    apply rem10_bounds_146; lia.
Qed.

Lemma special_score_zero_from_scan_last_146 : forall nums i current first last_digit,
  special_filter_safe_146 nums ->
  0 <= i < Zlength nums ->
  current = Znth i nums 0 ->
  10 < current ->
  first_digit_state_146 current first ->
  first < 10 ->
  last_digit = Z.rem current 10 ->
  Z.rem last_digit 2 <> 1 ->
  special_number_score current 0.
Proof.
  intros nums i current first last_digit Hsafe Hi Hcur Hgt Hstate Hfirst Hlast Hodd_last.
  subst current.
  eapply special_filter_safe_Znth_scan_score_146; eauto.
  right.
  split; [|reflexivity].
  right; right.
  apply odd_false_of_rem2_neq1_146; [|assumption].
  subst last_digit.
  apply rem10_bounds_146; lia.
Qed.

Lemma special_score_zero_from_scan_first_146 : forall nums i current first last_digit,
  special_filter_safe_146 nums ->
  0 <= i < Zlength nums ->
  current = Znth i nums 0 ->
  10 < current ->
  first_digit_state_146 current first ->
  first < 10 ->
  last_digit = Z.rem current 10 ->
  Z.rem first 2 <> 1 ->
  special_number_score current 0.
Proof.
  intros nums i current first last_digit Hsafe Hi Hcur Hgt Hstate Hfirst Hlast Hodd_first.
  subst current.
  eapply special_filter_safe_Znth_scan_score_146; eauto.
  right.
  split; [|reflexivity].
  right; left.
  apply odd_false_of_rem2_neq1_146; [|assumption].
  destruct Hstate as [Hbounds _]. lia.
Qed.
