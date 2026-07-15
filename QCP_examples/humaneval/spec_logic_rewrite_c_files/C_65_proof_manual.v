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
Require Import C_65_goal.
Require Import C_65_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_65.
Local Open Scope sac.

Ltac normalize_65 :=
  repeat match goal with
  | |- context[?x ÷ ?y] =>
      rewrite (Z.quot_div_nonneg x y) by lia
  | H : context[?x ÷ ?y] |- _ =>
      rewrite (Z.quot_div_nonneg x y) in H by lia
  | |- context[?x % ?y] =>
      rewrite (Z.rem_mod_nonneg x y) by lia
  | H : context[?x % ?y] |- _ =>
      rewrite (Z.rem_mod_nonneg x y) in H by lia
  | |- context[signed_last_nbits ?x 8] =>
      rewrite (signed_last_nbits_eq x 8) by
        (try change (2 ^ (8 - 1)) with 128; lia)
  | H : context[signed_last_nbits ?x 8] |- _ =>
      rewrite (signed_last_nbits_eq x 8) in H by
        (try change (2 ^ (8 - 1)) with 128; lia)
  | |- context[signed_last_nbits ?x 32] =>
      rewrite (signed_last_nbits_eq x 32) by
        (try change (2 ^ (32 - 1)) with 2147483648; lia)
  | H : context[signed_last_nbits ?x 32] |- _ =>
      rewrite (signed_last_nbits_eq x 32) in H by
        (try change (2 ^ (32 - 1)) with 2147483648; lia)
  end.

Ltac finish_65 :=
  normalize_65;
  try rewrite decimal_digits_z_65_zero;
  try rewrite Zlength_repeat_Z_65 by lia;
  try rewrite Zlength_replace_Znth_65 by lia;
  try match goal with
  | |- context[?x mod 10] =>
      let Hmod := fresh "Hmod" in
      pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hmod
  | H : context[?x mod 10] |- _ =>
      let Hmod := fresh "Hmod" in
      pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hmod
  end;
  try match goal with
  | |- context[Z.rem ?x 10] =>
      let Hrem := fresh "Hrem" in
      pose proof (Z.rem_bound_pos x 10 ltac:(lia)) as Hrem
  | H : context[Z.rem ?x 10] |- _ =>
      let Hrem := fresh "Hrem" in
      pose proof (Z.rem_bound_pos x 10 ltac:(lia)) as Hrem
  end;
  try lia;
  try cancel.

Ltac solve_simple_65 :=
  pre_process;
  finish_65;
  try subst;
  try entailer!;
  finish_65.

Lemma proof_of_circular_shift_safety_wit_23_split_goal_1 : circular_shift_safety_wit_23_split_goal_1.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_safety_wit_23_split_goal_2 : circular_shift_safety_wit_23_split_goal_2.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_safety_wit_23 : circular_shift_safety_wit_23.
Proof.
  unfold circular_shift_safety_wit_23.
  intros. pre_process.
  entailer!;
    replace (tmp % 10) with (tmp mod 10)
      by (symmetry; apply Z.rem_mod_nonneg; lia);
    pose proof (Z.mod_pos_bound tmp 10 ltac:(lia));
    lia.
Qed.

Lemma proof_of_circular_shift_entail_wit_1_split_goal_1 : circular_shift_entail_wit_1_split_goal_1.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_entail_wit_1_split_goal_spatial : circular_shift_entail_wit_1_split_goal_spatial.
Proof.
  unfold circular_shift_entail_wit_1_split_goal_spatial.
  intros. pre_process.
  rewrite PreH1.
  rewrite decimal_digits_z_65_zero.
  change (List.app (48 :: nil) (0 :: nil)) with (48 :: 0 :: nil).
  rewrite (CharArray.full_unfold retval (1 + 1) (0 :: nil) 48).
  rewrite (CharArray.seg_unfold retval 1 (1 + 1) nil 0).
  rewrite (CharArray.seg_empty retval 2 2).
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_1 : circular_shift_entail_wit_1.
Proof.
  unfold circular_shift_entail_wit_1.
  intros. pre_process.
  rewrite PreH1.
  rewrite decimal_digits_z_65_zero.
  change (List.app (48 :: nil) (0 :: nil)) with (48 :: 0 :: nil).
  rewrite (CharArray.full_unfold retval (1 + 1) (0 :: nil) 48).
  rewrite (CharArray.seg_unfold retval 1 (1 + 1) nil 0).
  rewrite (CharArray.seg_empty retval 2 2).
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_2_split_goal_1 : circular_shift_entail_wit_2_split_goal_1.
Proof.
  unfold circular_shift_entail_wit_2_split_goal_1.
  intros. pre_process.
  entailer!.
  apply base_count_state_init_65. lia.
Qed.

Lemma proof_of_circular_shift_entail_wit_2_split_goal_spatial : circular_shift_entail_wit_2_split_goal_spatial.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_entail_wit_2 : circular_shift_entail_wit_2.
Proof.
  unfold circular_shift_entail_wit_2.
  intros. pre_process.
  entailer!.
  apply base_count_state_init_65. lia.
Qed.

Lemma proof_of_circular_shift_entail_wit_3_split_goal_1 : circular_shift_entail_wit_3_split_goal_1.
Proof.
  unfold circular_shift_entail_wit_3_split_goal_1.
  intros. pre_process.
  replace (tmp ÷ 10) with (tmp / 10)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  entailer!.
  apply base_count_state_step_65; try lia; assumption.
Qed.

Lemma proof_of_circular_shift_entail_wit_3_split_goal_2 : circular_shift_entail_wit_3_split_goal_2.
Proof.
  unfold circular_shift_entail_wit_3_split_goal_2.
  intros. pre_process.
  assert (Htpos : 0 < tmp) by lia.
  pose proof (base_count_state_step_65 x_pre 10 tmp n Htpos ltac:(lia) PreH13) as Hstep.
  unfold base_count_state_z_65 in Hstep.
  destruct Hstep as [_ [_ Hlen]].
  unfold decimal_digits_z_65 in *.
  unfold base_digits_pos_z_65 in Hlen.
  replace ((x_pre <=? 0)%Z) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  pose proof (Zlength_nonneg
    (if (tmp / 10 <=? 0)%Z then nil else base_digits_z_65 (tmp / 10) 10)).
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_3_split_goal_3 : circular_shift_entail_wit_3_split_goal_3.
Proof.
  unfold circular_shift_entail_wit_3_split_goal_3.
  intros. pre_process.
  replace (tmp ÷ 10) with (tmp / 10)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  entailer!.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_circular_shift_entail_wit_3_split_goal_spatial : circular_shift_entail_wit_3_split_goal_spatial.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_entail_wit_3 : circular_shift_entail_wit_3.
Proof.
  unfold circular_shift_entail_wit_3.
  intros. pre_process.
  assert (Htpos : 0 < tmp) by lia.
  pose proof (base_count_state_step_65 x_pre 10 tmp n Htpos ltac:(lia) PreH13) as Hstep.
  replace (tmp ÷ 10) with (tmp / 10)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  assert (Hnlt : n + 1 < 64).
  {
    unfold base_count_state_z_65 in Hstep.
    destruct Hstep as [_ [_ Hlen]].
    unfold decimal_digits_z_65 in *.
    unfold base_digits_pos_z_65 in Hlen.
    replace ((x_pre <=? 0)%Z) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
    pose proof (Zlength_nonneg
      (if (tmp / 10 <=? 0)%Z then nil else base_digits_z_65 (tmp / 10) 10)).
    lia.
  }
  entailer!.
  - apply Z.div_pos; lia.
Qed.

Lemma proof_of_circular_shift_entail_wit_4_split_goal_1 : circular_shift_entail_wit_4_split_goal_1.
Proof.
  unfold circular_shift_entail_wit_4_split_goal_1.
  intros. pre_process.
  assert (tmp = 0) by lia. subst tmp.
  pose proof (base_count_state_done_65 x_pre 10 n ltac:(lia) PreH13) as Hn.
  unfold decimal_digits_z_65.
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_4_split_goal_spatial : circular_shift_entail_wit_4_split_goal_spatial.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_entail_wit_4 : circular_shift_entail_wit_4.
Proof.
  unfold circular_shift_entail_wit_4.
  intros. pre_process.
  assert (tmp = 0) by lia. subst tmp.
  match goal with
  | H : base_count_state_z_65 x_pre 10 0 n |- _ =>
      pose proof (base_count_state_done_65 x_pre 10 n ltac:(lia) H) as Hn
  end.
  assert (Hndec : n = Zlength (decimal_digits_z_65 x_pre)).
  { unfold decimal_digits_z_65. exact Hn. }
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_5_split_goal_1 : circular_shift_entail_wit_5_split_goal_1.
Proof.
  unfold circular_shift_entail_wit_5_split_goal_1.
  intros. pre_process.
  pose proof (Zlength_nonneg (decimal_digits_z_65 x_pre)).
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_5_split_goal_2 : circular_shift_entail_wit_5_split_goal_2.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_entail_wit_5_split_goal_spatial : circular_shift_entail_wit_5_split_goal_spatial.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_entail_wit_5 : circular_shift_entail_wit_5.
Proof.
  unfold circular_shift_entail_wit_5.
  intros. pre_process.
  sep_apply (CharArray.undef_full_split_to_undef_seg buf 0 64).
  2: lia.
  rewrite (CharArray.undef_seg_empty buf 0).
  rewrite (CharArray.full_empty buf 0).
  entailer!.
  rewrite PreH5.
  pose proof (Zlength_nonneg (decimal_digits_z_65 x_pre)).
  lia.
Qed.

Lemma proof_of_circular_shift_entail_wit_6_split_goal_1 : circular_shift_entail_wit_6_split_goal_1.
Proof.
  unfold circular_shift_entail_wit_6_split_goal_1.
  intros. pre_process.
  rewrite repeat_Z_tail_65 by lia.
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_6 : circular_shift_entail_wit_6.
Proof.
  unfold circular_shift_entail_wit_6.
  intros. pre_process.
  rewrite repeat_Z_tail_65 by lia.
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_7 : circular_shift_entail_wit_7.
Proof.
  unfold circular_shift_entail_wit_7.
  intros. pre_process.
  assert (i = n + 1) by lia. subst i.
  Exists (repeat_Z 0 n).
  rewrite repeat_Z_tail_65 by
    (match goal with H : n = Zlength _ |- _ => rewrite H; apply Zlength_nonneg end).
  entailer!.
  - match goal with H : n = Zlength _ |- _ => rewrite H end.
    unfold decimal_digits_z_65.
    apply base_fill_full_state_init_65. lia.
  - rewrite Zlength_repeat_Z_65;
      [reflexivity |
       match goal with H : n = Zlength _ |- _ => rewrite H; apply Zlength_nonneg end].
Qed.

Lemma proof_of_circular_shift_entail_wit_8 : circular_shift_entail_wit_8.
Proof.
  unfold circular_shift_entail_wit_8.
  intros. pre_process.
  Exists out_l_2.
  entailer!.
  match goal with H : n = Zlength _ |- _ => rewrite H end.
  apply Zlength_nonneg.
Qed.

Lemma proof_of_circular_shift_entail_wit_9 : circular_shift_entail_wit_9.
Proof.
  unfold circular_shift_entail_wit_9.
  intros. pre_process.
  Exists out_l_2.
  assert (1 <= fill).
  { eapply (base_fill_full_state_positive_digits_65 x_pre 10 tmp fill out_l_2);
      try lia; eassumption. }
  replace (fill - 1 + 1) with fill by lia.
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_10 : circular_shift_entail_wit_10.
Proof.
  unfold circular_shift_entail_wit_10.
  intros. pre_process.
  replace (tmp ÷ 10) with (tmp / 10)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace (Z.rem tmp 10) with (tmp mod 10)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  Exists (replace_Znth fill (signed_last_nbits (48 + tmp mod 10) 8) out_l_2).
  rewrite replace_Znth_app_l by lia.
  entailer!.
  - apply base_fill_full_state_step_65; try lia; assumption.
  - rewrite Zlength_replace_Znth_65; lia.
  - apply Z.div_pos; lia.
Qed.

Lemma proof_of_circular_shift_entail_wit_11_split_goal_1 : circular_shift_entail_wit_11_split_goal_1.
Proof.
  unfold circular_shift_entail_wit_11_split_goal_1.
  intros. pre_process.
  assert (tmp = 0) by lia. subst tmp.
  destruct PreH14 as [suffix [[_ [_ [Hdigits _]]] _]].
  unfold base_digits_pos_z_65 in Hdigits.
  replace (0 <=? 0)%Z with true in Hdigits by (symmetry; apply Z.leb_le; lia).
  change (Zlength (@nil Z)) with 0 in Hdigits.
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_11_split_goal_2 : circular_shift_entail_wit_11_split_goal_2.
Proof.
  unfold circular_shift_entail_wit_11_split_goal_2.
  intros. pre_process.
  assert (tmp = 0) by lia. subst tmp.
  assert (fill = 0).
  {
    destruct PreH14 as [suffix [[_ [_ [Hdigits _]]] _]].
    unfold base_digits_pos_z_65 in Hdigits.
    replace (0 <=? 0)%Z with true in Hdigits by (symmetry; apply Z.leb_le; lia).
    change (Zlength (@nil Z)) with 0 in Hdigits.
    lia.
  }
  subst fill.
  assert (out_l_2 = base_digits_z_65 x_pre 10)
    by (eapply base_fill_full_state_done_65; eassumption).
  subst out_l_2.
  unfold decimal_digits_z_65.
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_11 : circular_shift_entail_wit_11.
Proof.
  unfold circular_shift_entail_wit_11.
  intros. pre_process.
  assert (tmp = 0) by lia. subst tmp.
  assert (fill = 0).
  {
    destruct PreH14 as [suffix [[_ [_ [Hdigits _]]] _]].
    unfold base_digits_pos_z_65 in Hdigits.
    replace (0 <=? 0)%Z with true in Hdigits by (symmetry; apply Z.leb_le; lia).
    change (Zlength (@nil Z)) with 0 in Hdigits.
    lia.
  }
  subst fill.
  Exists (base_digits_z_65 x_pre 10).
  assert (out_l_2 = base_digits_z_65 x_pre 10).
  { eapply base_fill_full_state_done_65; eassumption. }
  subst out_l_2.
  unfold decimal_digits_z_65.
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_12_1_split_goal_1 : circular_shift_entail_wit_12_1_split_goal_1.
Proof.
  unfold circular_shift_entail_wit_12_1_split_goal_1.
  intros. pre_process.
  pose proof (Zlength_nonneg (decimal_digits_z_65 x_pre)).
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_12_1 : circular_shift_entail_wit_12_1.
Proof.
  unfold circular_shift_entail_wit_12_1.
  intros. pre_process.
  rewrite PreH11.
  entailer!.
  rewrite PreH10, PreH5.
  pose proof (Zlength_nonneg (decimal_digits_z_65 x_pre)).
  lia.
Qed.

Lemma proof_of_circular_shift_entail_wit_13_split_goal_1 : circular_shift_entail_wit_13_split_goal_1.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_entail_wit_13_split_goal_2 : circular_shift_entail_wit_13_split_goal_2.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_entail_wit_13_split_goal_3 : circular_shift_entail_wit_13_split_goal_3.
Proof.
  unfold circular_shift_entail_wit_13_split_goal_3.
  intros. pre_process.
  pose proof (Zlength_nonneg (decimal_digits_z_65 x_pre)).
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_13_split_goal_spatial : circular_shift_entail_wit_13_split_goal_spatial.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_entail_wit_13 : circular_shift_entail_wit_13.
Proof.
  unfold circular_shift_entail_wit_13.
  intros. pre_process.
  Exists (@nil Z).
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (n + 1)).
  2: lia.
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  match goal with H : n = Zlength _ |- _ => rewrite H end.
  apply Zlength_nonneg.
Qed.

Lemma proof_of_circular_shift_entail_wit_14_split_goal_1 : circular_shift_entail_wit_14_split_goal_1.
Proof.
  unfold circular_shift_entail_wit_14_split_goal_1.
  intros. pre_process.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_14_split_goal_2 : circular_shift_entail_wit_14_split_goal_2.
Proof.
  unfold circular_shift_entail_wit_14_split_goal_2.
  intros. pre_process.
  rewrite app_Znth1 by lia.
  replace (n - 1 - i) with (Zlength (decimal_digits_z_65 x_pre) - 1 - i) by lia.
  rewrite <- (circular_shift_output_z_65_reverse_char x_pre shift_pre i) by lia.
  entailer!.
  apply circular_shift_prefix_z_65_snoc; auto; try lia.
  rewrite circular_shift_output_z_65_length by lia. lia.
Qed.

Lemma proof_of_circular_shift_entail_wit_14 : circular_shift_entail_wit_14.
Proof.
  unfold circular_shift_entail_wit_14.
  intros. pre_process.
  rewrite app_Znth1 by lia.
  replace ((n - 1) - i) with (Zlength (decimal_digits_z_65 x_pre) - 1 - i) by lia.
  rewrite <- (circular_shift_output_z_65_reverse_char x_pre shift_pre i) by lia.
  Exists (app out_l_2 (cons (Znth i (circular_shift_output_z_65 x_pre shift_pre) 0) nil)).
  assert (Hprefix :
    circular_shift_prefix_z_65 x_pre shift_pre (i + 1)
      (app out_l_2 (cons (Znth i (circular_shift_output_z_65 x_pre shift_pre) 0) nil))).
  { apply circular_shift_prefix_z_65_snoc; auto; try lia.
    rewrite circular_shift_output_z_65_length by lia. lia. }
  assert (Hlen :
    Zlength (app out_l_2 (cons (Znth i (circular_shift_output_z_65 x_pre shift_pre) 0) nil)) =
    i + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_15_split_goal_1 : circular_shift_entail_wit_15_split_goal_1.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_entail_wit_15_split_goal_2 : circular_shift_entail_wit_15_split_goal_2.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_entail_wit_15_split_goal_spatial : circular_shift_entail_wit_15_split_goal_spatial.
Proof. solve_simple_65. Qed.

Lemma proof_of_circular_shift_entail_wit_15 : circular_shift_entail_wit_15.
Proof.
  unfold circular_shift_entail_wit_15.
  intros. pre_process.
  Exists (@nil Z).
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (n + 1)).
  2: lia.
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_16_1_split_goal_1 : circular_shift_entail_wit_16_1_split_goal_1.
Proof.
  unfold circular_shift_entail_wit_16_1_split_goal_1.
  intros. pre_process.
  entailer!.
  symmetry. apply Z.rem_small. lia.
Qed.

Lemma proof_of_circular_shift_entail_wit_16_1 : circular_shift_entail_wit_16_1.
Proof.
  unfold circular_shift_entail_wit_16_1.
  intros. pre_process.
  Exists out_l_2.
  assert (((n - shift_pre) + i) = Z.rem ((n - shift_pre) + i) n).
  { symmetry. apply Z.rem_small. lia. }
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_16_2_split_goal_1 : circular_shift_entail_wit_16_2_split_goal_1.
Proof.
  unfold circular_shift_entail_wit_16_2_split_goal_1.
  intros. pre_process.
  entailer!.
  apply (Z.rem_unique (n - shift_pre + i) n 1 (n - shift_pre + i - n)); lia.
Qed.

Lemma proof_of_circular_shift_entail_wit_16_2 : circular_shift_entail_wit_16_2.
Proof.
  unfold circular_shift_entail_wit_16_2.
  intros. pre_process.
  Exists out_l_2.
  assert ((((n - shift_pre) + i) - n) = Z.rem ((n - shift_pre) + i) n).
  { apply (Z.rem_unique (n - shift_pre + i) n 1 (n - shift_pre + i - n)); lia. }
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_17_split_goal_1 : circular_shift_entail_wit_17_split_goal_1.
Proof.
  unfold circular_shift_entail_wit_17_split_goal_1.
  intros. pre_process.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_17_split_goal_2 : circular_shift_entail_wit_17_split_goal_2.
Proof.
  unfold circular_shift_entail_wit_17_split_goal_2.
  intros. pre_process.
  subst src.
  replace (Z.rem (n - shift_pre + i) n) with ((n - shift_pre + i) mod n).
  2:{ symmetry. apply Z.rem_mod_nonneg; lia. }
  assert (Hmod_bound : 0 <= (n - shift_pre + i) mod n < n).
  { apply Z.mod_pos_bound. lia. }
  rewrite app_Znth1 by lia.
  replace (((n - shift_pre) + i) mod n)
    with ((Zlength (decimal_digits_z_65 x_pre) - shift_pre + i) mod
          Zlength (decimal_digits_z_65 x_pre)) by (subst n; reflexivity).
  rewrite <- (circular_shift_output_z_65_rot_char x_pre shift_pre i) by lia.
  entailer!.
  apply circular_shift_prefix_z_65_snoc; auto; try lia.
  rewrite circular_shift_output_z_65_length by lia. lia.
Qed.

Lemma proof_of_circular_shift_entail_wit_17 : circular_shift_entail_wit_17.
Proof.
  unfold circular_shift_entail_wit_17.
  intros. pre_process.
  subst src.
  replace (Z.rem (n - shift_pre + i) n) with ((n - shift_pre + i) mod n).
  2:{ symmetry. apply Z.rem_mod_nonneg; lia. }
  assert (Hmod_bound : 0 <= (n - shift_pre + i) mod n < n).
  { apply Z.mod_pos_bound. lia. }
  rewrite app_Znth1 by lia.
  replace (((n - shift_pre) + i) mod n)
    with ((Zlength (decimal_digits_z_65 x_pre) - shift_pre + i) mod
          Zlength (decimal_digits_z_65 x_pre)) by (subst n; reflexivity).
  rewrite <- (circular_shift_output_z_65_rot_char x_pre shift_pre i) by lia.
  Exists (app out_l_2 (cons (Znth i (circular_shift_output_z_65 x_pre shift_pre) 0) nil)).
  assert (Hprefix :
    circular_shift_prefix_z_65 x_pre shift_pre (i + 1)
      (app out_l_2 (cons (Znth i (circular_shift_output_z_65 x_pre shift_pre) 0) nil))).
  { apply circular_shift_prefix_z_65_snoc; auto; try lia.
    rewrite circular_shift_output_z_65_length by lia. lia. }
  assert (Hlen :
    Zlength (app out_l_2 (cons (Znth i (circular_shift_output_z_65 x_pre shift_pre) 0) nil)) =
    i + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_18_1_split_goal_1 : circular_shift_entail_wit_18_1_split_goal_1.
Proof.
  unfold circular_shift_entail_wit_18_1_split_goal_1.
  intros. pre_process.
  rewrite circular_shift_output_z_65_length by lia.
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_18_1_split_goal_2 : circular_shift_entail_wit_18_1_split_goal_2.
Proof.
  unfold circular_shift_entail_wit_18_1_split_goal_2.
  intros. pre_process.
  entailer!.
  assert (Hlenout : Zlength out_l_2 = n) by lia.
  assert (Heqout : out_l_2 = circular_shift_output_z_65 x_pre shift_pre).
  { apply circular_shift_prefix_z_65_full; try lia.
    rewrite <- PreH8, <- Hlenout.
    rewrite PreH14. exact PreH13. }
  rewrite <- Heqout.
  rewrite <- Hlenout.
  rewrite PreH14. exact PreH13.
Qed.

Lemma proof_of_circular_shift_entail_wit_18_1_split_goal_spatial : circular_shift_entail_wit_18_1_split_goal_spatial.
Proof.
  unfold circular_shift_entail_wit_18_1_split_goal_spatial.
  intros. pre_process.
  assert (Hlenout : Zlength out_l_2 = n) by lia.
  assert (Heqout : out_l_2 = circular_shift_output_z_65 x_pre shift_pre).
  { apply circular_shift_prefix_z_65_full; try lia.
    rewrite <- PreH8, <- Hlenout.
    rewrite PreH14. exact PreH13. }
  rewrite <- Hlenout, <- Heqout.
  rewrite PreH14.
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_18_1 : circular_shift_entail_wit_18_1.
Proof.
  unfold circular_shift_entail_wit_18_1.
  intros. pre_process.
  Exists out_l_2.
  assert (Hlenout : Zlength out_l_2 = n) by lia.
  assert (Heqout : out_l_2 = circular_shift_output_z_65 x_pre shift_pre).
  { apply circular_shift_prefix_z_65_full; try lia.
    rewrite <- PreH8, <- Hlenout.
    rewrite PreH14. exact PreH13. }
  replace (Zlength out_l_2) with n in * by lia.
  rewrite <- PreH14.
  entailer!.
  rewrite PreH14. exact PreH13.
Qed.

Lemma proof_of_circular_shift_entail_wit_18_2_split_goal_1 : circular_shift_entail_wit_18_2_split_goal_1.
Proof.
  unfold circular_shift_entail_wit_18_2_split_goal_1.
  intros. pre_process.
  rewrite circular_shift_output_z_65_length by lia.
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_18_2_split_goal_2 : circular_shift_entail_wit_18_2_split_goal_2.
Proof.
  unfold circular_shift_entail_wit_18_2_split_goal_2.
  intros. pre_process.
  entailer!.
  assert (Hlenout : Zlength out_l_2 = n) by lia.
  assert (Heqout : out_l_2 = circular_shift_output_z_65 x_pre shift_pre).
  { apply circular_shift_prefix_z_65_full; try lia.
    rewrite <- PreH9, <- Hlenout.
    rewrite PreH15. exact PreH14. }
  rewrite <- Heqout.
  rewrite <- Hlenout.
  rewrite PreH15. exact PreH14.
Qed.

Lemma proof_of_circular_shift_entail_wit_18_2_split_goal_spatial : circular_shift_entail_wit_18_2_split_goal_spatial.
Proof.
  unfold circular_shift_entail_wit_18_2_split_goal_spatial.
  intros. pre_process.
  assert (Hlenout : Zlength out_l_2 = n) by lia.
  assert (Heqout : out_l_2 = circular_shift_output_z_65 x_pre shift_pre).
  { apply circular_shift_prefix_z_65_full; try lia.
    rewrite <- PreH9, <- Hlenout.
    rewrite PreH15. exact PreH14. }
  rewrite <- Hlenout, <- Heqout.
  rewrite PreH15.
  entailer!.
Qed.

Lemma proof_of_circular_shift_entail_wit_18_2 : circular_shift_entail_wit_18_2.
Proof.
  unfold circular_shift_entail_wit_18_2.
  intros. pre_process.
  Exists out_l_2.
  assert (Hlenout : Zlength out_l_2 = n) by lia.
  assert (Heqout : out_l_2 = circular_shift_output_z_65 x_pre shift_pre).
  { apply circular_shift_prefix_z_65_full; try lia.
    rewrite <- PreH9, <- Hlenout.
    rewrite PreH15. exact PreH14. }
  replace (Zlength out_l_2) with n in * by lia.
  rewrite <- PreH15.
  entailer!.
  rewrite PreH15. exact PreH14.
Qed.

Lemma proof_of_circular_shift_return_wit_1 : circular_shift_return_wit_1.
Proof.
  unfold circular_shift_return_wit_1.
  intros. pre_process.
  Exists buf out_l_2 n.
  rewrite (CharArray.undef_seg_empty out (n + 1)).
  entailer!.
  - rewrite <- PreH10.
    entailer!.
  - rewrite PreH13.
    apply problem_65_spec_z_intro; lia.
  - rewrite circular_shift_output_z_65_length by lia.
    lia.
Qed.

Lemma proof_of_circular_shift_partial_solve_wit_6_pure_split_goal_1 : circular_shift_partial_solve_wit_6_pure_split_goal_1.
Proof.
  unfold circular_shift_partial_solve_wit_6_pure_split_goal_1.
  intros. pre_process. entailer!.
  pose proof (Zlength_nonneg (decimal_digits_z_65 x_pre)).
  lia.
Qed.

Lemma proof_of_circular_shift_partial_solve_wit_6_pure : circular_shift_partial_solve_wit_6_pure.
Proof.
  unfold circular_shift_partial_solve_wit_6_pure.
  intros. pre_process. entailer!.
  pose proof (Zlength_nonneg (decimal_digits_z_65 x_pre)).
  lia.
Qed.
