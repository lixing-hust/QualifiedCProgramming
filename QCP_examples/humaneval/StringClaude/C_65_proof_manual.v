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
From SimpleC.EE Require Import C_65_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_44.
Require Import coins_65.
Local Open Scope sac.

Lemma proof_of_circular_shift_safety_wit_23 : circular_shift_safety_wit_23.
Proof.
  unfold circular_shift_safety_wit_23.
  intros. pre_process.
  entailer!.
  - replace (tmp % 10) with (tmp mod 10)
      by (symmetry; apply Z.rem_mod_nonneg; lia).
    pose proof (Z.mod_pos_bound tmp 10 ltac:(lia)).
    lia.
  - replace (tmp % 10) with (tmp mod 10)
      by (symmetry; apply Z.rem_mod_nonneg; lia).
    pose proof (Z.mod_pos_bound tmp 10 ltac:(lia)).
    lia.
Qed. 

Lemma proof_of_circular_shift_entail_wit_1 : circular_shift_entail_wit_1.
Proof.
  unfold circular_shift_entail_wit_1.
  intros. pre_process.
  rewrite H.
  rewrite decimal_digits_z_zero.
  change (List.app (48 :: nil) (0 :: nil)) with (48 :: 0 :: nil).
  rewrite (CharArray.full_unfold retval (1 + 1) (0 :: nil) 48).
  rewrite (CharArray.seg_unfold retval 1 (1 + 1) nil 0).
  rewrite (CharArray.seg_empty retval 2 2).
  entailer!.
Qed. 

Lemma proof_of_circular_shift_entail_wit_2 : circular_shift_entail_wit_2.
Proof.
  unfold circular_shift_entail_wit_2.
  intros. pre_process.
  entailer!.
  apply base_count_state_init. lia.
Qed. 

Lemma proof_of_circular_shift_entail_wit_3 : circular_shift_entail_wit_3.
Proof.
  unfold circular_shift_entail_wit_3.
  intros. pre_process.
  assert (Htpos : 0 < tmp) by lia.
  pose proof (base_count_state_step x_pre 10 tmp n Htpos ltac:(lia) H11) as Hstep.
  replace (tmp ÷ 10) with (tmp / 10)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  assert (Hnlt : n + 1 < 64).
  {
    unfold base_count_state_z in Hstep.
    destruct Hstep as [_ [_ Hlen]].
    unfold base_digits_pos_z in Hlen.
    replace ((x_pre <=? 0)%Z) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
    rewrite (base_digits_z_10_decimal_digits_z x_pre) in Hlen by lia.
    pose proof (Zlength_nonneg
      (if (tmp / 10 <=? 0)%Z then nil else base_digits_z (tmp / 10) 10)).
    lia.
  }
  entailer!.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_circular_shift_entail_wit_4 : circular_shift_entail_wit_4.
Proof.
  unfold circular_shift_entail_wit_4.
  intros. pre_process.
  assert (tmp = 0) by lia. subst tmp.
  match goal with
  | H : base_count_state_z x_pre 10 0 n |- _ =>
      pose proof (base_count_state_done x_pre 10 n ltac:(lia) H) as Hn
  end.
  assert (Hndec : n = Zlength (decimal_digits_z x_pre)).
  { rewrite Hn. rewrite base_digits_z_10_decimal_digits_z by lia. reflexivity. }
  entailer!.
Qed. 

Lemma proof_of_circular_shift_entail_wit_5 : circular_shift_entail_wit_5.
Proof.
  unfold circular_shift_entail_wit_5.
  intros. pre_process.
  sep_apply (CharArray.undef_full_split_to_undef_seg buf 0 64).
  2: lia.
  rewrite (CharArray.undef_seg_empty buf 0).
  rewrite (CharArray.full_empty buf 0).
  entailer!.
  rewrite H4.
  pose proof (Zlength_nonneg (decimal_digits_z x_pre)).
  lia.
Qed. 

Lemma proof_of_circular_shift_entail_wit_6 : circular_shift_entail_wit_6.
Proof.
  unfold circular_shift_entail_wit_6.
  intros. pre_process.
  rewrite repeat_Z_tail by lia.
  entailer!.
Qed. 

Lemma proof_of_circular_shift_entail_wit_7 : circular_shift_entail_wit_7.
Proof.
  unfold circular_shift_entail_wit_7.
  intros. pre_process.
  assert (i = n + 1) by lia. subst i.
  Exists (repeat_Z 0 n).
  rewrite repeat_Z_tail by (rewrite H4; apply Zlength_nonneg).
  entailer!.
  - rewrite H4.
    apply base_fill_full_state_init. lia.
  - rewrite Zlength_repeat_Z; [reflexivity | rewrite H4; apply Zlength_nonneg].
Qed. 

Lemma proof_of_circular_shift_entail_wit_8 : circular_shift_entail_wit_8.
Proof.
  unfold circular_shift_entail_wit_8.
  intros. pre_process.
  Exists out_l_2.
  entailer!.
  rewrite H4.
  apply Zlength_nonneg.
Qed. 

Lemma proof_of_circular_shift_entail_wit_9 : circular_shift_entail_wit_9.
Proof.
  unfold circular_shift_entail_wit_9.
  intros. pre_process.
  Exists out_l_2.
  assert (1 <= fill).
  { eapply (base_fill_full_state_positive_digits x_pre 10 tmp fill out_l_2);
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
  - apply base_fill_full_state_step_10; try lia; assumption.
  - rewrite Zlength_replace_Znth_44; lia.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_circular_shift_entail_wit_11 : circular_shift_entail_wit_11.
Proof.
  unfold circular_shift_entail_wit_11.
  intros. pre_process.
  assert (tmp = 0) by lia. subst tmp.
  assert (fill = 0).
  {
    destruct H13 as [suffix [[_ [_ [Hdigits _]]] _]].
    unfold base_digits_pos_z in Hdigits.
    replace (0 <=? 0)%Z with true in Hdigits by (symmetry; apply Z.leb_le; lia).
    change (Zlength (@nil Z)) with 0 in Hdigits.
    lia.
  }
  subst fill.
  Exists (base_digits_z x_pre 10).
  assert (out_l_2 = base_digits_z x_pre 10).
  { eapply base_fill_full_state_done; eassumption. }
  subst out_l_2.
  rewrite base_digits_z_10_decimal_digits_z by lia.
  entailer!.
Qed. 

Lemma proof_of_circular_shift_entail_wit_12_2 : circular_shift_entail_wit_12_2.
Proof.
  unfold circular_shift_entail_wit_12_2.
  intros. pre_process.
  subst out_l.
  rewrite H11.
  entailer!.
  rewrite H9, H4.
  pose proof (Zlength_nonneg (decimal_digits_z x_pre)).
  lia.
Qed. 

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
  rewrite H9.
  apply Zlength_nonneg.
Qed. 

Lemma proof_of_circular_shift_entail_wit_14 : circular_shift_entail_wit_14.
Proof.
  unfold circular_shift_entail_wit_14.
  intros. pre_process.
  rewrite app_Znth1 by lia.
  replace ((n - 1) - i) with (Zlength (decimal_digits_z x_pre) - 1 - i) by lia.
  rewrite <- (circular_shift_output_z_reverse_char x_pre shift_pre i) by lia.
  Exists (app out_l_2 (cons (Znth i (circular_shift_output_z x_pre shift_pre) 0) nil)).
  assert (Hprefix :
    circular_shift_prefix_z x_pre shift_pre (i + 1)
      (app out_l_2 (cons (Znth i (circular_shift_output_z x_pre shift_pre) 0) nil))).
  { apply circular_shift_prefix_z_snoc; auto; try lia.
    rewrite circular_shift_output_z_length by lia. lia. }
  assert (Hlen :
    Zlength (app out_l_2 (cons (Znth i (circular_shift_output_z x_pre shift_pre) 0) nil)) =
    i + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  entailer!.
Qed. 

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

Lemma proof_of_circular_shift_entail_wit_16_1 : circular_shift_entail_wit_16_1.
Proof.
  unfold circular_shift_entail_wit_16_1.
  intros. pre_process.
  Exists out_l_2.
  assert ((((n - shift_pre) + i) - n) = Z.rem ((n - shift_pre) + i) n).
  { apply Z.rem_unique with (q := 1); lia. }
  entailer!.
Qed. 

Lemma proof_of_circular_shift_entail_wit_16_2 : circular_shift_entail_wit_16_2.
Proof.
  unfold circular_shift_entail_wit_16_2.
  intros. pre_process.
  Exists out_l_2.
  assert (((n - shift_pre) + i) = Z.rem ((n - shift_pre) + i) n).
  { symmetry. apply Z.rem_small. lia. }
  entailer!.
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
    with ((Zlength (decimal_digits_z x_pre) - shift_pre + i) mod
          Zlength (decimal_digits_z x_pre)) by (subst n; reflexivity).
  rewrite <- (circular_shift_output_z_rot_char x_pre shift_pre i) by lia.
  Exists (app out_l_2 (cons (Znth i (circular_shift_output_z x_pre shift_pre) 0) nil)).
  assert (Hprefix :
    circular_shift_prefix_z x_pre shift_pre (i + 1)
      (app out_l_2 (cons (Znth i (circular_shift_output_z x_pre shift_pre) 0) nil))).
  { apply circular_shift_prefix_z_snoc; auto; try lia.
    rewrite circular_shift_output_z_length by lia. lia. }
  assert (Hlen :
    Zlength (app out_l_2 (cons (Znth i (circular_shift_output_z x_pre shift_pre) 0) nil)) =
    i + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  entailer!.
Qed. 

Lemma proof_of_circular_shift_entail_wit_18_1 : circular_shift_entail_wit_18_1.
Proof.
  unfold circular_shift_entail_wit_18_1.
  intros. pre_process.
  assert (Hi : i = n) by lia.
  subst i.
  Exists out_l_2.
  assert (Heqout : out_l_2 = circular_shift_output_z x_pre shift_pre).
  { apply circular_shift_prefix_z_full; try lia.
    replace (Zlength (decimal_digits_z x_pre)) with (Zlength out_l_2) by lia.
    exact H12. }
  replace (Zlength out_l_2) with n in * by lia.
  entailer!.
Qed. 

Lemma proof_of_circular_shift_entail_wit_18_2 : circular_shift_entail_wit_18_2.
Proof.
  unfold circular_shift_entail_wit_18_2.
  intros. pre_process.
  assert (Hi : i = n) by lia.
  subst i.
  Exists out_l_2.
  assert (Heqout : out_l_2 = circular_shift_output_z x_pre shift_pre).
  { apply circular_shift_prefix_z_full; try lia.
    replace (Zlength (decimal_digits_z x_pre)) with (Zlength out_l_2) by lia.
    exact H11. }
  replace (Zlength out_l_2) with n in * by lia.
  entailer!.
Qed. 

Lemma proof_of_circular_shift_return_wit_1 : circular_shift_return_wit_1.
Proof.
  unfold circular_shift_return_wit_1.
  intros. pre_process.
  Exists buf out_l_2 n.
  rewrite (CharArray.undef_seg_empty out (n + 1)).
  entailer!.
  - rewrite <- H8.
    entailer!.
  - rewrite H11.
    apply problem_65_spec_z_intro; lia.
  - rewrite <- H11.
    lia.
Qed. 

Lemma proof_of_circular_shift_partial_solve_wit_6_pure : circular_shift_partial_solve_wit_6_pure.
Proof.
  unfold circular_shift_partial_solve_wit_6_pure.
  intros. pre_process. entailer!.
  pose proof (Zlength_nonneg (decimal_digits_z x_pre)).
  lia.
Qed. 
