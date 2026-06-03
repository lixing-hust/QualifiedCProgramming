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
From SimpleC.EE Require Import C_44_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_44.
Local Open Scope sac.

Lemma proof_of_change_base_safety_wit_19 : change_base_safety_wit_19.
Proof.
  unfold change_base_safety_wit_19.
  intros.
  pre_process.
  assert (total <= x_pre) by
    (subst total; apply base_digits_z_length_pos_le; lia).
  entailer!.
Qed. 

Lemma proof_of_change_base_safety_wit_23 : change_base_safety_wit_23.
Proof.
  unfold change_base_safety_wit_23.
  intros.
  pre_process.
  pose proof (Z.rem_bound_pos x base_pre ltac:(lia) ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_change_base_entail_wit_1 : change_base_entail_wit_1.
Proof.
  unfold change_base_entail_wit_1.
  intros.
  pre_process.
  pose proof (base_count_state_init x_pre base_pre ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_change_base_entail_wit_2 : change_base_entail_wit_2.
Proof.
  unfold change_base_entail_wit_2.
  intros.
  pre_process.
  assert (Htpos : 0 < t) by lia.
  pose proof (base_count_state_step _ _ _ _ Htpos H2 H10).
  replace (t ÷ base_pre) with (t / base_pre)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  assert (Hdigits_lt : digits + 1 < INT_MAX).
  {
    unfold base_count_state_z in H10.
    destruct H10 as [_ [_ Hlen]].
    rewrite (base_digits_pos_step t base_pre) in Hlen by lia.
    rewrite Zlength_app in Hlen.
    change (Zlength (cons (48 + t mod base_pre) nil)) with 1 in Hlen.
    unfold base_digits_pos_z in Hlen.
    replace ((x_pre <=? 0)%Z) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
    pose proof (base_digits_z_length_pos_le x_pre base_pre H0 H2).
    pose proof (Zlength_nonneg
      (if (t / base_pre <=? 0)%Z
       then nil
       else base_digits_z (t / base_pre) base_pre)).
    lia.
  }
  entailer!.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_change_base_entail_wit_3 : change_base_entail_wit_3.
Proof.
  unfold change_base_entail_wit_3.
  intros.
  pre_process.
  assert (t = 0) by lia; subst t.
  pose proof (base_count_state_done _ _ _ H1 H11) as Hdigits.
  subst digits.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (Zlength (base_digits_z x_pre base_pre) + 1)).
  rewrite (CharArray.full_empty retval 0).
  rewrite (CharArray.undef_seg_empty retval 0).
  entailer!.
  lia.
Qed. 

Lemma proof_of_change_base_entail_wit_4 : change_base_entail_wit_4.
Proof.
  unfold change_base_entail_wit_4.
  intros.
  pre_process.
  rewrite repeat_Z_tail by lia.
  entailer!.
Qed. 

Lemma proof_of_change_base_entail_wit_5 : change_base_entail_wit_5.
Proof.
  unfold change_base_entail_wit_5.
  intros.
  pre_process.
  assert (i = total + 1) by lia; subst i.
  rewrite (CharArray.undef_seg_empty out (total + 1)).
  Exists (repeat_Z 0 total).
  rewrite repeat_Z_tail by (subst total; apply Zlength_nonneg).
  entailer!.
  - subst digits total.
    apply base_fill_full_state_init; lia.
  - rewrite Zlength_repeat_Z; [lia | subst total; apply Zlength_nonneg].
Qed. 

Lemma proof_of_change_base_entail_wit_6 : change_base_entail_wit_6.
Proof.
  unfold change_base_entail_wit_6.
  intros.
  pre_process.
  Exists out_l_2.
  entailer!.
  subst digits total. apply Zlength_nonneg.
Qed. 

Lemma proof_of_change_base_entail_wit_7 : change_base_entail_wit_7.
Proof.
  unfold change_base_entail_wit_7.
  intros.
  pre_process.
  Exists out_l_2.
  assert (Hxpos : 0 < x) by lia.
  pose proof (base_fill_full_state_positive_digits _ _ _ _ _ Hxpos H2 H11).
  replace (digits - 1 + 1) with digits by lia.
  entailer!.
Qed. 

Lemma proof_of_change_base_entail_wit_8 : change_base_entail_wit_8.
Proof.
  unfold change_base_entail_wit_8.
  intros.
  pre_process.
  replace (x ÷ base_pre) with (x / base_pre)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace (Z.rem x base_pre) with (x mod base_pre)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  Exists (replace_Znth digits (signed_last_nbits (48 + x mod base_pre) 8) out_l_2).
  rewrite replace_Znth_app_l by lia.
  entailer!.
  - apply base_fill_full_state_step; lia || assumption.
  - rewrite Zlength_replace_Znth_44 by lia. lia.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_change_base_return_wit_1 : change_base_return_wit_1.
Proof.
  unfold change_base_return_wit_1.
  intros.
  pre_process.
  assert (x = 0) by lia; subst x.
  destruct H11 as [suffix [[_ [_ [Hdigits Hsplit]]] Hout]].
  unfold base_digits_pos_z in Hdigits.
  replace (Z.leb 0 0) with true in Hdigits by (symmetry; apply Z.leb_le; lia).
  simpl in Hdigits. subst digits.
  simpl in Hsplit. subst suffix.
  unfold repeat_Z in Hout. simpl in Hout. subst out_l_2.
  Exists (base_digits_z x_pre base_pre) (Zlength (base_digits_z x_pre base_pre)).
  entailer!.
  - rewrite H10. entailer!.
  - apply problem_44_spec_z_intro; [lia | lia | reflexivity].
  - pose proof (base_digits_z_length_pos_le x_pre base_pre ltac:(lia) ltac:(lia)).
    lia.
  - pose proof (base_digits_z_nonempty x_pre base_pre) as Hnonempty.
    destruct (base_digits_z x_pre base_pre) eqn:Hbd; [contradiction | idtac].
    rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
Qed. 

Lemma proof_of_change_base_return_wit_2 : change_base_return_wit_2.
Proof.
  unfold change_base_return_wit_2.
  intros.
  pre_process.
  subst x_pre.
  Exists ((48 :: nil) : list Z) 1.
  rewrite (CharArray.undef_seg_empty retval 2).
  entailer!.
  - change (((48 :: nil) ++ 0 :: nil)) with (48 :: 0 :: nil).
    rewrite (CharArray.full_unfold retval (1 + 1) (0 :: nil) 48).
    rewrite (CharArray.seg_unfold retval 1 (1 + 1) nil 0).
    rewrite (CharArray.seg_empty retval 2 2).
    entailer!.
  - apply problem_44_spec_z_zero; lia.
Qed. 
