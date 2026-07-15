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
Require Import C_84_goal.
Require Import C_84_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_84.
Local Open Scope sac.

Ltac solve_84_pures :=
  unfold binary_count_state_z_84, binary_backfill_state_z_84,
    digit_sum_state_z_84, binary_safe_84, solve_safe_84 in *;
  simpl in *;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end;
  try lia.

Lemma proof_of_to_binary_string_safety_wit_10 : to_binary_string_safety_wit_10.
Proof.
  left; pre_process; entailer!; solve_84_pures.
Qed.

Lemma proof_of_to_binary_string_safety_wit_20 : to_binary_string_safety_wit_20.
Proof.
  left; intros.
  assert (0 <= Z.rem num 2 < 2) by (apply Z.rem_bound_pos; lia).
  entailer!.
Qed.

Lemma proof_of_to_binary_string_entail_wit_1 : to_binary_string_entail_wit_1.
Proof.
  left; intros; entailer!; solve_84_pures.
Qed.

Lemma proof_of_to_binary_string_entail_wit_2 : to_binary_string_entail_wit_2.
Proof.
  left; intros; entailer!.
  - unfold binary_safe_84 in PreH7.
    destruct PreH7 as (_ & _ & _ & _ & Hstep & _ & _ & _ & _ & _ & _).
    eapply Hstep; eauto; lia.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_to_binary_string_entail_wit_3 : to_binary_string_entail_wit_3.
Proof.
  left; intros.
  assert (x = 0) by lia; subst x.
  pose proof PreH7 as Hsafe.
  unfold binary_safe_84 in PreH7.
  destruct PreH7 as (_ & Hlen & _ & _ & _ & Hzero & Hpos & _ & _ & _ & _).
  pose proof (Hzero bits PreH2 PreH8) as Hbits; subst bits.
  pose proof (Hpos (binary_length_z_84 num_pre) PreH2 eq_refl) as Hpos'.
  entailer!.
Qed.

Lemma proof_of_to_binary_string_entail_wit_4 : to_binary_string_entail_wit_4.
Proof.
  left; intros.
  pose proof PreH8 as Hsafe.
  unfold binary_safe_84 in PreH8.
  destruct PreH8 as (_ & _ & _ & _ & _ & _ & _ & Hinit & _ & _ & _).
  pose proof (Hinit bits PreH2 PreH5) as Hbf.
  entailer!.
  rewrite derivable1_sepcon_comm.
  apply derivable1_sepcon_mono.
  - change (CharArray.undef_missing_i retval bits 0 (bits + 1) |--
            CharArray.undef_seg retval 0 bits).
    pose proof (CharArray.undef_missing_i_to_undef_seg_tail retval 0 (bits + 1)) as Hm.
    replace (bits + 1 - 1) with bits in Hm by lia.
    apply Hm; lia.
  - apply CharArray.seg_single.
Qed.

Lemma proof_of_to_binary_string_entail_wit_5 : to_binary_string_entail_wit_5.
Proof.
  left; intros.
  subst x bits.
  Exists (cons 0 nil).
  entailer!.
  change (1 = binary_length_z_84 num_pre + 1 - binary_length_z_84 num_pre).
  ring.
Qed.

Lemma proof_of_to_binary_string_entail_wit_6 : to_binary_string_entail_wit_6.
Proof.
  left; intros.
  pose proof PreH10 as Hsafe.
  unfold binary_safe_84 in PreH10.
  destruct PreH10 as (_ & _ & _ & _ & _ & _ & _ & _ & Hstep & _ & _).
  assert (Hnum_pos : 0 < num) by lia.
  pose proof (Hstep num bits suffix_2 PreH11 Hnum_pos) as (Hbits & _).
  Exists suffix_2.
  entailer!.
Qed.

Lemma proof_of_to_binary_string_entail_wit_7 : to_binary_string_entail_wit_7.
Proof.
  left; intros.
  pose proof PreH9 as Hsafe.
  unfold binary_safe_84 in PreH9.
  destruct PreH9 as (_ & _ & _ & _ & _ & _ & _ & _ & Hstep & _ & _).
  pose proof (Hstep num bits suffix_2 PreH10 PreH1) as (_ & Hchar & Hnext).
  Exists suffix_2.
  entailer!.
  - rewrite (signed_last_nbits_eq (48 + num % 2) 8) by lia.
    sep_apply_l_atomic (CharArray.seg_single out (bits - 1) (48 + num % 2)).
    replace (bits - 1 + 1) with bits by lia.
    sep_apply_l_atomic (CharArray.undef_missing_i_to_undef_seg_tail out 0 bits).
    + entailer!.
    + replace (bits + 0 - 1) with (bits - 1) by lia.
      cancel (CharArray.undef_seg out 0 (bits - 1)).
      sep_apply_l_atomic (CharArray.seg_merge_to_seg
        out (bits - 1) bits (binary_length_z_84 num_pre + 1)
        (48 + num % 2 :: nil) suffix_2).
      * entailer!.
      * simpl; entailer!.
  - rewrite Zlength_cons; lia.
Qed.

Lemma proof_of_to_binary_string_entail_wit_8 : to_binary_string_entail_wit_8.
Proof.
  left; intros.
  Exists (cons (48 + num % 2) suffix_2).
  assert (Hquot_nonneg : 0 <= num ÷ 2) by (apply Z.quot_pos; lia).
  assert (Hquot_le : num ÷ 2 <= num_pre).
  {
    eapply Z.quot_le_upper_bound; try lia.
  }
  entailer!.
Qed.

Lemma proof_of_to_binary_string_entail_wit_9 : to_binary_string_entail_wit_9.
Proof.
  left; intros.
  assert (Hnum0 : num = 0) by lia.
  subst num.
  pose proof PreH11 as Hbf.
  unfold binary_backfill_state_z_84 in Hbf.
  destruct Hbf as (_ & _ & _ & _ & _ & Hexit_pos & _).
  pose proof (Hexit_pos eq_refl) as Hbits0.
  subst bits.
  pose proof PreH10 as Hsafe.
  unfold binary_safe_84 in PreH10.
  destruct PreH10 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdone & Hlen).
  pose proof (Hdone suffix_2 PreH11) as Hsuffix.
  subst suffix_2.
  Exists (app (binary_output_z_84 num_pre) (0 :: nil)).
  entailer!.
  rewrite (CharArray.undef_seg_empty out 0).
  entailer!.
Qed.

Lemma proof_of_to_binary_string_return_wit_1 : to_binary_string_return_wit_1.
Proof.
  left; intros.
  subst suffix.
  pose proof PreH7 as Hsafe.
  unfold binary_safe_84 in Hsafe.
  destruct Hsafe as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen).
  pose proof (Hlen (binary_output_z_84 num_pre) eq_refl) as Hout_len.
  Exists (binary_output_z_84 num_pre) (binary_length_z_84 num_pre).
  entailer!.
Qed.

Lemma proof_of_to_binary_string_return_wit_2 : to_binary_string_return_wit_2.
Proof.
  left; intros.
  subst num_pre.
  pose proof PreH5 as Hsafe.
  unfold binary_safe_84 in Hsafe.
  destruct Hsafe as (_ & _ & Hzero & _ & _ & _ & _ & _ & _ & _ & Hlen).
  pose proof (Hlen (binary_output_z_84 0) eq_refl) as Hout_len.
  Exists (binary_output_z_84 0) (binary_length_z_84 0).
  rewrite Hzero in *.
  entailer!.
  rewrite (CharArray.undef_seg_empty retval 2).
  sep_apply_l_atomic (CharArray.seg_single retval 1 0).
  sep_apply_l_atomic (CharArray.seg_single retval 0 48).
  sep_apply_l_atomic (CharArray.seg_merge_to_seg
    retval 0 1 2 (48 :: nil) (0 :: nil)).
  - entailer!.
  - simpl.
    sep_apply_l_atomic (CharArray.seg_to_full retval 0 2 (48 :: 0 :: nil)).
    replace (retval + 0 * sizeof(CHAR)) with retval by lia.
    replace (2 - 0) with 2 by lia.
    entailer!.
Qed.

Lemma proof_of_solve_safety_wit_3 : solve_safety_wit_3.
Proof.
  left; intros.
  assert (0 <= N % 10 < 10) by (apply Z.rem_bound_pos; lia).
  unfold digit_sum_state_z_84 in PreH10.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  entailer!.
Qed.

Lemma proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Proof.
  left; intros.
  pose proof PreH4 as Hsafe.
  unfold solve_safe_84 in PreH4.
  destruct PreH4 as (_ & Hinit & _).
  entailer!.
Qed.

Lemma proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Proof.
  left; intros.
  pose proof PreH9 as Hsafe.
  unfold solve_safe_84 in PreH9.
  destruct PreH9 as (_ & _ & Hstep & _ & _).
  assert (HN_pos : 0 < N) by lia.
  pose proof (Hstep N sum PreH10 HN_pos) as (Hsum_bounds & Hstate).
  assert (Hquot_nonneg : 0 <= N ÷ 10) by (apply Z.quot_pos; lia).
  assert (Hquot_le : N ÷ 10 <= N_pre).
  {
    eapply Z.quot_le_upper_bound; try lia.
  }
  entailer!.
Qed.

Lemma proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Proof.
  left; intros.
  assert (HN0 : N = 0) by lia.
  subst N.
  pose proof PreH9 as Hsafe.
  unfold solve_safe_84 in PreH9.
  destruct PreH9 as (_ & _ & _ & Hdone & _).
  pose proof (Hdone sum PreH10) as (Hsum & Hbin).
  entailer!.
Qed.

Lemma proof_of_solve_return_wit_1 : solve_return_wit_1.
Proof.
  left; intros.
  pose proof PreH10 as Hsafe.
  unfold solve_safe_84 in Hsafe.
  destruct Hsafe as (_ & _ & _ & _ & Hspec).
  pose proof (Hspec sum out_l_2 PreH11 PreH3) as Hproblem.
  Exists out_l_2 len_2.
  entailer!.
Qed.

Lemma proof_of_solve_partial_solve_wit_1_pure : solve_partial_solve_wit_1_pure.
Proof.
  left; intros.
  pose proof PreH9 as Hbin.
  unfold binary_safe_84 in Hbin.
  destruct Hbin as (_ & Hlen_bound & _).
  entailer!.
Qed.
