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
From SimpleC.EE Require Import C_103_goal.
From SimpleC.EE Require Import C_103_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_103.
Local Open Scope sac.

Lemma proof_of_to_binary_string_safety_wit_10 : to_binary_string_safety_wit_10.
Proof.
  left; pre_process; entailer!.
  pose proof (binary_safe_length_bound_103 num_pre PreH7) as Hlen.
  unfold binary_count_state_z_103 in PreH8.
  destruct PreH8 as (_ & _ & Hcount).
  pose proof (Zlength_nonneg (binary_bits_pos_z_103 x)).
  assert (Hlen_eq : binary_length_z_103 num_pre =
                    Zlength (binary_bits_pos_z_103 num_pre)).
  {
    unfold binary_length_z_103, binary_output_z_103,
      binary_bits_z_103, binary_bits_pos_z_103.
    destruct num_pre; try lia; simpl.
    rewrite !Zlength_correct, length_map, length_rev.
    reflexivity.
  }
  entailer!.
Qed.

Lemma proof_of_to_binary_string_safety_wit_14 : to_binary_string_safety_wit_14.
Proof.
  left; pre_process; entailer!.
  pose proof (binary_safe_length_bound_103 num_pre PreH7).
  entailer!.
Qed.

Lemma proof_of_to_binary_string_safety_wit_20 : to_binary_string_safety_wit_20.
Proof.
  left; intros.
  pose proof (Z.rem_bound_pos num 2 ltac:(lia) ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_to_binary_string_entail_wit_1 : to_binary_string_entail_wit_1.
Proof.
  left; intros.
  pose proof (binary_safe_count_initial_103 num_pre PreH4).
  entailer!.
Qed.

Lemma proof_of_to_binary_string_entail_wit_2 : to_binary_string_entail_wit_2.
Proof.
  left; intros.
  pose proof (binary_safe_count_step_103
    num_pre x bits PreH7 PreH8 ltac:(lia)) as Hstep.
  assert (0 <= x ÷ 2) by (apply Z.quot_pos; lia).
  entailer!.
Qed.

Lemma proof_of_to_binary_string_entail_wit_3 : to_binary_string_entail_wit_3.
Proof.
  left; intros.
  assert (x = 0) by lia; subst x.
  pose proof (binary_safe_count_final_103
    num_pre bits PreH7 PreH2 PreH8) as Hbits.
  pose proof (binary_safe_length_pos_103
    num_pre bits PreH7 PreH2 Hbits) as Hpos.
  entailer!.
Qed.

Lemma proof_of_to_binary_string_entail_wit_4 : to_binary_string_entail_wit_4.
Proof.
  left; intros.
  pose proof (binary_safe_backfill_initial_103
    num_pre bits PreH8 PreH2 PreH5) as Hstate.
  entailer!.
  rewrite derivable1_sepcon_comm.
  apply derivable1_sepcon_mono.
  - change (CharArray.undef_missing_i retval bits 0 (bits + 1) |--
            CharArray.undef_seg retval 0 bits).
    pose proof (CharArray.undef_missing_i_to_undef_seg_tail
      retval 0 (bits + 1)) as Htail.
    replace (bits + 1 - 1) with bits in Htail by lia.
    apply Htail; lia.
  - apply CharArray.seg_single.
Qed.

Lemma proof_of_to_binary_string_entail_wit_5 : to_binary_string_entail_wit_5.
Proof.
  left; intros.
  subst x bits.
  Exists (cons 0 nil).
  entailer!.
  change (1 = binary_length_z_103 num_pre + 1 -
              binary_length_z_103 num_pre).
  ring.
Qed.

Lemma proof_of_to_binary_string_entail_wit_6 : to_binary_string_entail_wit_6.
Proof.
  left; intros.
  pose proof (binary_safe_backfill_step_103
    num_pre num bits suffix_2 PreH10 PreH11 ltac:(lia)) as (Hbits & _).
  Exists suffix_2.
  entailer!.
Qed.

Lemma proof_of_to_binary_string_entail_wit_7 : to_binary_string_entail_wit_7.
Proof.
  left; intros.
  pose proof (binary_safe_backfill_step_103
    num_pre num bits suffix_2 PreH9 PreH10 PreH1)
    as (_ & Hchar & Hnext).
  Exists suffix_2.
  entailer!.
  - rewrite (signed_last_nbits_eq (48 + num % 2) 8) by lia.
    sep_apply_l_atomic (CharArray.seg_single out (bits - 1)
      (48 + num % 2)).
    replace (bits - 1 + 1) with bits by lia.
    sep_apply_l_atomic
      (CharArray.undef_missing_i_to_undef_seg_tail out 0 bits).
    + entailer!.
    + replace (bits + 0 - 1) with (bits - 1) by lia.
      cancel (CharArray.undef_seg out 0 (bits - 1)).
      sep_apply_l_atomic (CharArray.seg_merge_to_seg
        out (bits - 1) bits (binary_length_z_103 num_pre + 1)
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
  { eapply Z.quot_le_upper_bound; lia. }
  entailer!.
Qed.

Lemma proof_of_to_binary_string_entail_wit_9 : to_binary_string_entail_wit_9.
Proof.
  left; intros.
  assert (Hnum0 : num = 0) by lia; subst num.
  pose proof (binary_backfill_zero_pos_103
    num_pre bits suffix_2 PreH11) as Hbits; subst bits.
  pose proof (binary_safe_backfill_final_103
    num_pre suffix_2 PreH10 PreH11) as Hsuffix; subst suffix_2.
  Exists (app (binary_output_z_103 num_pre) (0 :: nil)).
  entailer!.
  rewrite (CharArray.undef_seg_empty out 0).
  entailer!.
Qed.

Lemma proof_of_to_binary_string_return_wit_1 : to_binary_string_return_wit_1.
Proof.
  left; intros.
  subst suffix.
  Exists (binary_output_z_103 num_pre) (binary_length_z_103 num_pre).
  unfold binary_length_z_103.
  entailer!.
Qed.

Lemma proof_of_to_binary_string_return_wit_2 : to_binary_string_return_wit_2.
Proof.
  left; intros.
  subst num_pre.
  pose proof (binary_safe_zero_output_103 0 PreH5 eq_refl) as Hzero.
  Exists (binary_output_z_103 0) (binary_length_z_103 0).
  rewrite Hzero in *.
  entailer!.
  rewrite (CharArray.undef_seg_empty retval 2).
  sep_apply_l_atomic (CharArray.seg_single retval 1 0).
  sep_apply_l_atomic (CharArray.seg_single retval 0 48).
  sep_apply_l_atomic (CharArray.seg_merge_to_seg
    retval 0 1 2 (48 :: nil) (0 :: nil)).
  - entailer!.
  - simpl.
    sep_apply_l_atomic
      (CharArray.seg_to_full retval 0 2 (48 :: 0 :: nil)).
    replace (retval + 0 * sizeof(CHAR)) with retval by lia.
    replace (2 - 0) with 2 by lia.
    entailer!.
Qed.

Lemma proof_of_to_binary_string_partial_solve_wit_4_pure :
  to_binary_string_partial_solve_wit_4_pure.
Proof.
  left; intros.
  pose proof (binary_safe_length_bound_103 num_pre PreH7).
  entailer!.
Qed.

Lemma proof_of_rounded_avg_return_wit_1 : rounded_avg_return_wit_1.
Proof.
  left; intros.
  replace (m_pre + n_pre) with (n_pre + m_pre) in * by lia.
  pose proof (rounded_avg_safe_use_103
    n_pre m_pre PreH11 PreH4) as Hsafe.
  cbn in Hsafe.
  destruct Hsafe as (Havg & Hdiv & Hbinary).
  subst out_l_2.
  pose proof (problem_103_spec_z_binary
    n_pre m_pre ((n_pre + m_pre) ÷ 2)
    PreH4 ltac:(lia) Hdiv) as Hspec.
  Exists (binary_output_z_103 ((n_pre + m_pre) ÷ 2)) len_2.
  entailer!.
Qed.

Lemma proof_of_rounded_avg_return_wit_2 : rounded_avg_return_wit_2.
Proof.
  left; intros.
  pose proof (problem_103_spec_z_neg n_pre m_pre PreH2) as Hspec.
  Exists (45 :: 49 :: nil) 2.
  entailer!.
  rewrite (CharArray.undef_seg_empty retval 3).
  sep_apply_l_atomic (CharArray.seg_single retval 2 0).
  sep_apply_l_atomic (CharArray.seg_single retval 1 49).
  sep_apply_l_atomic (CharArray.seg_single retval 0 45).
  sep_apply_l_atomic (CharArray.seg_merge_to_seg
    retval 0 1 2 (45 :: nil) (49 :: nil)).
  - entailer!.
  - simpl.
    sep_apply_l_atomic (CharArray.seg_merge_to_seg
      retval 0 2 3 (45 :: 49 :: nil) (0 :: nil)).
    + entailer!.
    + simpl.
      sep_apply_l_atomic
        (CharArray.seg_to_full retval 0 3 (45 :: 49 :: 0 :: nil)).
      replace (retval + 0 * sizeof(CHAR)) with retval by lia.
      replace (3 - 0) with 3 by lia.
      entailer!.
Qed.

Lemma proof_of_rounded_avg_partial_solve_wit_5_pure :
  rounded_avg_partial_solve_wit_5_pure.
Proof.
  left; intros.
  replace (m_pre + n_pre) with (n_pre + m_pre) in * by lia.
  pose proof (rounded_avg_safe_use_103
    n_pre m_pre PreH8 PreH1) as Hsafe.
  cbn in Hsafe.
  destruct Hsafe as (Havg & Hdiv & Hbinary).
  entailer!.
Qed.
