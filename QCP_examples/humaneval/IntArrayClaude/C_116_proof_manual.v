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
From SimpleC.EE Require Import C_116_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_116.
Local Open Scope sac.

Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof. pre_process. Qed.

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof. pre_process. Qed.

Lemma proof_of_sort_array_safety_wit_14 : sort_array_safety_wit_14.
Proof.
  pre_process.
  entailer!.
  all: rewrite Z.rem_mod_nonneg by lia.
  all: pose proof (Z.mod_pos_bound n 2 ltac:(lia)).
  all: lia.
Qed.

Lemma proof_of_sort_array_entail_wit_1 : sort_array_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  apply sort_copy_prefix_116_init.
Qed.

Lemma proof_of_sort_array_entail_wit_2 : sort_array_entail_wit_2.
Proof.
  pre_process.
  Exists (output_l_2 ++ Znth i input_l 0 :: nil).
  sep_apply (IntArray.seg_single data i (Znth i input_l 0)).
  sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)); [ | lia].
  entailer!.
  - eapply sort_copy_prefix_116_step; eauto; lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_sort_array_entail_wit_4 : sort_array_entail_wit_4.
Proof.
  pre_process.
  assert (i = arr_size_pre) by lia.
  subst i.
  pose proof (sort_copy_prefix_116_final (Zlength output_l) input_l output_l H10 ltac:(lia)) as Hout.
  subst output_l.
  rewrite H11 in *.
  rewrite (IntArray.undef_seg_empty data arr_size_pre).
  sep_apply (IntArray.seg_to_full data 0 arr_size_pre).
  replace (data + 0 * sizeof(INT)) with data by lia.
  replace (arr_size_pre - 0) with arr_size_pre by lia.
  entailer!.
Qed.

Lemma proof_of_sort_array_entail_wit_5 : sort_array_entail_wit_5.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  apply sort_score_prefix_116_init.
Qed.

Lemma proof_of_sort_array_entail_wit_7 : sort_array_entail_wit_7.
Proof.
  pre_process.
  Exists score_l_2.
  entailer!.
Qed.

Lemma proof_of_sort_array_entail_wit_8 : sort_array_entail_wit_8.
Proof.
  pre_process.
  Exists score_l_2.
  pose proof (sort_array_116_int_range_at input_l i H8 ltac:(lia)) as Hrange.
  subst b.
  subst n.
  unfold Zabs.
  rewrite Z.abs_eq by lia.
  entailer!.
  eapply bit_count_state_at_116_init; eauto; lia.
Qed.

Lemma proof_of_sort_array_entail_wit_9 : sort_array_entail_wit_9.
Proof.
  pre_process.
  Exists score_l_2.
  pose proof (bit_count_state_at_116_step i input_l n b ltac:(assumption) ltac:(lia)) as Hstep.
  unfold bit_count_state_at_116, bit_count_state_116 in Hstep.
  destruct Hstep as [Hx2 [Hn2 [Hb2 Hfuel]]].
  entailer!.
  unfold bit_count_state_at_116, bit_count_state_116.
  repeat split; try lia.
  exact Hfuel.
Qed.

Lemma proof_of_sort_array_entail_wit_10 : sort_array_entail_wit_10.
Proof.
  pre_process.
  Exists (score_l_2 ++ b :: nil).
  sep_apply (IntArray.seg_single bin i b).
  sep_apply (IntArray.seg_merge_to_seg bin 0 i (i + 1)); [ | lia].
  entailer!.
  - eapply sort_score_prefix_116_step.
    + eauto.
    + lia.
    + eapply bit_count_state_at_116_final; eauto.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_sort_array_entail_wit_12 : sort_array_entail_wit_12.
Proof.
  pre_process.
  assert (i = arr_size_pre) by lia.
  subst i.
  Exists score_l_2 input_l.
  rewrite H12 in *.
  rewrite (IntArray.undef_seg_empty bin arr_size_pre).
  sep_apply (IntArray.seg_to_full bin 0 arr_size_pre).
  replace (bin + 0 * sizeof(INT)) with bin by lia.
  replace (arr_size_pre - 0) with arr_size_pre by lia.
  entailer!.
  eapply sort_outer_state_116_init.
  - apply sort_copy_prefix_116_self.
  - rewrite <- H5. exact H11.
Qed.

Lemma proof_of_sort_array_entail_wit_13 : sort_array_entail_wit_13.
Proof.
  pre_process.
  Exists score_l_2 output_l_2.
  entailer!.
  eapply sort_inner_state_116_init; eauto; lia.
Qed.

Lemma proof_of_sort_array_entail_wit_14 : sort_array_entail_wit_14.
Proof.
  pre_process.
  assert (j = arr_size_pre) by lia.
  subst j.
  Exists score_l_2 output_l_2.
  entailer!.
  replace arr_size_pre with (Zlength input_l) in H14 by lia.
  eapply sort_outer_state_116_step; eauto; lia.
Qed.

Lemma proof_of_sort_array_entail_wit_15_1 : sort_array_entail_wit_15_1.
Proof.
  pre_process.
  Exists (replace_Znth (j - 1) (Znth j score_l_2 0)
            (replace_Znth j (Znth (j - 1) score_l_2 0) score_l_2))
         (replace_Znth (j - 1) (Znth j output_l_2 0)
            (replace_Znth j (Znth (j - 1) output_l_2 0) output_l_2)).
  entailer!.
  - eapply sort_inner_state_116_step_swap; eauto; try lia.
  - repeat rewrite replace_Znth_length_116; lia.
  - repeat rewrite replace_Znth_length_116; lia.
Qed.

Lemma proof_of_sort_array_entail_wit_15_2 : sort_array_entail_wit_15_2.
Proof.
  pre_process.
  Exists (replace_Znth (j - 1) (Znth j score_l_2 0)
            (replace_Znth j (Znth (j - 1) score_l_2 0) score_l_2))
         (replace_Znth (j - 1) (Znth j output_l_2 0)
            (replace_Znth j (Znth (j - 1) output_l_2 0) output_l_2)).
  entailer!.
  - eapply sort_inner_state_116_step_swap; eauto; try lia.
  - repeat rewrite replace_Znth_length_116; lia.
  - repeat rewrite replace_Znth_length_116; lia.
Qed.

Lemma proof_of_sort_array_entail_wit_15_3 : sort_array_entail_wit_15_3.
Proof.
  pre_process.
  Exists score_l_2 output_l_2.
  entailer!.
  eapply sort_inner_state_116_step_keep; eauto.
  - lia.
  - intro Hbad.
    destruct Hbad as [Hbad | [Hbad1 Hbad2]]; lia.
Qed.

Lemma proof_of_sort_array_entail_wit_15_4 : sort_array_entail_wit_15_4.
Proof.
  pre_process.
  Exists score_l_2 output_l_2.
  entailer!.
  eapply sort_inner_state_116_step_keep; eauto.
  - lia.
  - intro Hbad.
    destruct Hbad as [Hbad | [Hbad1 Hbad2]]; lia.
Qed.

Lemma proof_of_sort_array_entail_wit_17 : sort_array_entail_wit_17.
Proof.
  pre_process.
  assert (i = arr_size_pre) by lia.
  subst i.
  Exists score_l_2 output_l_2.
  entailer!.
  replace arr_size_pre with (Zlength input_l) in H12 by lia.
  eapply sort_outer_state_116_final_spec; eauto.
Qed.

Lemma proof_of_sort_array_partial_solve_wit_7_pure : sort_array_partial_solve_wit_7_pure.
Proof.
  pre_process.
  pose proof (sort_array_116_int_range_at input_l i ltac:(assumption) ltac:(lia)).
  entailer!.
Qed.
