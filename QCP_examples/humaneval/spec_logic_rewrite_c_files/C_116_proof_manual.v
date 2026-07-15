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
From SimpleC.EE Require Import C_116_goal.
From SimpleC.EE Require Import C_116_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_116.
Local Open Scope sac.

Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof.
  pre_process; entailer!.
Qed. 

Lemma proof_of_sort_array_safety_wit_14 : sort_array_safety_wit_14.
Proof.
  pre_process; entailer!;
    pose proof (Z.rem_bound_pos n 2 ltac:(lia) ltac:(lia));
    lia.
Qed. 

Lemma proof_of_sort_array_entail_wit_1 : sort_array_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply (IntArray.undef_full_split_to_undef_seg retval_2 0 arr_size_pre).
  rewrite IntArray.seg_empty.
  rewrite (IntArray.undef_seg_empty retval_2 0).
  entailer!.
  - apply sort_copy_prefix_116_init.
  - lia.
Qed. 

Lemma proof_of_sort_array_entail_wit_2 : sort_array_entail_wit_2.
Proof.
  pre_process.
  Exists (output_l_2 +:: Znth i input_l 0).
  entailer!.
  - apply sort_copy_prefix_116_step; auto; lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed. 

Lemma proof_of_sort_array_entail_wit_4 : sort_array_entail_wit_4.
Proof.
  pre_process.
  assert (Hi_eq : i = arr_size_pre) by lia.
  assert (Hout_eq : output_l = input_l).
  { eapply sort_copy_prefix_116_final; eauto; lia. }
  subst output_l.
  replace i with arr_size_pre by lia.
  rewrite (IntArray.undef_seg_empty data arr_size_pre).
  sep_apply (IntArray.seg_to_full data 0 arr_size_pre input_l).
  replace (data + 0 * sizeof ( INT )) with data by lia.
  replace (arr_size_pre - 0) with arr_size_pre by lia.
  entailer!.
Qed. 

Lemma proof_of_sort_array_entail_wit_5 : sort_array_entail_wit_5.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply (IntArray.undef_full_to_undef_seg retval arr_size_pre).
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
  entailer!.
  - subst n b.
    apply bit_count_state_at_116_init; auto; lia.
  - pose proof (sort_array_116_int_range_at input_l i PreH10 ltac:(lia)).
    subst n.
    rewrite Z.abs_eq by lia.
    lia.
Qed. 

Lemma proof_of_sort_array_entail_wit_9 : sort_array_entail_wit_9.
Proof.
  pre_process.
  Exists score_l_2.
  assert (Hstep : bit_count_state_at_116 i input_l (n ÷ 2) (b + n % 2)).
  { apply bit_count_state_at_116_step; auto. }
  pose proof Hstep as Hstep_bounds.
  unfold bit_count_state_at_116, bit_count_state_116 in Hstep_bounds.
  destruct Hstep_bounds as [_ [[Hn0 Hn1] [[Hb0 Hb1] _]]].
  entailer!.
Qed. 

Lemma proof_of_sort_array_entail_wit_10 : sort_array_entail_wit_10.
Proof.
  pre_process.
  Exists (score_l_2 +:: b).
  assert (Hres : bit_count_result_116 (Znth i input_l 0) b).
  { eapply bit_count_state_at_116_final; eauto. }
  entailer!.
  - apply sort_score_prefix_116_step; auto; lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed. 

Lemma proof_of_sort_array_entail_wit_12 : sort_array_entail_wit_12.
Proof.
  pre_process.
  assert (Hi_eq : i = arr_size_pre) by lia.
  Exists score_l_2. Exists input_l.
  replace i with arr_size_pre by lia.
  rewrite (IntArray.undef_seg_empty bin arr_size_pre).
  sep_apply (IntArray.seg_to_full bin 0 arr_size_pre score_l_2).
  replace (bin + 0 * sizeof ( INT )) with bin by lia.
  replace (arr_size_pre - 0) with arr_size_pre by lia.
  entailer!.
  apply sort_outer_state_116_init.
  - apply sort_copy_prefix_116_self.
  - replace (Zlength input_l) with i by lia.
    exact PreH13.
Qed. 

Lemma proof_of_sort_array_entail_wit_13 : sort_array_entail_wit_13.
Proof.
  pre_process.
  Exists score_l_2. Exists output_l_2.
  entailer!.
  apply sort_inner_state_116_init; auto; lia.
Qed. 

Lemma proof_of_sort_array_entail_wit_14 : sort_array_entail_wit_14.
Proof.
  pre_process.
  assert (Hj_eq : j = arr_size_pre) by lia.
  subst j.
  Exists score_l_2. Exists output_l_2.
  entailer!.
  apply sort_outer_state_116_step.
  - replace (Zlength input_l) with arr_size_pre by lia.
    exact PreH16.
  - lia.
Qed. 

Lemma proof_of_sort_array_entail_wit_15_1 : sort_array_entail_wit_15_1.
Proof.
  pre_process.
  Exists (replace_Znth (j - 1) (Znth j score_l_2 0)
    (replace_Znth j (Znth (j - 1) score_l_2 0) score_l_2)).
  Exists (replace_Znth (j - 1) (Znth j output_l_2 0)
    (replace_Znth j (Znth (j - 1) output_l_2 0) output_l_2)).
  entailer!.
  - apply sort_inner_state_116_step_swap; auto; try lia.
  - repeat rewrite replace_Znth_length_116; lia.
  - repeat rewrite replace_Znth_length_116; lia.
Qed. 

Lemma proof_of_sort_array_entail_wit_15_2 : sort_array_entail_wit_15_2.
Proof.
  pre_process.
  Exists (replace_Znth (j - 1) (Znth j score_l_2 0)
    (replace_Znth j (Znth (j - 1) score_l_2 0) score_l_2)).
  Exists (replace_Znth (j - 1) (Znth j output_l_2 0)
    (replace_Znth j (Znth (j - 1) output_l_2 0) output_l_2)).
  entailer!.
  - apply sort_inner_state_116_step_swap; auto; try lia.
  - repeat rewrite replace_Znth_length_116; lia.
  - repeat rewrite replace_Znth_length_116; lia.
Qed. 

Lemma proof_of_sort_array_entail_wit_15_3 : sort_array_entail_wit_15_3.
Proof.
  pre_process.
  Exists score_l_2. Exists output_l_2.
  entailer!.
  apply sort_inner_state_116_step_keep; auto; try lia.
Qed. 

Lemma proof_of_sort_array_entail_wit_15_4 : sort_array_entail_wit_15_4.
Proof.
  pre_process.
  Exists score_l_2. Exists output_l_2.
  entailer!.
  apply sort_inner_state_116_step_keep; auto; try lia.
Qed. 

Lemma proof_of_sort_array_entail_wit_17 : sort_array_entail_wit_17.
Proof.
  pre_process.
  assert (Hi_eq : i = arr_size_pre) by lia.
  subst i.
  Exists score_l_2. Exists output_l_2.
  entailer!.
  apply sort_outer_state_116_final_spec with (scores := score_l_2); auto.
  replace (Zlength input_l) with arr_size_pre by lia.
  exact PreH14.
Qed. 

Lemma proof_of_sort_array_partial_solve_wit_7_pure : sort_array_partial_solve_wit_7_pure.
Proof.
  pre_process; entailer!;
    pose proof (sort_array_116_int_range_at input_l i PreH8 ltac:(lia));
    lia.
Qed. 
