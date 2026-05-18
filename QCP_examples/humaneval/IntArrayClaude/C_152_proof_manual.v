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
From SimpleC.EE Require Import C_152_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_152.
Local Open Scope sac.

Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof.
  pre_process.
Qed. 

Lemma proof_of_compare_safety_wit_5 : compare_safety_wit_5.
Proof.
  pre_process.
  pose proof (compare_int_range_at game_l guess_l i H12 ltac:(lia)) as Hrange.
  entailer!.
Qed. 

Lemma proof_of_compare_entail_wit_1 : compare_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  apply compare_prefix_0; lia.
Qed. 

Lemma proof_of_compare_entail_wit_2 : compare_entail_wit_2.
Proof.
  pre_process.
  Exists (output_l_2 ++ (retval :: nil)).
  sep_apply (IntArray.seg_single data i retval).
  sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)); [ | lia].
  entailer!.
  - eapply compare_prefix_snoc; eauto; try lia.
  - symmetry.
    eapply compare_prefix_snoc_Zlength; eauto; try lia.
Qed. 

Lemma proof_of_compare_return_wit_1 : compare_return_wit_1.
Proof.
  pre_process.
  replace i with n in * by lia.
  replace n with game_size_pre in * by lia.
  Exists output_l_2 game_size_pre data_2.
  rewrite (IntArray.undef_seg_empty data_2 game_size_pre).
  sep_apply (IntArray.seg_to_full data_2 0 game_size_pre).
  replace (data_2 + 0 * sizeof(INT)) with data_2 by lia.
  replace (game_size_pre - 0) with game_size_pre by lia.
  entailer!.
  apply compare_prefix_full_spec.
  - rewrite <- H8.
    assumption.
  - assumption.
Qed. 

Lemma proof_of_compare_partial_solve_wit_5_pure : compare_partial_solve_wit_5_pure.
Proof.
  pre_process.
  pose proof (compare_int_range_at game_l guess_l i H12 ltac:(lia)) as Hrange.
  entailer!.
Qed. 
