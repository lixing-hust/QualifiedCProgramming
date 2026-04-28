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
From SimpleC.EE Require Import C_120_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_120.
Local Open Scope sac.

Lemma proof_of_maximum_entail_wit_1 : maximum_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
Qed. 

Lemma proof_of_maximum_entail_wit_2 : maximum_entail_wit_2.
Proof.
  pre_process.
  Exists (tmp_l_2 ++ (Znth i input_l 0 :: nil)).
  sep_apply (IntArray.seg_single tmp i (Znth i input_l 0)).
  sep_apply (IntArray.seg_merge_to_seg tmp 0 i (i + 1)); [ | lia].
  entailer!.
  - rewrite copy_prefix_snoc by lia.
    subst tmp_l_2.
    reflexivity.
  - rewrite Zlength_app.
    rewrite Zlength_cons.
    rewrite Zlength_nil.
    lia.
Qed. 

Lemma proof_of_maximum_entail_wit_3 : maximum_entail_wit_3.
Proof.
  pre_process.
  replace i with arr_size_pre in * by lia.
  subst tmp_l.
  rewrite copy_prefix_full by lia.
  entailer!.
Qed. 

Lemma proof_of_maximum_entail_wit_4 : maximum_entail_wit_4.
Proof.
  pre_process.
  assert (sorted_full_l = sorted_l_2).
  {
    rewrite <- H5.
    symmetry.
    apply sublist_self.
    lia.
  }
  subst sorted_full_l.
  Exists sorted_l_2.
  entailer!.
Qed. 

Lemma proof_of_maximum_entail_wit_5 : maximum_entail_wit_5.
Proof.
  pre_process.
  Exists (@nil Z) sorted_l_2.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  - symmetry. apply maximum_output_prefix_nil.
Qed. 

Lemma proof_of_maximum_entail_wit_6 : maximum_entail_wit_6.
Proof.
  pre_process.
  Exists (output_l_2 ++ (Znth (arr_size_pre - k_pre + i) sorted_l_2 0 :: nil)) sorted_l_2.
  sep_apply (IntArray.seg_single data i (Znth (arr_size_pre - k_pre + i) sorted_l_2 0)).
  sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)); [ | lia].
  entailer!.
  - rewrite maximum_output_prefix_snoc by lia.
    subst output_l_2.
    replace (arr_size_pre - k_pre + i) with ((arr_size_pre - k_pre) + i) by lia.
    reflexivity.
  - rewrite Zlength_app.
    rewrite Zlength_cons.
    rewrite Zlength_nil.
    lia.
Qed. 

Lemma proof_of_maximum_entail_wit_7 : maximum_entail_wit_7.
Proof.
  pre_process.
  replace i with k_pre in * by lia.
  Exists output_l_2 sorted_l_2.
  subst output_l_2.
  assert (problem_120_spec_z input_l k_pre
            (maximum_output_prefix sorted_l_2 arr_size_pre k_pre k_pre)).
  {
    replace arr_size_pre with (Zlength input_l) by lia.
    apply problem_120_spec_z_of_sorted with (sorted_l := sorted_l_2); try assumption; try lia.
    - symmetry. apply maximum_output_prefix_Zlength; lia.
    - reflexivity.
  }
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full data 0 k_pre (maximum_output_prefix sorted_l_2 arr_size_pre k_pre k_pre)).
  replace (data + 0 * sizeof(INT)) with data by lia.
  replace (k_pre - 0) with k_pre by lia.
  entailer!.
Qed. 

Lemma proof_of_maximum_return_wit_2 : maximum_return_wit_2.
Proof.
  pre_process.
  replace k_pre with 0 in * by lia.
  Exists (@nil Z) retval_2.
  sep_apply IntArray_undef_full_0_to_full_nil.
  entailer!.
  - apply problem_120_spec_z_nil.
Qed. 
