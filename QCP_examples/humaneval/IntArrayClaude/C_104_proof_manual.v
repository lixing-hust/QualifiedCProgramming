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
From SimpleC.EE Require Import C_104_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_104.
Local Open Scope sac.

Lemma proof_of_has_only_odd_digits_int_entail_wit_1 : has_only_odd_digits_int_entail_wit_1.
Proof.
  pre_process.
  Left.
  entailer!.
  constructor.
  lia.
Qed. 

Lemma proof_of_has_only_odd_digits_int_entail_wit_4_1 : has_only_odd_digits_int_entail_wit_4_1.
Proof.
  pre_process.
  subst u.
  Right.
  assert (0 <= num ÷ 10 <= value_pre).
  {
    assert (Hq : num ÷ 10 = num / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hq.
    assert (0 <= num / 10) by (apply Z.div_pos; lia).
    assert (num / 10 <= num).
    {
      apply Z.div_le_upper_bound; lia.
    }
    lia.
  }
  entailer!.
  apply odd_scan_even_quot; try assumption; lia.
Qed. 

Lemma proof_of_has_only_odd_digits_int_entail_wit_4_2 : has_only_odd_digits_int_entail_wit_4_2.
Proof.
  pre_process.
  subst u.
  Left.
  assert (0 <= num ÷ 10 <= value_pre).
  {
    assert (Hq : num ÷ 10 = num / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hq.
    assert (0 <= num / 10) by (apply Z.div_pos; lia).
    assert (num / 10 <= num).
    {
      apply Z.div_le_upper_bound; lia.
    }
    lia.
  }
  entailer!.
  apply odd_scan_odd_quot; try assumption; lia.
Qed. 

Lemma proof_of_has_only_odd_digits_int_return_wit_1 : has_only_odd_digits_int_return_wit_1.
Proof.
  pre_process.
  Right.
  entailer!.
  apply has_even_digit_done with (num := num) (u := u); assumption.
Qed. 

Lemma proof_of_has_only_odd_digits_int_return_wit_2 : has_only_odd_digits_int_return_wit_2.
Proof.
  pre_process.
  Left.
  entailer!.
  apply only_odd_digits_done with (num := num) (u := u); try assumption; lia.
Qed. 

Lemma proof_of_has_only_odd_digits_int_return_wit_3 : has_only_odd_digits_int_return_wit_3.
Proof.
  pre_process.
  Right.
  entailer!.
  apply has_even_digit_done with (num := num) (u := u); assumption.
Qed. 

Lemma proof_of_unique_digits_entail_wit_1 : unique_digits_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  constructor.
Qed. 

Lemma proof_of_unique_digits_entail_wit_4_1 : unique_digits_entail_wit_4_1.
Proof.
  pre_process.
  Exists (output_l_2 ++ (Znth i input_l 0 :: nil)).
  sep_apply (IntArray.seg_single data output_size (Znth i input_l 0)).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size (output_size + 1)); [ | lia].
  entailer!.
  - apply unique_digits_prefix_add_step; try assumption; lia.
  - rewrite Zlength_app.
    rewrite Zlength_cons.
    rewrite Zlength_nil.
    lia.
Qed. 

Lemma proof_of_unique_digits_entail_wit_4_2 : unique_digits_entail_wit_4_2.
Proof.
  pre_process.
  Exists output_l_2.
  entailer!.
  apply unique_digits_prefix_skip_step; try assumption; lia.
Qed. 

Lemma proof_of_unique_digits_entail_wit_6 : unique_digits_entail_wit_6.
Proof.
  pre_process.
  Exists sorted_full_l sorted_l_2 output_l_2.
  assert (problem_104_spec_z input_l sorted_l_2).
  {
    assert (unique_digits_prefix input_l (Zlength input_l) output_l_2).
    {
      replace (Zlength input_l) with x_size_pre by lia.
      assumption.
    }
    apply problem_104_spec_z_of_sorted with (filtered := output_l_2); assumption.
  }
  entailer!.
Qed. 

Lemma proof_of_unique_digits_return_wit_1 : unique_digits_return_wit_1.
Proof.
  pre_process.
  Exists data_l_2 sorted_l output_size_2 data_2.
  entailer!.
Qed. 

Lemma proof_of_unique_digits_partial_solve_wit_4_pure : unique_digits_partial_solve_wit_4_pure.
Proof.
  pre_process.
  pose proof (problem_104_pre_z_Znth input_l i H5 ltac:(lia)).
  entailer!.
Qed. 
