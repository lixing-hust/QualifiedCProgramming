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
From SimpleC.EE Require Import C_88_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_88.
Local Open Scope sac.

Lemma proof_of_sort_array_safety_wit_6 : sort_array_safety_wit_6.
Proof.
  pre_process.
  match goal with
  | H : sort_array_input_range input_l |- _ => destruct H as [Hrange Hsum]
  end.
  entailer!.
  - pose proof (Hrange 0 ltac:(lia)).
    pose proof (Hrange (array_size_pre - 1) ltac:(lia)).
    lia.
  - rewrite H8.
    apply Hsum. lia.
Qed. 

Lemma proof_of_sort_array_entail_wit_1 : sort_array_entail_wit_1.
Proof.
  pre_process.
  sep_apply IntArray.undef_full_to_undef_seg.
  change (copy_prefix 0 input_l) with (@nil Z).
  rewrite IntArray.seg_empty.
  entailer!.
Qed. 

Lemma proof_of_sort_array_entail_wit_2 : sort_array_entail_wit_2.
Proof.
  pre_process.
  sep_apply (IntArray.seg_single data i (Znth i input_l 0)).
  sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)
               (copy_prefix i input_l) (Znth i input_l 0 :: nil)).
  entailer!.
  - rewrite copy_prefix_snoc by lia. reflexivity.
  - rewrite copy_prefix_Zlength by lia. lia.
  - lia.
Qed. 

Lemma proof_of_sort_array_entail_wit_3 : sort_array_entail_wit_3.
Proof.
  pre_process.
  replace i with array_size_pre in * by lia.
  assert (Hcopy : copy_prefix array_size_pre input_l = input_l).
  {
    match goal with
    | H : array_size_pre = Zlength input_l |- _ =>
        rewrite H; apply copy_prefix_full
    end.
  }
  rewrite Hcopy.
  rewrite (IntArray.undef_seg_empty data array_size_pre).
  sep_apply (IntArray.seg_to_full data 0 array_size_pre input_l).
  replace (data + 0 * sizeof(INT)) with data by lia.
  replace (array_size_pre - 0) with array_size_pre by lia.
  entailer!.
Qed. 

Lemma proof_of_sort_array_entail_wit_4 : sort_array_entail_wit_4.
Proof.
  pre_process.
  Exists sorted_l_2.
  rewrite reverse_loop_0.
  assert (Hspec : problem_88_spec_z input_l
                    (reverse_loop array_size_pre (array_size_pre ÷ 2) sorted_l_2)).
  { apply H4. split; assumption. }
  assert (Hq : 0 <= array_size_pre ÷ 2).
  {
    assert (Hquot : array_size_pre ÷ 2 = array_size_pre / 2) by
      (apply Z.quot_div_nonneg; lia).
    rewrite Hquot.
    apply Z.div_pos; lia.
  }
  assert (Hb1 : 0 < array_size_pre ÷ 2 -> 0 <= 0 < array_size_pre).
  { intros; lia. }
  assert (Hb2 : 0 < array_size_pre ÷ 2 ->
                0 <= array_size_pre - 1 - 0 < array_size_pre).
  { intros; lia. }
  entailer!.
Qed. 

Lemma proof_of_sort_array_entail_wit_5 : sort_array_entail_wit_5.
Proof.
  pre_process.
  Exists sorted_l_2.
  rewrite reverse_loop_snoc by lia.
  unfold reverse_step.
  assert (Hqle : array_size_pre ÷ 2 <= array_size_pre).
  {
    assert (Hquot : array_size_pre ÷ 2 = array_size_pre / 2) by
      (apply Z.quot_div_nonneg; lia).
    rewrite Hquot.
    apply Z.div_le_upper_bound; lia.
  }
  assert (Hb1 : i + 1 < array_size_pre ÷ 2 ->
                0 <= i + 1 < array_size_pre).
  { intros; lia. }
  assert (Hb2 : i + 1 < array_size_pre ÷ 2 ->
                0 <= array_size_pre - 1 - (i + 1) < array_size_pre).
  { intros; lia. }
  assert (Hlen : array_size_pre =
                 Zlength (reverse_loop array_size_pre (i + 1) sorted_l_2)).
  { rewrite reverse_loop_Zlength by lia. lia. }
  assert (Hlen_step :
            array_size_pre =
            Zlength
              (replace_Znth (array_size_pre - 1 - i)
                 (Znth i (reverse_loop array_size_pre i sorted_l_2) 0)
                 (replace_Znth i
                    (Znth (array_size_pre - 1 - i)
                       (reverse_loop array_size_pre i sorted_l_2) 0)
                    (reverse_loop array_size_pre i sorted_l_2)))).
  {
    repeat rewrite replace_Znth_length_local.
    exact H16.
  }
  entailer!.
Qed. 

Lemma proof_of_sort_array_return_wit_2 : sort_array_return_wit_2.
Proof.
  pre_process.
  Exists sorted_l data_2.
  entailer!.
Qed. 

Lemma proof_of_sort_array_return_wit_3 : sort_array_return_wit_3.
Proof.
  pre_process.
  assert (Hnil : input_l = (@nil Z)).
  {
    apply Zlength_nil_inv.
    lia.
  }
  subst array_size_pre.
  subst input_l.
  Exists (@nil Z) retval_2.
  rewrite (IntArray.undef_full_empty retval_2).
  rewrite (IntArray.full_empty retval_2 0).
  entailer!.
  apply problem_88_spec_nil.
Qed. 
