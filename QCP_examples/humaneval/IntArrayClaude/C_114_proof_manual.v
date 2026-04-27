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
From SimpleC.EE Require Import C_114_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_114.
Local Open Scope sac.

Lemma proof_of_minSubArraySum_safety_wit_5 : minSubArraySum_safety_wit_5.
Proof.
  pre_process.
  subst current.
  match goal with
  | H: kadane_int64_range nums_l |- _ =>
      destruct H as [_ [Hsum _]];
      pose proof (Hsum i ltac:(lia)) as Hrange
  end.
  entailer!.
Qed. 

Lemma proof_of_minSubArraySum_entail_wit_1 : minSubArraySum_entail_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_minSubArraySum_entail_wit_2_1 : minSubArraySum_entail_wit_2_1.
Proof.
  pre_process.
  subst current min.
  assert (Hsuffix:
    min_suffix_prefix (i + 1) nums_l =
    min_suffix_prefix i nums_l + Znth i nums_l 0).
  { apply min_suffix_prefix_step_lt; lia. }
  assert (Hminnext:
    min_subarray_prefix (i + 1) nums_l =
    min_suffix_prefix i nums_l + Znth i nums_l 0).
  { apply (min_subarray_prefix_step_lt nums_l i
             (min_suffix_prefix i nums_l + Znth i nums_l 0)); try lia. }
  rewrite Hsuffix.
  rewrite Hminnext.
  entailer!.
Qed. 

Lemma proof_of_minSubArraySum_entail_wit_2_2 : minSubArraySum_entail_wit_2_2.
Proof.
  pre_process.
  subst current min.
  assert (Hsuffix:
    min_suffix_prefix (i + 1) nums_l = Znth i nums_l 0).
  { apply min_suffix_prefix_step_ge; lia. }
  assert (Hminnext:
    min_subarray_prefix (i + 1) nums_l = Znth i nums_l 0).
  { apply (min_subarray_prefix_step_lt nums_l i (Znth i nums_l 0)); try lia. }
  rewrite Hsuffix.
  rewrite Hminnext.
  entailer!.
Qed. 

Lemma proof_of_minSubArraySum_entail_wit_2_3 : minSubArraySum_entail_wit_2_3.
Proof.
  pre_process.
  subst current min.
  assert (Hsuffix:
    min_suffix_prefix (i + 1) nums_l = Znth i nums_l 0).
  { apply min_suffix_prefix_step_ge; lia. }
  assert (Hminnext:
    min_subarray_prefix (i + 1) nums_l = min_subarray_prefix i nums_l).
  { apply (min_subarray_prefix_step_ge nums_l i (Znth i nums_l 0)); try lia. }
  rewrite Hsuffix.
  rewrite Hminnext.
  entailer!.
Qed. 

Lemma proof_of_minSubArraySum_entail_wit_2_4 : minSubArraySum_entail_wit_2_4.
Proof.
  pre_process.
  subst current min.
  assert (Hsuffix:
    min_suffix_prefix (i + 1) nums_l =
    min_suffix_prefix i nums_l + Znth i nums_l 0).
  { apply min_suffix_prefix_step_lt; lia. }
  assert (Hminnext:
    min_subarray_prefix (i + 1) nums_l = min_subarray_prefix i nums_l).
  { apply (min_subarray_prefix_step_ge nums_l i
             (min_suffix_prefix i nums_l + Znth i nums_l 0)); try lia. }
  rewrite Hsuffix.
  rewrite Hminnext.
  entailer!.
Qed. 

Lemma proof_of_minSubArraySum_return_wit_1 : minSubArraySum_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = nums_size_pre) by lia.
  subst i min.
  entailer!.
  unfold problem_114_spec_z.
  replace nums_size_pre with (Zlength nums_l) by lia.
  reflexivity.
Qed. 
