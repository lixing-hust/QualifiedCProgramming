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
From SimpleC.EE Require Import C_42_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_42.
Local Open Scope sac.

Lemma proof_of_incr_list_safety_wit_3 : incr_list_safety_wit_3.
Proof.
  pre_process.
  match goal with
  | H: list_incr_int_range input_l |- _ =>
      pose proof (H i) as Hrange
  end.
  entailer!.
Qed.

Lemma proof_of_incr_list_entail_wit_1 : incr_list_entail_wit_1.
Proof.
  pre_process.
  subst.
  rewrite sublist_nil by lia.
  simpl.
  sep_apply IntArray.undef_full_to_undef_seg.
  entailer!.
  rewrite IntArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_incr_list_entail_wit_2 : incr_list_entail_wit_2.
Proof.
  pre_process.
  rewrite map_incr_sublist_snoc by (rewrite <- H2; lia).
  sep_apply (IntArray.seg_single data i (Znth i input_l 0 + 1)).
  sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)); [ | lia].
  entailer!.
Qed.

Lemma proof_of_incr_list_return_wit_1 : incr_list_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = l_size_pre) by lia.
  subst i.
  Exists (map_incr input_l) l_size_pre data_2.
  rewrite sublist_self by exact H2.
  sep_apply (IntArray.seg_to_full data_2 0 l_size_pre).
  replace (data_2 + 0 * sizeof (INT)) with data_2 by lia.
  replace (l_size_pre - 0) with l_size_pre by lia.
  rewrite (IntArray.undef_seg_empty data_2 l_size_pre).
  entailer!.
  - apply problem_42_spec_map_incr.
  - rewrite map_incr_Zlength.
    auto.
Qed.
