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
From SimpleC.EE Require Import C_136_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_136.
Local Open Scope sac.

Lemma proof_of_largest_smallest_integers_entail_wit_1 : largest_smallest_integers_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_init.
  lia.
Qed.

Lemma proof_of_largest_smallest_integers_entail_wit_2_1 : largest_smallest_integers_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_min_zero with (minpos := minpos); try assumption; lia.
Qed.

Lemma proof_of_largest_smallest_integers_entail_wit_2_2 : largest_smallest_integers_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_min_smaller with (minpos := minpos); try assumption; lia.
Qed.

Lemma proof_of_largest_smallest_integers_entail_wit_2_3 : largest_smallest_integers_entail_wit_2_3.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_max_zero with (maxneg := maxneg); try assumption; lia.
Qed.

Lemma proof_of_largest_smallest_integers_entail_wit_2_4 : largest_smallest_integers_entail_wit_2_4.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_max_bigger with (maxneg := maxneg); try assumption; lia.
Qed.

Lemma proof_of_largest_smallest_integers_entail_wit_2_5 : largest_smallest_integers_entail_wit_2_5.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_keep_zero; try assumption; lia.
Qed.

Lemma proof_of_largest_smallest_integers_entail_wit_2_6 : largest_smallest_integers_entail_wit_2_6.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_keep_negative; try assumption; lia.
Qed.

Lemma proof_of_largest_smallest_integers_entail_wit_2_7 : largest_smallest_integers_entail_wit_2_7.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_keep_positive; try assumption; lia.
Qed.

Lemma proof_of_largest_smallest_integers_return_wit_1 : largest_smallest_integers_return_wit_1.
Proof.
  pre_process.
  replace i with lst_size_pre in * by lia.
  Exists (maxneg :: minpos :: nil) 2 retval_2.
  entailer!.
  - sep_apply (IntArray.seg_single retval_2 1 minpos).
    sep_apply (IntArray.seg_single retval_2 0 maxneg).
    sep_apply (IntArray.seg_merge_to_seg retval_2 0 1 2); [ | lia].
    sep_apply (IntArray.seg_to_full retval_2 0 2).
    replace (retval_2 + 0 * sizeof (INT)) with retval_2 by lia.
    replace (2 - 0) with 2 by lia.
    entailer!.
  - exists maxneg, minpos.
    split.
    + reflexivity.
    + split.
      * rewrite <- H4.
        assumption.
      * apply largest_smallest_prefix_full_spec.
        rewrite <- H4.
        assumption.
Qed.
