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
From SimpleC.EE Require Import C_155_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_155.
Local Open Scope sac.

Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof. pre_process. Qed.

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof. pre_process. Qed.

Lemma proof_of_even_odd_count_entail_wit_1_1 : even_odd_count_entail_wit_1_1.
Proof.
  pre_process.
  entailer!.
  subst retval.
  unfold Zabs in *.
  apply digit_count_state_init_nonzero.
  pose proof (Z.abs_nonneg num_pre).
  lia.
Qed.

Lemma proof_of_even_odd_count_entail_wit_1_2 : even_odd_count_entail_wit_1_2.
Proof.
  pre_process.
  entailer!.
  subst retval.
  apply digit_count_state_init_zero.
  unfold Zabs in *.
  lia.
Qed.

Lemma proof_of_even_odd_count_entail_wit_2 : even_odd_count_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  - replace (w mod 10) with (Z.rem w 10) in * by
      (apply Z.rem_mod_nonneg; lia).
    eapply digit_count_state_step_odd.
    + exact H11.
    + lia.
    + reflexivity.
    + exact H.
  - apply digit_count_state_odd_next_bound with (num := num_pre) (w := w) (even := n2); try assumption.
    unfold Zabs in *; lia.
Qed.

Lemma proof_of_even_odd_count_entail_wit_3 : even_odd_count_entail_wit_3.
Proof.
  pre_process.
  entailer!.
  - replace (w mod 10) with (Z.rem w 10) in * by
      (apply Z.rem_mod_nonneg; lia).
    eapply digit_count_state_step_even.
    + exact H11.
    + lia.
    + reflexivity.
    + exact H.
  - apply digit_count_state_even_next_bound with (num := num_pre) (w := w) (odd := n1); try assumption.
    unfold Zabs in *; lia.
Qed.

Lemma proof_of_even_odd_count_entail_wit_4_1 : even_odd_count_entail_wit_4_1.
Proof.
  pre_process.
  entailer!.
  - pose proof (Zquot_10_lt_self w H3).
    lia.
  - rewrite Z.quot_div_nonneg by lia.
    apply Z.div_pos; lia.
Qed.

Lemma proof_of_even_odd_count_entail_wit_4_2 : even_odd_count_entail_wit_4_2.
Proof.
  pre_process.
  entailer!.
  - pose proof (Zquot_10_lt_self w H3).
    lia.
  - rewrite Z.quot_div_nonneg by lia.
    apply Z.div_pos; lia.
Qed.

Lemma proof_of_even_odd_count_return_wit_1 : even_odd_count_return_wit_1.
Proof.
  pre_process.
  replace w with 0 in * by lia.
  Exists (n2 :: n1 :: nil) 2 retval_2.
  entailer!.
  - sep_apply (IntArray.seg_single retval_2 1 n1).
    sep_apply (IntArray.seg_single retval_2 0 n2).
    sep_apply (IntArray.seg_merge_to_seg retval_2 0 1 2); [ | lia].
    sep_apply (IntArray.seg_to_full retval_2 0 2).
    replace (retval_2 + 0 * sizeof (INT)) with retval_2 by lia.
    replace (2 - 0) with 2 by lia.
    entailer!.
  - apply digit_count_state_final_spec.
    assumption.
Qed.
