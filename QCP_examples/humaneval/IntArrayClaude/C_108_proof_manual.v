Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_108_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_108.
Local Open Scope sac.

Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof.
  pre_process.
Qed.

Lemma proof_of_count_nums_safety_wit_4 : count_nums_safety_wit_4.
Proof.
  pre_process.
  pose proof (count_nums_prefix_bounds i input_l num H8).
  entailer!.
Qed.

Lemma proof_of_count_nums_safety_wit_8 : count_nums_safety_wit_8.
Proof.
  pre_process.
  unfold digit_scan_state in H9.
  destruct H9 as [_ [fuel [[_ Hw_upper] [_ [Hsum [Hsum_cur _]]]]]].
  assert (w % 10 = w mod 10) as Hrem.
  { apply Z.rem_mod_nonneg; lia. }
  assert (0 <= w mod 10 < 10) by (apply Z.mod_pos_bound; lia).
  rewrite Hrem.
  entailer!.
Qed.

Lemma proof_of_count_nums_safety_wit_13 : count_nums_safety_wit_13.
Proof.
  pre_process.
  unfold digit_scan_state in H9.
  destruct H9 as [_ [fuel [[Hw_nonneg Hw_upper] [_ [Hsum [Hsum_cur _]]]]]].
  entailer!.
Qed.

Lemma proof_of_count_nums_safety_wit_15 : count_nums_safety_wit_15.
Proof.
  pre_process.
  pose proof (count_nums_prefix_bounds i input_l num H8).
  entailer!.
Qed.

Lemma proof_of_count_nums_entail_wit_1 : count_nums_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  apply count_nums_prefix_init.
  rewrite <- H1.
  lia.
Qed.

Lemma proof_of_count_nums_entail_wit_2 : count_nums_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  subst retval.
  apply digit_scan_state_init.
  assert (INT_MIN < Znth i input_l 0 <= INT_MAX).
  {
    match goal with
    | Hrange: count_nums_int_range input_l |- _ =>
        apply Hrange; lia
    end.
  }
  rewrite Z.abs_neq by lia.
  lia.
Qed.

Lemma proof_of_count_nums_entail_wit_3 : count_nums_entail_wit_3.
Proof.
  pre_process.
  assert (0 <= w) as Hw_nonneg.
  {
    unfold digit_scan_state in H9.
    destruct H9 as [_ [fuel [[Hw_nonneg _] _]]].
    exact Hw_nonneg.
  }
  assert (w ÷ 10 = w / 10) as Hquot.
  { apply Z.quot_div_nonneg; lia. }
  assert (w % 10 = w mod 10) as Hrem.
  { apply Z.rem_mod_nonneg; lia. }
  rewrite Hquot, Hrem.
  entailer!.
  apply digit_scan_state_step; auto.
Qed.

Lemma proof_of_count_nums_entail_wit_4_1 : count_nums_entail_wit_4_1.
Proof.
  pre_process.
  entailer!.
  apply count_nums_prefix_hit; auto; try lia.
  unfold sum_digits.
  assert ((Znth i input_l 0 >? 0) = true) as Hgt by (apply Z.gtb_lt; lia).
  rewrite Hgt.
  lia.
Qed.

Lemma proof_of_count_nums_entail_wit_4_2 : count_nums_entail_wit_4_2.
Proof.
  pre_process.
  entailer!.
  apply count_nums_prefix_hit; auto; try lia.
  eapply digit_scan_state_final_hit; eauto; lia.
Qed.

Lemma proof_of_count_nums_entail_wit_4_3 : count_nums_entail_wit_4_3.
Proof.
  pre_process.
  entailer!.
  apply count_nums_prefix_miss; auto; try lia.
  eapply digit_scan_state_final_miss; eauto; lia.
Qed.

Lemma proof_of_count_nums_return_wit_1 : count_nums_return_wit_1.
Proof.
  pre_process.
  entailer!.
  apply problem_108_spec_z_of_prefix.
  replace (Zlength input_l) with i by lia.
  exact H7.
Qed.

Lemma proof_of_count_nums_partial_solve_wit_3_pure : count_nums_partial_solve_wit_3_pure.
Proof.
  pre_process.
  entailer!.
  match goal with
  | Hrange: count_nums_int_range input_l |- _ =>
      pose proof (Hrange i ltac:(lia)); lia
  end.
Qed.
