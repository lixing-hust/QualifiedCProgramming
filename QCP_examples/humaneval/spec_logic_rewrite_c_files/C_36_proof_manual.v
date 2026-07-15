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
From SimpleC.EE Require Import C_36_goal.
From SimpleC.EE Require Import C_36_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_36.
Local Open Scope sac.

Lemma proof_of_fizz_buzz_safety_wit_15 : fizz_buzz_safety_wit_15.
Proof.
  left. intros. entailer!.
  - try lia.
    pose proof (fizz_buzz_prefix_z_nonneg i).
    lia.
  - try lia.
    apply (hit_increment_bound count q); assumption.
Qed.

Lemma proof_of_fizz_buzz_safety_wit_17 : fizz_buzz_safety_wit_17.
Proof.
  left. intros. entailer!.
  try lia.
  apply (hit_increment_bound digit_count q); assumption.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_1 : fizz_buzz_entail_wit_1.
Proof.
  right. intros. entailer!.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_2_1 : fizz_buzz_entail_wit_2_1.
Proof.
  right. intros. entailer!.
  - apply divisible_11_or_13_from_11. exact PreH1.
  - apply count_digit7_z_nonneg.
  - apply digit7_state_start. lia.
  - rewrite PreH10. apply (fizz_buzz_prefix_hit_bound_11 n_pre i); assumption.
  - pose proof (fizz_buzz_prefix_hit_bound_11 n_pre i PreH6 PreH8 PreH2 PreH1).
    pose proof (fizz_buzz_prefix_z_nonneg i).
    lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_2_2 : fizz_buzz_entail_wit_2_2.
Proof.
  right. intros. entailer!.
  - apply divisible_11_or_13_from_13. exact PreH1.
  - apply count_digit7_z_nonneg.
  - apply digit7_state_start. lia.
  - rewrite PreH11. apply (fizz_buzz_prefix_hit_bound_13 n_pre i); assumption.
  - pose proof (fizz_buzz_prefix_hit_bound_13 n_pre i PreH7 PreH9 PreH3 PreH1).
    pose proof (fizz_buzz_prefix_z_nonneg i).
    lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_3_1 : fizz_buzz_entail_wit_3_1.
Proof.
  right. intros. entailer!.
  - rewrite Zquot_eq_Zdiv_nonneg by lia. apply Z.div_pos; lia.
  - rewrite Zquot_eq_Zdiv_nonneg by lia. apply Z.div_le_upper_bound; lia.
  - apply digit7_state_hit_seen_bound with q; assumption.
  - apply digit7_state_hit; assumption.
  - apply (hit_remaining_bound count q); assumption.
  - apply (hit_remaining_bound digit_count q); assumption.
  - apply (hit_increment_bound count q); assumption.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_3_2 : fizz_buzz_entail_wit_3_2.
Proof.
  right. intros. entailer!.
  - rewrite Zquot_eq_Zdiv_nonneg by lia. apply Z.div_pos; lia.
  - rewrite Zquot_eq_Zdiv_nonneg by lia. apply Z.div_le_upper_bound; lia.
  - apply digit7_state_miss; assumption.
  - apply (miss_remaining_bound count q); assumption.
  - apply (miss_remaining_bound digit_count q); assumption.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_4_1 : fizz_buzz_entail_wit_4_1.
Proof.
  right. intros. entailer!.
  rewrite PreH11.
  symmetry. apply fizz_buzz_prefix_step_none; assumption.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_4_2 : fizz_buzz_entail_wit_4_2.
Proof.
  right. intros. entailer!.
  assert (q = 0) by lia. subst q.
  pose proof (digit7_state_done i digit_count PreH15) as Hdone.
  rewrite Hdone in PreH14.
  rewrite PreH14.
  symmetry. apply fizz_buzz_prefix_step_divisible; assumption.
Qed.

Lemma proof_of_fizz_buzz_return_wit_1 : fizz_buzz_return_wit_1.
Proof.
  right. intros. entailer!.
  assert (i = n_pre) by lia. subst i.
  apply problem_36_spec_z_from_prefix; auto.
Qed.
