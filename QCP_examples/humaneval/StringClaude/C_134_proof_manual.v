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
From SimpleC.EE Require Import C_134_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_134.
Local Open Scope sac.

Ltac c134_pre :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Ltac c134_alpha :=
  unfold is_alpha_z in *; lia.

Lemma proof_of_check_if_last_char_is_a_letter_entail_wit_1_1 : check_if_last_char_is_a_letter_entail_wit_1_1.
Proof.
  unfold check_if_last_char_is_a_letter_entail_wit_1_1.
  intros.
  c134_pre.
  entailer!.
  try c134_alpha.
Qed.

Lemma proof_of_check_if_last_char_is_a_letter_entail_wit_1_2 : check_if_last_char_is_a_letter_entail_wit_1_2.
Proof.
  unfold check_if_last_char_is_a_letter_entail_wit_1_2.
  intros.
  c134_pre.
  entailer!.
  try c134_alpha.
Qed.

Lemma proof_of_check_if_last_char_is_a_letter_return_wit_1 : check_if_last_char_is_a_letter_return_wit_1.
Proof.
  unfold check_if_last_char_is_a_letter_return_wit_1.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_z_false; eauto.
  apply not_ends_with_single_letter_z_prev_not_space; auto; lia.
Qed.

Lemma proof_of_check_if_last_char_is_a_letter_return_wit_2 : check_if_last_char_is_a_letter_return_wit_2.
Proof.
  unfold check_if_last_char_is_a_letter_return_wit_2.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_z_true; eauto.
  apply ends_with_single_letter_z_intro_space; auto; lia.
Qed.

Lemma proof_of_check_if_last_char_is_a_letter_return_wit_3 : check_if_last_char_is_a_letter_return_wit_3.
Proof.
  unfold check_if_last_char_is_a_letter_return_wit_3.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_z_true; eauto.
  apply ends_with_single_letter_z_intro_single; try lia.
  unfold is_alpha_z.
  replace (Zlength l - 1) with 0 by lia.
  replace (1 - 1) with 0 in * by lia.
  left; lia.
Qed.

Lemma proof_of_check_if_last_char_is_a_letter_return_wit_4 : check_if_last_char_is_a_letter_return_wit_4.
Proof.
  unfold check_if_last_char_is_a_letter_return_wit_4.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_z_true; eauto.
  apply ends_with_single_letter_z_intro_single; try lia.
  unfold is_alpha_z.
  replace (Zlength l - 1) with 0 by lia.
  replace (1 - 1) with 0 in * by lia.
  right; lia.
Qed.

Lemma proof_of_check_if_last_char_is_a_letter_return_wit_5 : check_if_last_char_is_a_letter_return_wit_5.
Proof.
  unfold check_if_last_char_is_a_letter_return_wit_5.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_z_false; eauto.
  apply not_ends_with_single_letter_z_not_alpha; try lia.
  unfold is_alpha_z.
  lia.
Qed.

Lemma proof_of_check_if_last_char_is_a_letter_return_wit_6 : check_if_last_char_is_a_letter_return_wit_6.
Proof.
  unfold check_if_last_char_is_a_letter_return_wit_6.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_z_false; eauto.
  apply not_ends_with_single_letter_z_not_alpha; try lia.
  unfold is_alpha_z.
  lia.
Qed.

Lemma proof_of_check_if_last_char_is_a_letter_return_wit_7 : check_if_last_char_is_a_letter_return_wit_7.
Proof.
  unfold check_if_last_char_is_a_letter_return_wit_7.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_z_false; eauto.
  apply not_ends_with_single_letter_z_not_alpha; try lia.
  unfold is_alpha_z.
  lia.
Qed.

Lemma proof_of_check_if_last_char_is_a_letter_return_wit_8 : check_if_last_char_is_a_letter_return_wit_8.
Proof.
  unfold check_if_last_char_is_a_letter_return_wit_8.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_z_false; eauto.
  apply not_ends_with_single_letter_z_empty.
  lia.
Qed.
