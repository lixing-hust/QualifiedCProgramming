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
From SimpleC.EE Require Import C_118_goal.
From SimpleC.EE Require Import C_118_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_118.
Local Open Scope sac.

Lemma proof_of_is_vowel_code_118_return_wit_1 : is_vowel_code_118_return_wit_1.
Proof. left; intros; unfold is_vowel_z_118; entailer!; firstorder. Qed.

Lemma proof_of_is_vowel_code_118_return_wit_2 : is_vowel_code_118_return_wit_2.
Proof. right; intros; unfold is_vowel_z_118; entailer!; firstorder. Qed.

Lemma proof_of_is_vowel_code_118_return_wit_3 : is_vowel_code_118_return_wit_3.
Proof. right; intros; unfold is_vowel_z_118; entailer!; firstorder. Qed.

Lemma proof_of_is_vowel_code_118_return_wit_4 : is_vowel_code_118_return_wit_4.
Proof. right; intros; unfold is_vowel_z_118; entailer!; firstorder. Qed.

Lemma proof_of_is_vowel_code_118_return_wit_5 : is_vowel_code_118_return_wit_5.
Proof. right; intros; unfold is_vowel_z_118; entailer!; firstorder. Qed.

Lemma proof_of_is_vowel_code_118_return_wit_6 : is_vowel_code_118_return_wit_6.
Proof. right; intros; unfold is_vowel_z_118; entailer!; firstorder. Qed.

Lemma proof_of_is_vowel_code_118_return_wit_7 : is_vowel_code_118_return_wit_7.
Proof. right; intros; unfold is_vowel_z_118; entailer!; firstorder. Qed.

Lemma proof_of_is_vowel_code_118_return_wit_8 : is_vowel_code_118_return_wit_8.
Proof. right; intros; unfold is_vowel_z_118; entailer!; firstorder. Qed.

Lemma proof_of_is_vowel_code_118_return_wit_9 : is_vowel_code_118_return_wit_9.
Proof. right; intros; unfold is_vowel_z_118; entailer!; firstorder. Qed.

Lemma proof_of_is_vowel_code_118_return_wit_10 : is_vowel_code_118_return_wit_10.
Proof. right; intros; unfold is_vowel_z_118; entailer!; firstorder. Qed.

Lemma proof_of_is_vowel_code_118_return_wit_11 : is_vowel_code_118_return_wit_11.
Proof. right; intros; unfold is_vowel_z_118; entailer!; firstorder. Qed.

Lemma proof_of_get_closest_vowel_entail_wit_1 : get_closest_vowel_entail_wit_1.
Proof.
  right; intros.
  pose proof (problem_118_pre_z_alpha_codes input PreH5 PreH6).
  entailer!.
Qed.

Lemma proof_of_get_closest_vowel_entail_wit_2 : get_closest_vowel_entail_wit_2.
Proof.
  right; intros.
  subst n.
  pose proof (no_candidate_after_z_118_start input).
  unfold string_length in *.
  entailer!.
Qed.

Lemma proof_of_get_closest_vowel_entail_wit_3 : get_closest_vowel_entail_wit_3.
Proof.
  right; intros.
  assert (Hi : 1 <= i < Zlength input - 1) by
    (unfold string_length in *; lia).
  pose proof (candidate_z_118_from_c_string input i PreH22 Hi
    PreH3 PreH9 PreH6) as Hcandidate.
  pose proof (c_string_inside_eq_118 input i ltac:(lia)) as Heq.
  entailer!.
Qed.

Lemma proof_of_get_closest_vowel_entail_wit_4_1 : get_closest_vowel_entail_wit_4_1.
Proof.
  right; intros.
  entailer!.
  apply candidate_z_118_not_cur.
  - unfold string_length in *; lia.
  - exact PreH3.
Qed.

Lemma proof_of_get_closest_vowel_entail_wit_4_2 : get_closest_vowel_entail_wit_4_2.
Proof.
  right; intros.
  entailer!.
  apply candidate_z_118_not_right.
  - unfold string_length in *; lia.
  - exact PreH3.
Qed.

Lemma proof_of_get_closest_vowel_entail_wit_4_3 : get_closest_vowel_entail_wit_4_3.
Proof.
  right; intros.
  entailer!.
  apply candidate_z_118_not_left.
  - unfold string_length in *; lia.
  - exact PreH3.
Qed.

Lemma proof_of_get_closest_vowel_entail_wit_5 : get_closest_vowel_entail_wit_5.
Proof.
  right; intros.
  pose proof (no_candidate_after_z_118_step input i PreH13 PreH14).
  entailer!.
Qed.

Lemma proof_of_get_closest_vowel_entail_wit_6 : get_closest_vowel_entail_wit_6.
Proof.
  right; intros.
  assert (i = 0) by lia; subst i.
  entailer!.
Qed.

Lemma proof_of_get_closest_vowel_return_wit_1 : get_closest_vowel_return_wit_1.
Proof.
  left; intros.
  Exists (@nil Z).
  pose proof (problem_118_spec_z_not_found input PreH10 PreH12).
  unfold store_string, string_length, c_string.
  simpl.
  entailer!.
  rewrite (CharArray.undef_seg_empty retval 1).
  sep_apply_l_atomic (CharArray.seg_single retval 0 0).
  sep_apply_l_atomic (CharArray.seg_to_full retval 0 1 (0 :: nil)).
  replace (retval + 0 * sizeof(CHAR)) with retval by lia.
  replace (1 - 0) with 1 by lia.
  entailer!.
Qed.

Lemma proof_of_get_closest_vowel_return_wit_2 : get_closest_vowel_return_wit_2.
Proof.
  left; intros; subst cur.
  Exists (Znth i input 0 :: nil).
  pose proof (problem_118_spec_z_found input i PreH14 PreH16 PreH17).
  assert (Hrange : 0 <= Znth i input 0 <= 127).
  { apply alpha_codes_z_118_range with (input := input); [exact PreH15 |].
    unfold string_length in *; lia. }
  rewrite (signed_last_nbits_eq (Znth i input 0) 8) by lia.
  unfold store_string, string_length, c_string.
  simpl.
  entailer!.
  rewrite (CharArray.undef_seg_empty retval 2).
  sep_apply_l_atomic (CharArray.seg_single retval 1 0).
  sep_apply_l_atomic (CharArray.seg_single retval 0 (Znth i input 0)).
  replace (1 + 1) with 2 by lia.
  replace (0 + 1) with 1 by lia.
  rewrite derivable1_sepcon_comm.
  sep_apply_l_atomic (CharArray.seg_merge_to_seg
    retval 0 1 2 (Znth i input 0 :: nil) (0 :: nil)).
  - entailer!.
  - simpl.
    sep_apply_l_atomic (CharArray.seg_to_full retval 0 2
      (Znth i input 0 :: 0 :: nil)).
    replace (retval + 0 * sizeof(CHAR)) with retval by lia.
    replace (2 - 0) with 2 by lia.
    entailer!.
Qed.

Lemma proof_of_get_closest_vowel_return_wit_3 : get_closest_vowel_return_wit_3.
Proof.
  left; intros.
  Exists (@nil Z).
  pose proof (problem_118_spec_z_short input PreH10 ltac:(unfold string_length in *; lia)).
  unfold store_string, string_length, c_string.
  simpl.
  entailer!.
  rewrite (CharArray.undef_seg_empty retval 1).
  sep_apply_l_atomic (CharArray.seg_single retval 0 0).
  sep_apply_l_atomic (CharArray.seg_to_full retval 0 1 (0 :: nil)).
  replace (retval + 0 * sizeof(CHAR)) with retval by lia.
  replace (1 - 0) with 1 by lia.
  entailer!.
Qed.

Lemma proof_of_get_closest_vowel_partial_solve_wit_4_pure :
  get_closest_vowel_partial_solve_wit_4_pure.
Proof.
  left; intros.
  pose proof (alpha_codes_c_string_range_118 input i PreH12 ltac:(unfold string_length in *; lia)).
  entailer!.
Qed.

Lemma proof_of_get_closest_vowel_partial_solve_wit_5_pure :
  get_closest_vowel_partial_solve_wit_5_pure.
Proof.
  left; intros.
  pose proof (alpha_codes_c_string_range_118 input (i + 1) PreH16
    ltac:(unfold string_length in *; lia)).
  entailer!.
Qed.

Lemma proof_of_get_closest_vowel_partial_solve_wit_6_pure :
  get_closest_vowel_partial_solve_wit_6_pure.
Proof.
  left; intros.
  pose proof (alpha_codes_c_string_range_118 input (i - 1) PreH19
    ltac:(unfold string_length in *; lia)).
  entailer!.
Qed.
