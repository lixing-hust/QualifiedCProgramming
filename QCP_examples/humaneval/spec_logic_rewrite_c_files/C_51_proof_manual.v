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
From SimpleC.EE Require Import C_51_goal.
From SimpleC.EE Require Import C_51_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_51.
Local Open Scope sac.

Lemma proof_of_remove_vowels_entail_wit_1 : remove_vowels_entail_wit_1.
Proof.
  unfold remove_vowels_entail_wit_1. right.
  pre_process_default.
  pose proof vowel_payload_safe_proof_51.
  pose proof (filter_prefix_nil_51 input_l).
  sep_apply_l_atomic (GlobalStrings_split LitMap vowel_literal_51).
  sep_apply_l_atomic (vowel_lit_to_store_51 LitMap).
  unfold all_vowel_literals_51, vowel_ptr_51, vowel_literal_51,
    vowel_payload_51, string_lib.store_string.
  simpl.
  replace (LitMap "AEIOUaeiou" + 0) with (LitMap "AEIOUaeiou") by lia.
  subst text0.
  pose proof (Zlength_nonneg input_l).
  unfold string_lib.string_length in PreH3.
  entailer!; try apply Zlength_nonneg.
Qed.

Lemma proof_of_remove_vowels_entail_wit_2_1 : remove_vowels_entail_wit_2_1.
Proof.
  unfold remove_vowels_entail_wit_2_1. right.
  pre_process_default.
  assert (Hi : 0 <= i < string_length input_l) by (subst n; lia).
  assert (Hrange : 0 <= Znth i (c_string input_l) 0 <= 127).
  { apply all_ascii_c_string_inside_51; [exact (proj1 PreH13) | exact Hi]. }
  assert (Hkeep : keep_char_z_51 (Znth i (c_string input_l) 0) = true).
  { eapply strchr_vowel_miss_51; [exact Hrange | subst retval; exact PreH2]. }
  assert (Hstep : filter_prefix_51 input_l (i + 1)
      (app output_l_2
        (cons (signed_last_nbits (Znth i (c_string input_l) 0) 8) nil))).
  { eapply filter_prefix_miss_c_51; eauto. }
  entailer!; eauto.
  rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_remove_vowels_entail_wit_2_2 : remove_vowels_entail_wit_2_2.
Proof.
  unfold remove_vowels_entail_wit_2_2. right.
  pre_process_default.
  assert (Hi : 0 <= i < string_length input_l) by (subst n; lia).
  assert (Hnz : Znth i (c_string input_l) 0 <> 0).
  { apply c_string_nonzero_inside_51; [exact PreH13 | exact Hi]. }
  assert (Hkeep : keep_char_z_51 (Znth i (c_string input_l) 0) = false).
  { eapply strchr_vowel_hit_51; eauto. }
  assert (Hstep : filter_prefix_51 input_l (i + 1) output_l_2).
  { eapply filter_prefix_hit_c_51; eauto. }
  entailer!; eauto; lia.
Qed.

Lemma proof_of_remove_vowels_return_wit_1 : remove_vowels_return_wit_1.
Proof.
  unfold remove_vowels_return_wit_1. right.
  pre_process_default.
  assert (Hi : i = n) by lia.
  assert (Hfull : filter_prefix_51 input_l (string_length input_l) output_l_2).
  { replace (string_length input_l) with i by lia. exact PreH15. }
  pose proof (filter_prefix_full_spec_51 input_l output_l_2 Hfull) as Hspec.
  pose proof (proj1 Hfull) as Hbound.
  Exists output_l_2.
  subst vowels n j.
  unfold string_lib.store_string, string_lib.string_length, string_lib.c_string.
  unfold string_length in *.
  entailer!; try lia.
Qed.

Lemma proof_of_remove_vowels_partial_solve_wit_2_pure : remove_vowels_partial_solve_wit_2_pure.
Proof.
  unfold remove_vowels_partial_solve_wit_2_pure. left.
  pre_process_default.
  pose proof (Zlength_nonneg input_l).
  unfold string_lib.string_length in *.
  entailer!; lia.
Qed.

Lemma proof_of_remove_vowels_partial_solve_wit_3_pure : remove_vowels_partial_solve_wit_3_pure.
Proof.
  unfold remove_vowels_partial_solve_wit_3_pure. right.
  pre_process_default.
  destruct PreH21 as [Hvvalid [Hvascii Hvlen]].
  assert (Hi : 0 <= i < string_length input_l) by (subst n; lia).
  pose proof (all_ascii_c_string_inside_51 input_l i (proj1 PreH19) Hi) as Hchar.
  entailer!; lia.
Qed.
