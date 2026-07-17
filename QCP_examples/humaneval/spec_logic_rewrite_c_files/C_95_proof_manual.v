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
From SimpleC.EE Require Import C_95_goal.
From SimpleC.EE Require Import C_95_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_95.
Local Open Scope sac.

Lemma proof_of_check_dict_case_safety_wit_33 : check_dict_case_safety_wit_33.
Proof.
  unfold check_dict_case_safety_wit_33. left. intros. entailer!.
  all: unfold dict_case_state_z_95 in PreH16; lia.
Qed.

Lemma proof_of_check_dict_case_safety_wit_34 : check_dict_case_safety_wit_34.
Proof.
  unfold check_dict_case_safety_wit_34. left. intros. entailer!.
  all: unfold dict_case_state_z_95 in PreH18; lia.
Qed.

Lemma proof_of_check_dict_case_safety_wit_39 : check_dict_case_safety_wit_39.
Proof.
  unfold check_dict_case_safety_wit_39. left. intros.
  pose proof (rows_well_formed_row_95 rows dict_size_pre k PreH17
                ltac:(lia)) as Hrow.
  entailer!.
  all: destruct Hrow as [Hrowlen _]; lia.
Qed.

Lemma proof_of_check_dict_case_safety_wit_40 : check_dict_case_safety_wit_40.
Proof.
  unfold check_dict_case_safety_wit_40. left. intros.
  pose proof (rows_well_formed_row_95 rows dict_size_pre k PreH15
                ltac:(lia)) as Hrow.
  entailer!.
  all: destruct Hrow as [Hrowlen _]; lia.
Qed.

Lemma proof_of_check_dict_case_entail_wit_1 : check_dict_case_entail_wit_1.
Proof.
  unfold check_dict_case_entail_wit_1. left. intros. entailer!.
  apply dict_case_state_init_95.
Qed.

Lemma proof_of_check_dict_case_entail_wit_2 : check_dict_case_entail_wit_2.
Proof.
  unfold check_dict_case_entail_wit_2. right. intros.
  rewrite (Znth_indep rows k __default__List_Z nil) by
    (rewrite (rows_well_formed_length_95 rows dict_size_pre PreH7); lia).
  entailer!.
Qed.

Lemma proof_of_check_dict_case_entail_wit_3 : check_dict_case_entail_wit_3.
Proof.
  unfold check_dict_case_entail_wit_3. left. intros. entailer!.
  pose proof (rows_well_formed_row_95 rows dict_size_pre k PreH5 ltac:(lia)). lia.
Qed.

Lemma proof_of_check_dict_case_entail_wit_4_1 : check_dict_case_entail_wit_4_1.
Proof.
  unfold check_dict_case_entail_wit_4_1. right. intros.
  destruct (current_nonzero_before_last_95 rows dict_size_pre k i PreH17
              ltac:(lia) ltac:(lia) PreH10) as [Hib Hnext].
  assert (dict_case_state_z_95 k (i + 1) rows 1 isupper) as Hstate.
  { apply dict_case_state_lower_step_95 with (islower := islower).
    - rewrite (rows_well_formed_length_95 rows dict_size_pre PreH17). lia.
    - exact Hib.
    - unfold lower_char_z_95. lia.
    - exact PreH1.
    - exact PreH19. }
  entailer!.
Qed.

Lemma proof_of_check_dict_case_entail_wit_4_2 : check_dict_case_entail_wit_4_2.
Proof.
  unfold check_dict_case_entail_wit_4_2. right. intros.
  destruct (current_nonzero_before_last_95 rows dict_size_pre k i PreH15
              ltac:(lia) ltac:(lia) PreH8) as [Hib Hnext].
  assert (dict_case_state_z_95 k (i + 1) rows islower 1) as Hstate.
  { apply dict_case_state_upper_step_95 with (isupper := isupper).
    - rewrite (rows_well_formed_length_95 rows dict_size_pre PreH15). lia.
    - exact Hib.
    - unfold upper_char_z_95. lia.
    - exact PreH1.
    - exact PreH17. }
  entailer!.
Qed.

Lemma proof_of_check_dict_case_entail_wit_5 : check_dict_case_entail_wit_5.
Proof.
  unfold check_dict_case_entail_wit_5. right. intros.
  assert (dict_case_state_z_95 (k + 1) 0 rows islower isupper) as Hstate.
  { exact (dict_case_state_row_done_95 rows dict_size_pre k i islower isupper
             PreH9 ltac:(lia) ltac:(lia) PreH2 PreH11). }
  entailer!.
  pose proof (CharPtrArray2.missing_i_merge_to_full
                keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
            (Zlength (Znth k rows nil)) (Znth k rows nil)) with
         (CharArray.full row_ptr
            (Zlength (Znth k rows nil)) (Znth k rows nil)) in Hmerge.
  rewrite sizeof_ptr.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma proof_of_check_dict_case_return_wit_1 : check_dict_case_return_wit_1.
Proof.
  unfold check_dict_case_return_wit_1. intros.
  rewrite <- derivable1_orp_intros2.
  assert (k = dict_size_pre) by lia. subst k.
  assert (problem_95_spec_z rows 1) as Hspec.
  { exact (problem_95_spec_z_one_from_state_95 rows dict_size_pre
             islower isupper PreH6 PreH4 PreH8). }
  entailer!.
Qed.

Lemma proof_of_check_dict_case_return_wit_2 : check_dict_case_return_wit_2.
Proof.
  unfold check_dict_case_return_wit_2. intros.
  rewrite <- derivable1_orp_intros1.
  assert (problem_95_spec_z rows 0) as Hspec.
  { apply problem_95_spec_z_zero_lower_mixed_95 with
      (n := dict_size_pre) (k := k) (i := i)
      (islower := islower) (isupper := isupper).
    - exact PreH17.
    - lia.
    - destruct (current_nonzero_before_last_95 rows dict_size_pre k i
                  PreH17 ltac:(lia) ltac:(lia) PreH10); assumption.
    - unfold lower_char_z_95. lia.
    - exact PreH1.
    - exact PreH19. }
  entailer!.
  pose proof (CharPtrArray2.missing_i_merge_to_full
                keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
            (Zlength (Znth k rows nil)) (Znth k rows nil)) with
         (CharArray.full row_ptr
            (Zlength (Znth k rows nil)) (Znth k rows nil)) in Hmerge.
  rewrite sizeof_ptr. sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia. cancel.
Qed.

Lemma proof_of_check_dict_case_return_wit_3 : check_dict_case_return_wit_3.
Proof.
  unfold check_dict_case_return_wit_3. intros.
  rewrite <- derivable1_orp_intros1.
  assert (problem_95_spec_z rows 0) as Hspec.
  { apply problem_95_spec_z_zero_upper_mixed_95 with
      (n := dict_size_pre) (k := k) (i := i)
      (islower := islower) (isupper := isupper).
    - exact PreH15.
    - lia.
    - destruct (current_nonzero_before_last_95 rows dict_size_pre k i
                  PreH15 ltac:(lia) ltac:(lia) PreH8); assumption.
    - unfold upper_char_z_95. lia.
    - exact PreH1.
    - exact PreH17. }
  entailer!.
  pose proof (CharPtrArray2.missing_i_merge_to_full
                keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
            (Zlength (Znth k rows nil)) (Znth k rows nil)) with
         (CharArray.full row_ptr
            (Zlength (Znth k rows nil)) (Znth k rows nil)) in Hmerge.
  rewrite sizeof_ptr. sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia. cancel.
Qed.

Lemma proof_of_check_dict_case_return_wit_4 : check_dict_case_return_wit_4.
Proof.
  unfold check_dict_case_return_wit_4. intros.
  rewrite <- derivable1_orp_intros1.
  assert (problem_95_spec_z rows 0) as Hspec.
  { apply problem_95_spec_z_zero_invalid_95 with
      (n := dict_size_pre) (k := k) (i := i)
      (islower := islower) (isupper := isupper); try assumption; try lia.
    unfold letter_char_z_95, lower_char_z_95, upper_char_z_95. lia. }
  entailer!.
  pose proof (CharPtrArray2.missing_i_merge_to_full
                keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
            (Zlength (Znth k rows nil)) (Znth k rows nil)) with
         (CharArray.full row_ptr
            (Zlength (Znth k rows nil)) (Znth k rows nil)) in Hmerge.
  rewrite sizeof_ptr. sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia. cancel.
Qed.

Lemma proof_of_check_dict_case_return_wit_5 : check_dict_case_return_wit_5.
Proof.
  unfold check_dict_case_return_wit_5. intros.
  rewrite <- derivable1_orp_intros1.
  assert (problem_95_spec_z rows 0) as Hspec.
  { apply problem_95_spec_z_zero_invalid_95 with
      (n := dict_size_pre) (k := k) (i := i)
      (islower := islower) (isupper := isupper); try assumption; try lia.
    unfold letter_char_z_95, lower_char_z_95, upper_char_z_95. lia. }
  entailer!.
  pose proof (CharPtrArray2.missing_i_merge_to_full
                keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
            (Zlength (Znth k rows nil)) (Znth k rows nil)) with
         (CharArray.full row_ptr
            (Zlength (Znth k rows nil)) (Znth k rows nil)) in Hmerge.
  rewrite sizeof_ptr. sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia. cancel.
Qed.

Lemma proof_of_check_dict_case_return_wit_6 : check_dict_case_return_wit_6.
Proof.
  unfold check_dict_case_return_wit_6. intros.
  rewrite <- derivable1_orp_intros1.
  assert (problem_95_spec_z rows 0) as Hspec.
  { apply problem_95_spec_z_zero_invalid_95 with
      (n := dict_size_pre) (k := k) (i := i)
      (islower := islower) (isupper := isupper); try assumption; try lia.
    unfold letter_char_z_95, lower_char_z_95, upper_char_z_95. lia. }
  entailer!.
  pose proof (CharPtrArray2.missing_i_merge_to_full
                keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
            (Zlength (Znth k rows nil)) (Znth k rows nil)) with
         (CharArray.full row_ptr
            (Zlength (Znth k rows nil)) (Znth k rows nil)) in Hmerge.
  rewrite sizeof_ptr. sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia. cancel.
Qed.

Lemma proof_of_check_dict_case_return_wit_7 : check_dict_case_return_wit_7.
Proof.
  unfold check_dict_case_return_wit_7. intros.
  rewrite <- derivable1_orp_intros1.
  assert (problem_95_spec_z rows 0) as Hspec.
  { exact (problem_95_spec_z_zero_empty_95 rows dict_size_pre PreH4 PreH1). }
  entailer!.
Qed.
