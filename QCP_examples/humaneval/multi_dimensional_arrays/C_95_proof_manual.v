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

Lemma proof_of_check_dict_case_safety_wit_33_split_goal_1 : check_dict_case_safety_wit_33_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_safety_wit_33_split_goal_2 : check_dict_case_safety_wit_33_split_goal_2.
Proof. Abort.

Lemma proof_of_check_dict_case_safety_wit_33 : check_dict_case_safety_wit_33.
Proof.
  pre_process_default; unfold scan_state_z in *; try entailer!; try lia.
Qed.

Lemma proof_of_check_dict_case_safety_wit_34_split_goal_1 : check_dict_case_safety_wit_34_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_safety_wit_34_split_goal_2 : check_dict_case_safety_wit_34_split_goal_2.
Proof. Abort.

Lemma proof_of_check_dict_case_safety_wit_34 : check_dict_case_safety_wit_34.
Proof.
  pre_process_default; unfold scan_state_z in *; try entailer!; try lia.
Qed.

Lemma proof_of_check_dict_case_safety_wit_39_split_goal_1 : check_dict_case_safety_wit_39_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_safety_wit_39_split_goal_2 : check_dict_case_safety_wit_39_split_goal_2.
Proof. Abort.

Lemma proof_of_check_dict_case_safety_wit_39 : check_dict_case_safety_wit_39.
Proof.
  pre_process_default; unfold scan_state_z in *; try entailer!; try lia.
  destruct PreH17 as [_ Hrow].
  specialize (Hrow k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_check_dict_case_safety_wit_40_split_goal_1 : check_dict_case_safety_wit_40_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_safety_wit_40_split_goal_2 : check_dict_case_safety_wit_40_split_goal_2.
Proof. Abort.

Lemma proof_of_check_dict_case_safety_wit_40 : check_dict_case_safety_wit_40.
Proof.
  pre_process_default; unfold scan_state_z in *; try entailer!; try lia.
  destruct PreH15 as [_ Hrow].
  specialize (Hrow k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_check_dict_case_entail_wit_1_split_goal_1 : check_dict_case_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_1 : check_dict_case_entail_wit_1.
Proof.
  pre_process_default; unfold scan_state_z, rows_well_formed_z in *; try entailer!; try cancel; try lia.
  eapply problem_95_spec_z_empty; eauto.
Qed.

Lemma proof_of_check_dict_case_entail_wit_2_split_goal_1 : check_dict_case_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_2 : check_dict_case_entail_wit_2.
Proof.
  pre_process_default; try entailer!; try cancel; try lia.
  apply scan_state_z_initial.
Qed.

Lemma proof_of_check_dict_case_entail_wit_3_split_goal_spatial : check_dict_case_entail_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_3 : check_dict_case_entail_wit_3.
Proof.
  pre_process_default.
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i keys_pre k dict_size_pre rows).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth k rows nil)) (Znth k rows nil))
      with (CharArray.full row_ptr (Zlength (Znth k rows nil)) (Znth k rows nil)).
    entailer!.
Qed.

Lemma proof_of_check_dict_case_entail_wit_5_split_goal_1 : check_dict_case_entail_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_5 : check_dict_case_entail_wit_5.
Proof.
  pre_process_default; try entailer!; try cancel; try lia.
  destruct PreH5 as [_ Hrow].
  specialize (Hrow k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_check_dict_case_entail_wit_6_1_split_goal_1 : check_dict_case_entail_wit_6_1_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_6_1_split_goal_2 : check_dict_case_entail_wit_6_1_split_goal_2.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_6_1 : check_dict_case_entail_wit_6_1.
Proof.
  pre_process_default; try entailer!; try cancel; try lia.
  - eapply scan_state_z_lower_step with (dict_size := dict_size_pre); eauto; try lia.
    unfold lower_char_z; lia.
  - eapply payload_index_from_nonzero in PreH17; eauto; unfold payload_index_z in *; lia.
Qed.

Lemma proof_of_check_dict_case_entail_wit_6_2_split_goal_1 : check_dict_case_entail_wit_6_2_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_6_2_split_goal_2 : check_dict_case_entail_wit_6_2_split_goal_2.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_6_2 : check_dict_case_entail_wit_6_2.
Proof.
  pre_process_default; try entailer!; try cancel; try lia.
  - eapply scan_state_z_upper_step with (dict_size := dict_size_pre); eauto; try lia.
    unfold upper_char_z; lia.
  - eapply payload_index_from_nonzero in PreH15; eauto; unfold payload_index_z in *; lia.
Qed.

Lemma proof_of_check_dict_case_entail_wit_7_split_goal_1 : check_dict_case_entail_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_7_split_goal_2 : check_dict_case_entail_wit_7_split_goal_2.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_7_split_goal_3 : check_dict_case_entail_wit_7_split_goal_3.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_7_split_goal_4 : check_dict_case_entail_wit_7_split_goal_4.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_7_split_goal_5 : check_dict_case_entail_wit_7_split_goal_5.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_7_split_goal_spatial : check_dict_case_entail_wit_7_split_goal_spatial.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_7 : check_dict_case_entail_wit_7.
Proof.
  pre_process_default; try entailer!; try lia.
  all: try solve [
    eapply scan_state_z_finish_row with (dict_size := dict_size_pre) (i := i); eauto; try lia
  ].
  all: try solve [
    unfold scan_state_z in PreH10;
    destruct PreH10 as [_ [_ [_ [Hislower [Hisupper _]]]]]; lia
  ].
  pose proof (CharPtrArray2.missing_i_merge_to_full
        keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  try rewrite sizeof_ptr in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth k rows nil)) (Znth k rows nil))
    with (CharArray.full row_ptr (Zlength (Znth k rows nil)) (Znth k rows nil)) in Hmerge.
  try rewrite sizeof_ptr.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.

Lemma proof_of_check_dict_case_return_wit_1 : check_dict_case_return_wit_1.
Proof.
  pre_process_default.
  assert (Hk_eq : k = dict_size_pre) by lia.
  subst k.
  assert (Huniform : rows_have_uniform_case_z rows).
  { eapply scan_state_z_done_uniform; eauto. }
  assert (Hspec : problem_95_spec_z rows 1).
  { eapply problem_95_spec_z_success; eauto. }
  eapply derivable1_trans with
    (y := “ 1 = 1 ” &&
          (“ problem_95_spec_z rows 1 ” &&
           CharPtrArray2.full keys_pre dict_size_pre rows)).
  - entailer!.
  - apply derivable1_orp_intros2.
Qed.

Lemma proof_of_check_dict_case_return_wit_2 : check_dict_case_return_wit_2.
Proof.
  pre_process_default.
  eapply derivable1_trans with
    (y := “ 0 = 0 ” &&
          (“ problem_95_spec_z rows 0 ” &&
           CharPtrArray2.full keys_pre dict_size_pre rows)).
  - pose proof (CharPtrArray2.missing_i_merge_to_full
          keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr in Hmerge.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth k rows nil)) (Znth k rows nil))
      with (CharArray.full row_ptr (Zlength (Znth k rows nil)) (Znth k rows nil)) in Hmerge.
    try rewrite sizeof_ptr.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    entailer!.
    apply problem_95_spec_z_mixed with (dict_size := dict_size_pre) (k := k) (i := i + 1); eauto.
    eapply mixed_case_seen_lower_intro with (dict_size := dict_size_pre); eauto; try lia.
    unfold lower_char_z; lia.
  - apply derivable1_orp_intros1.
Qed.

Lemma proof_of_check_dict_case_return_wit_3 : check_dict_case_return_wit_3.
Proof.
  pre_process_default.
  eapply derivable1_trans with
    (y := “ 0 = 0 ” &&
          (“ problem_95_spec_z rows 0 ” &&
           CharPtrArray2.full keys_pre dict_size_pre rows)).
  - pose proof (CharPtrArray2.missing_i_merge_to_full
          keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr in Hmerge.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth k rows nil)) (Znth k rows nil))
      with (CharArray.full row_ptr (Zlength (Znth k rows nil)) (Znth k rows nil)) in Hmerge.
    try rewrite sizeof_ptr.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    entailer!.
    apply problem_95_spec_z_mixed with (dict_size := dict_size_pre) (k := k) (i := i + 1); eauto.
    eapply mixed_case_seen_upper_intro with (dict_size := dict_size_pre); eauto; try lia.
    unfold upper_char_z; lia.
  - apply derivable1_orp_intros1.
Qed.

Lemma proof_of_check_dict_case_return_wit_4 : check_dict_case_return_wit_4.
Proof.
  pre_process_default.
  eapply derivable1_trans with
    (y := “ 0 = 0 ” &&
          (“ problem_95_spec_z rows 0 ” &&
           CharPtrArray2.full keys_pre dict_size_pre rows)).
  - pose proof (CharPtrArray2.missing_i_merge_to_full
          keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr in Hmerge.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth k rows nil)) (Znth k rows nil))
      with (CharArray.full row_ptr (Zlength (Znth k rows nil)) (Znth k rows nil)) in Hmerge.
    try rewrite sizeof_ptr.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    entailer!.
    apply problem_95_spec_z_invalid with (dict_size := dict_size_pre) (k := k) (i := i); eauto.
    eapply invalid_char_seen_intro with (dict_size := dict_size_pre); eauto; try lia.
    unfold letter_char_z, lower_char_z, upper_char_z; lia.
  - apply derivable1_orp_intros1.
Qed.

Lemma proof_of_check_dict_case_return_wit_5 : check_dict_case_return_wit_5.
Proof.
  pre_process_default.
  eapply derivable1_trans with
    (y := “ 0 = 0 ” &&
          (“ problem_95_spec_z rows 0 ” &&
           CharPtrArray2.full keys_pre dict_size_pre rows)).
  - pose proof (CharPtrArray2.missing_i_merge_to_full
          keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr in Hmerge.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth k rows nil)) (Znth k rows nil))
      with (CharArray.full row_ptr (Zlength (Znth k rows nil)) (Znth k rows nil)) in Hmerge.
    try rewrite sizeof_ptr.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    entailer!.
    apply problem_95_spec_z_invalid with (dict_size := dict_size_pre) (k := k) (i := i); eauto.
    eapply invalid_char_seen_intro with (dict_size := dict_size_pre); eauto; try lia.
    unfold letter_char_z, lower_char_z, upper_char_z; lia.
  - apply derivable1_orp_intros1.
Qed.

Lemma proof_of_check_dict_case_return_wit_6 : check_dict_case_return_wit_6.
Proof.
  pre_process_default.
  eapply derivable1_trans with
    (y := “ 0 = 0 ” &&
          (“ problem_95_spec_z rows 0 ” &&
           CharPtrArray2.full keys_pre dict_size_pre rows)).
  - pose proof (CharPtrArray2.missing_i_merge_to_full
          keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    try rewrite sizeof_ptr in Hmerge.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth k rows nil)) (Znth k rows nil))
      with (CharArray.full row_ptr (Zlength (Znth k rows nil)) (Znth k rows nil)) in Hmerge.
    try rewrite sizeof_ptr.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    entailer!.
    apply problem_95_spec_z_invalid with (dict_size := dict_size_pre) (k := k) (i := i); eauto.
    eapply invalid_char_seen_intro with (dict_size := dict_size_pre); eauto; try lia.
    unfold letter_char_z, lower_char_z, upper_char_z; lia.
  - apply derivable1_orp_intros1.
Qed.
