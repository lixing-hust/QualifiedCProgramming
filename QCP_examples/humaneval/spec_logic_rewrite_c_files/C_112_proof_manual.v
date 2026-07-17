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
From SimpleC.EE Require Import C_112_goal.
From SimpleC.EE Require Import C_112_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.coins_112.
Local Open Scope sac.

Lemma proof_of_reverse_delete_safety_wit_19_split_goal_1 : reverse_delete_safety_wit_19_split_goal_1.
Proof.
  pre_process.
  pose proof (filter_not_in_z_112_length_le input removed) as Hlen.
  pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)) as Hnonneg.
  pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)) as Hidx.
  unfold string_length in *; entailer!.
Qed.

Lemma proof_of_reverse_delete_safety_wit_19_split_goal_2 : reverse_delete_safety_wit_19_split_goal_2.
Proof.
  pre_process.
  pose proof (filter_not_in_z_112_length_le input removed) as Hlen.
  pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)) as Hnonneg.
  pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)) as Hidx.
  unfold string_length in *; entailer!.
Qed.

Lemma proof_of_reverse_delete_safety_wit_19 : reverse_delete_safety_wit_19.
Proof.
  pre_process.
  all: pose proof (filter_not_in_z_112_length_le input removed) as Hlen;
       pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)) as Hnonneg;
       pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)) as Hidx;
       unfold string_length in *; entailer!.
Qed.
Lemma proof_of_reverse_delete_safety_wit_20_split_goal_1 : reverse_delete_safety_wit_20_split_goal_1.
Proof.
  pre_process.
  pose proof (filter_not_in_z_112_length_le input removed) as Hlen.
  pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)) as Hnonneg.
  pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)) as Hidx.
  unfold string_length in *; entailer!.
Qed.

Lemma proof_of_reverse_delete_safety_wit_20_split_goal_2 : reverse_delete_safety_wit_20_split_goal_2.
Proof.
  pre_process.
  pose proof (filter_not_in_z_112_length_le input removed) as Hlen.
  pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)) as Hnonneg.
  pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)) as Hidx.
  unfold string_length in *; entailer!.
Qed.

Lemma proof_of_reverse_delete_safety_wit_20 : reverse_delete_safety_wit_20.
Proof.
  pre_process.
  all: pose proof (filter_not_in_z_112_length_le input removed) as Hlen;
       pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)) as Hnonneg;
       pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)) as Hidx;
       unfold string_length in *; entailer!.
Qed.
Lemma proof_of_reverse_delete_safety_wit_21_split_goal_1 : reverse_delete_safety_wit_21_split_goal_1.
Proof. pre_process; pose proof (filter_not_in_z_112_length_le input removed); pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)); pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)); unfold string_length in *; entailer!. Qed.

Lemma proof_of_reverse_delete_safety_wit_21_split_goal_2 : reverse_delete_safety_wit_21_split_goal_2.
Proof. pre_process; pose proof (filter_not_in_z_112_length_le input removed); pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)); pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)); unfold string_length in *; entailer!. Qed.

Lemma proof_of_reverse_delete_safety_wit_21 : reverse_delete_safety_wit_21.
Proof. pre_process. all: pose proof (filter_not_in_z_112_length_le input removed); pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)); pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)); unfold string_length in *; entailer!. Qed.
Lemma proof_of_reverse_delete_safety_wit_22_split_goal_1 : reverse_delete_safety_wit_22_split_goal_1.
Proof. pre_process; pose proof (filter_not_in_z_112_length_le input removed); pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)); pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)); unfold string_length in *; entailer!. Qed.

Lemma proof_of_reverse_delete_safety_wit_22_split_goal_2 : reverse_delete_safety_wit_22_split_goal_2.
Proof. pre_process; pose proof (filter_not_in_z_112_length_le input removed); pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)); pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)); unfold string_length in *; entailer!. Qed.

Lemma proof_of_reverse_delete_safety_wit_22 : reverse_delete_safety_wit_22.
Proof. pre_process. all: pose proof (filter_not_in_z_112_length_le input removed); pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)); pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)); unfold string_length in *; entailer!. Qed.
Lemma proof_of_reverse_delete_safety_wit_27_split_goal_1 : reverse_delete_safety_wit_27_split_goal_1.
Proof. pre_process; pose proof (filter_not_in_z_112_length_le input removed); pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)); pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)); unfold string_length in *; entailer!. Qed.

Lemma proof_of_reverse_delete_safety_wit_27_split_goal_2 : reverse_delete_safety_wit_27_split_goal_2.
Proof. pre_process; pose proof (filter_not_in_z_112_length_le input removed); pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)); pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)); unfold string_length in *; entailer!. Qed.

Lemma proof_of_reverse_delete_safety_wit_27 : reverse_delete_safety_wit_27.
Proof. pre_process. all: pose proof (filter_not_in_z_112_length_le input removed); pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)); pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)); unfold string_length in *; entailer!. Qed.
Lemma proof_of_reverse_delete_safety_wit_28_split_goal_1 : reverse_delete_safety_wit_28_split_goal_1.
Proof. pre_process; pose proof (filter_not_in_z_112_length_le input removed); pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)); pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)); unfold string_length in *; entailer!. Qed.

Lemma proof_of_reverse_delete_safety_wit_28_split_goal_2 : reverse_delete_safety_wit_28_split_goal_2.
Proof. pre_process; pose proof (filter_not_in_z_112_length_le input removed); pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)); pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)); unfold string_length in *; entailer!. Qed.

Lemma proof_of_reverse_delete_safety_wit_28 : reverse_delete_safety_wit_28.
Proof. pre_process. all: pose proof (filter_not_in_z_112_length_le input removed); pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)); pose proof (palindrome_index_bounds_112 m i ltac:(lia) ltac:(lia)); unfold string_length in *; entailer!. Qed.
Lemma proof_of_reverse_delete_entail_wit_1_split_goal_1 : reverse_delete_entail_wit_1_split_goal_1.
Proof. pre_process; pose proof (filter_prefix_state_112_zero input removed); entailer!. Qed.

Lemma proof_of_reverse_delete_entail_wit_1_split_goal_2 : reverse_delete_entail_wit_1_split_goal_2.
Proof. pre_process; pose proof (string_length_nonneg input); entailer!. Qed.

Lemma proof_of_reverse_delete_entail_wit_1_split_goal_3 : reverse_delete_entail_wit_1_split_goal_3.
Proof. pre_process; entailer!. Qed.

Lemma proof_of_reverse_delete_entail_wit_1_split_goal_spatial : reverse_delete_entail_wit_1_split_goal_spatial.
Proof. pre_process; subst s_pre; subst c_pre; entailer!. Qed.

Lemma proof_of_reverse_delete_entail_wit_1 : reverse_delete_entail_wit_1.
Proof.
  unfold reverse_delete_entail_wit_1; right.
  pre_process.
  pose proof (filter_prefix_state_112_zero input removed).
  pose proof (string_length_nonneg input).
  subst s_pre; subst c_pre; entailer!.
Qed.
Lemma proof_of_reverse_delete_entail_wit_2_split_goal_1 : reverse_delete_entail_wit_2_split_goal_1.
Proof. pre_process; pose proof (c_string_char_bound input i ltac:(assumption) ltac:(unfold string_length in *; lia)); entailer!. Qed.

Lemma proof_of_reverse_delete_entail_wit_2_split_goal_2 : reverse_delete_entail_wit_2_split_goal_2.
Proof. pre_process; pose proof (c_string_char_bound input i ltac:(assumption) ltac:(unfold string_length in *; lia)); entailer!. Qed.

Lemma proof_of_reverse_delete_entail_wit_2_split_goal_3 : reverse_delete_entail_wit_2_split_goal_3.
Proof. pre_process; entailer!. Qed.

Lemma proof_of_reverse_delete_entail_wit_2 : reverse_delete_entail_wit_2.
Proof.
  unfold reverse_delete_entail_wit_2; right; pre_process.
  pose proof (c_string_char_bound input i ltac:(assumption) ltac:(unfold string_length in *; lia)).
  entailer!.
Qed.
Lemma proof_of_reverse_delete_entail_wit_3_1_split_goal_1 : reverse_delete_entail_wit_3_1_split_goal_1.
Proof.
  pre_process.
  assert (Hi : 0 <= i < string_length input) by lia.
  pose proof (c_string_inside_nonzero_112 input i ltac:(assumption) Hi) as Hnz.
  assert (Hch : ch <> 0) by congruence.
  pose proof (strchr_result_zero_not_in_112 removed ch retval c0 Hch PreH1 PreH2) as Hnot.
  pose proof (filter_prefix_state_112_step_keep input removed i filtered_l_2 ch ltac:(unfold string_length in Hi; exact Hi) PreH11 Hnot PreH22) as Hstep.
  entailer!.
Qed.

Lemma proof_of_reverse_delete_entail_wit_3_1_split_goal_2 : reverse_delete_entail_wit_3_1_split_goal_2.
Proof. pre_process; rewrite Zlength_app, Zlength_cons, Zlength_nil; entailer!. Qed.

Lemma proof_of_reverse_delete_entail_wit_3_1 : reverse_delete_entail_wit_3_1.
Proof.
  unfold reverse_delete_entail_wit_3_1; right; pre_process.
  assert (Hi : 0 <= i < string_length input) by lia.
  pose proof (c_string_inside_nonzero_112 input i ltac:(assumption) Hi) as Hnz.
  assert (Hch : ch <> 0) by congruence.
  pose proof (strchr_result_zero_not_in_112 removed ch retval c0 Hch PreH1 PreH2) as Hnot.
  pose proof (filter_prefix_state_112_step_keep input removed i filtered_l_2 ch ltac:(unfold string_length in Hi; exact Hi) PreH11 Hnot PreH22) as Hstep.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!.
Qed.
Lemma proof_of_reverse_delete_entail_wit_3_2_split_goal_1 : reverse_delete_entail_wit_3_2_split_goal_1.
Proof.
  pre_process.
  assert (Hi : 0 <= i < string_length input) by lia.
  pose proof (c_string_inside_nonzero_112 input i ltac:(assumption) Hi) as Hnz.
  assert (Hch : ch <> 0) by congruence.
  pose proof (strchr_result_nonzero_in_112 removed ch retval c0 Hch PreH1 PreH2) as Hin.
  pose proof (filter_prefix_state_112_step_drop input removed i filtered_l_2 ch ltac:(unfold string_length in Hi; exact Hi) PreH11 Hin PreH22) as Hstep.
  entailer!.
Qed.

Lemma proof_of_reverse_delete_entail_wit_3_2 : reverse_delete_entail_wit_3_2.
Proof.
  unfold reverse_delete_entail_wit_3_2; right; pre_process.
  assert (Hi : 0 <= i < string_length input) by lia.
  pose proof (c_string_inside_nonzero_112 input i ltac:(assumption) Hi) as Hnz.
  assert (Hch : ch <> 0) by congruence.
  pose proof (strchr_result_nonzero_in_112 removed ch retval c0 Hch PreH1 PreH2) as Hin.
  pose proof (filter_prefix_state_112_step_drop input removed i filtered_l_2 ch ltac:(unfold string_length in Hi; exact Hi) PreH11 Hin PreH22) as Hstep.
  entailer!.
Qed.
Lemma proof_of_reverse_delete_entail_wit_4_split_goal_1 : reverse_delete_entail_wit_4_split_goal_1.
Proof.
  pre_process.
  assert (Hi : i = Zlength input) by (unfold string_length in *; lia).
  pose proof (filter_prefix_state_112_done input removed i filtered_l Hi PreH19) as Hdone.
  subst filtered_l.
  entailer!.
Qed.

Lemma proof_of_reverse_delete_entail_wit_4_split_goal_spatial : reverse_delete_entail_wit_4_split_goal_spatial.
Proof.
  pre_process.
  assert (Hi : i = Zlength input) by (unfold string_length in *; lia).
  pose proof (filter_prefix_state_112_done input removed i filtered_l Hi PreH19) as Hdone.
  subst filtered_l; subst k; unfold store_string, c_string, string_length in *; entailer!.
Qed.

Lemma proof_of_reverse_delete_entail_wit_4 : reverse_delete_entail_wit_4.
Proof.
  unfold reverse_delete_entail_wit_4; right; pre_process.
  assert (Hi : i = Zlength input) by (unfold string_length in *; lia).
  pose proof (filter_prefix_state_112_done input removed i filtered_l Hi PreH19) as Hdone.
  subst filtered_l; subst k; unfold store_string, c_string, string_length in *; entailer!.
Qed.
Lemma proof_of_reverse_delete_entail_wit_6 : reverse_delete_entail_wit_6.
Proof.
  pre_process.
  pose proof (palindrome_scan_state_112_init (filter_not_in_z_112 input removed)).
  pose proof (Zlength_nonneg (filter_not_in_z_112 input removed)) as Hlen.
  pose proof (Z.quot_pos (Zlength (filter_not_in_z_112 input removed)) 2 Hlen ltac:(lia)).
  Left; entailer!.
  - subst pal; assumption.
  - rewrite PreH4; assumption.
Qed.
Lemma proof_of_reverse_delete_entail_wit_7_1_split_goal_1 : reverse_delete_entail_wit_7_1_split_goal_1.
Proof.
  pre_process.
  assert (Hi : 0 <= i < Zlength (filter_not_in_z_112 input removed) ÷ 2)
    by (rewrite <- PreH8; lia).
  rewrite PreH8 in PreH4.
  pose proof (palindrome_scan_state_112_mismatch
    (filter_not_in_z_112 input removed) i pal Hi PreH20 PreH4) as Hstep.
  entailer!.
Qed.

Lemma proof_of_reverse_delete_entail_wit_7_1 : reverse_delete_entail_wit_7_1.
Proof.
  unfold reverse_delete_entail_wit_7_1; right; pre_process.
  assert (Hi : 0 <= i < Zlength (filter_not_in_z_112 input removed) ÷ 2)
    by (rewrite <- PreH8; lia).
  rewrite PreH8 in PreH4.
  pose proof (palindrome_scan_state_112_mismatch
    (filter_not_in_z_112 input removed) i pal Hi PreH20 PreH4) as Hstep.
  entailer!.
Qed.
Lemma proof_of_reverse_delete_entail_wit_7_2_split_goal_1 : reverse_delete_entail_wit_7_2_split_goal_1.
Proof.
  pre_process.
  assert (Hi : 0 <= i < Zlength (filter_not_in_z_112 input removed) ÷ 2)
    by (rewrite <- PreH8; lia).
  rewrite PreH8 in PreH4.
  pose proof (palindrome_scan_state_112_mismatch
    (filter_not_in_z_112 input removed) i pal Hi PreH20 PreH4) as Hstep.
  entailer!.
Qed.

Lemma proof_of_reverse_delete_entail_wit_7_2 : reverse_delete_entail_wit_7_2.
Proof.
  unfold reverse_delete_entail_wit_7_2; right; pre_process.
  assert (Hi : 0 <= i < Zlength (filter_not_in_z_112 input removed) ÷ 2)
    by (rewrite <- PreH8; lia).
  rewrite PreH8 in PreH4.
  pose proof (palindrome_scan_state_112_mismatch
    (filter_not_in_z_112 input removed) i pal Hi PreH20 PreH4) as Hstep.
  entailer!.
Qed.
Lemma proof_of_reverse_delete_entail_wit_8_1 : reverse_delete_entail_wit_8_1.
Proof.
  pre_process.
  assert (Hi : 0 <= i < Zlength (filter_not_in_z_112 input removed) ÷ 2)
    by (rewrite <- PreH5; lia).
  rewrite PreH5 in PreH1.
  subst pal.
  pose proof (palindrome_scan_state_112_equal_one
    (filter_not_in_z_112 input removed) i Hi PreH17 PreH1) as Hstep.
  Left; entailer!.
Qed.
Lemma proof_of_reverse_delete_entail_wit_8_2 : reverse_delete_entail_wit_8_2.
Proof.
  pre_process.
  assert (Hi : 0 <= i < Zlength (filter_not_in_z_112 input removed) ÷ 2)
    by (rewrite <- PreH5; lia).
  subst pal.
  pose proof (palindrome_scan_state_112_equal_zero
    (filter_not_in_z_112 input removed) i Hi PreH17) as Hstep.
  Right; entailer!.
Qed.
Lemma proof_of_reverse_delete_entail_wit_9_1 : reverse_delete_entail_wit_9_1.
Proof.
  pre_process; subst pal.
  pose proof (palindrome_result_112_false
    (filter_not_in_z_112 input removed) (i + 1) PreH15) as Hresult.
  Right; entailer!.
Qed.
Lemma proof_of_reverse_delete_entail_wit_9_2 : reverse_delete_entail_wit_9_2.
Proof.
  pre_process; subst pal.
  pose proof (palindrome_result_112_false
    (filter_not_in_z_112 input removed) i PreH16) as Hresult.
  Right; entailer!.
Qed.
Lemma proof_of_reverse_delete_entail_wit_9_3 : reverse_delete_entail_wit_9_3.
Proof.
  pre_process; subst pal.
  assert (Hi : i = Zlength (filter_not_in_z_112 input removed) ÷ 2)
    by (rewrite <- PreH4; lia).
  rewrite Hi in PreH16.
  pose proof (palindrome_result_112_true
    (filter_not_in_z_112 input removed) PreH16) as Hresult.
  Left; entailer!.
Qed.
Lemma proof_of_reverse_delete_return_wit_1 : reverse_delete_return_wit_1.
Proof.
  pre_process; subst pal_2.
  pose proof (problem_112_spec_z_bridge input removed 1
    PreH12 PreH13 PreH11 (or_intror eq_refl)) as Hspec.
  Left; Exists (filter_not_in_z_112 input removed) 1 retval filtered_2 data_2.
  unfold flag_payload_112; simpl Z.eqb.
  replace (retval + 0 * sizeof (CHAR)) with retval by lia.
  sep_apply (helper_chararray_point_to_full_single retval 84).
  sep_apply (helper_chararray_full_snoc retval 1 (84 :: nil) 114 ltac:(lia)).
  change (1 + 1) with 2;
    change ((84 :: nil) ++ 114 :: nil) with (84 :: 114 :: nil).
  sep_apply (helper_chararray_full_snoc retval 2 (84 :: 114 :: nil) 117 ltac:(lia)).
  change (2 + 1) with 3;
    change ((84 :: 114 :: nil) ++ 117 :: nil) with (84 :: 114 :: 117 :: nil).
  sep_apply (helper_chararray_full_snoc retval 3 (84 :: 114 :: 117 :: nil) 101 ltac:(lia)).
  change (3 + 1) with 4;
    change ((84 :: 114 :: 117 :: nil) ++ 101 :: nil)
      with (84 :: 114 :: 117 :: 101 :: nil).
  sep_apply (helper_chararray_full_snoc retval 4
    (84 :: 114 :: 117 :: 101 :: nil) 0 ltac:(lia)).
  change (4 + 1) with 5;
    change ((84 :: 114 :: 117 :: 101 :: nil) ++ 0 :: nil)
      with (84 :: 114 :: 117 :: 101 :: 0 :: nil).
  rewrite (PtrArray.undef_missing_i_unfold data_2 1 1 2 ltac:(lia)).
  rewrite (PtrArray.undef_seg_empty data_2 2).
  unfold PtrArray.full, store_array, store_string, c_string, string_length.
  simpl.
  entailer!.
  apply derivable1_orp_elim.
  - subst n; subst m; rewrite sizeof_ptr; subst k; entailer!.
  - entailer!.
Qed.
Lemma proof_of_reverse_delete_return_wit_2 : reverse_delete_return_wit_2.
Proof.
  pre_process; subst pal_2.
  pose proof (problem_112_spec_z_bridge input removed 0
    PreH12 PreH13 PreH11 (or_introl eq_refl)) as Hspec.
  Right; Exists (filter_not_in_z_112 input removed) 0 retval filtered_2 data_2.
  unfold flag_payload_112; simpl Z.eqb.
  replace (retval + 0 * sizeof (CHAR)) with retval by lia.
  sep_apply (helper_chararray_point_to_full_single retval 70).
  sep_apply (helper_chararray_full_snoc retval 1 (70 :: nil) 97 ltac:(lia)).
  change (1 + 1) with 2;
    change ((70 :: nil) ++ 97 :: nil) with (70 :: 97 :: nil).
  sep_apply (helper_chararray_full_snoc retval 2 (70 :: 97 :: nil) 108 ltac:(lia)).
  change (2 + 1) with 3;
    change ((70 :: 97 :: nil) ++ 108 :: nil) with (70 :: 97 :: 108 :: nil).
  sep_apply (helper_chararray_full_snoc retval 3
    (70 :: 97 :: 108 :: nil) 115 ltac:(lia)).
  change (3 + 1) with 4;
    change ((70 :: 97 :: 108 :: nil) ++ 115 :: nil)
      with (70 :: 97 :: 108 :: 115 :: nil).
  sep_apply (helper_chararray_full_snoc retval 4
    (70 :: 97 :: 108 :: 115 :: nil) 101 ltac:(lia)).
  change (4 + 1) with 5;
    change ((70 :: 97 :: 108 :: 115 :: nil) ++ 101 :: nil)
      with (70 :: 97 :: 108 :: 115 :: 101 :: nil).
  sep_apply (helper_chararray_full_snoc retval 5
    (70 :: 97 :: 108 :: 115 :: 101 :: nil) 0 ltac:(lia)).
  change (5 + 1) with 6;
    change ((70 :: 97 :: 108 :: 115 :: 101 :: nil) ++ 0 :: nil)
      with (70 :: 97 :: 108 :: 115 :: 101 :: 0 :: nil).
  rewrite (PtrArray.undef_missing_i_unfold data_2 1 1 2 ltac:(lia)).
  rewrite (PtrArray.undef_seg_empty data_2 2).
  unfold PtrArray.full, store_array, store_string, c_string, string_length.
  simpl.
  entailer!.
  apply derivable1_orp_elim.
  - subst n; subst m; rewrite sizeof_ptr; subst k; entailer!.
  - entailer!.
Qed.
Lemma proof_of_reverse_delete_partial_solve_wit_4_pure_split_goal_1 : reverse_delete_partial_solve_wit_4_pure_split_goal_1.
Proof.
  pre_process; subst retval.
  unfold string_length in *.
  pose proof (Zlength_nonneg input).
  entailer!.
Qed.

Lemma proof_of_reverse_delete_partial_solve_wit_4_pure : reverse_delete_partial_solve_wit_4_pure.
Proof.
  unfold reverse_delete_partial_solve_wit_4_pure.
  left.
  pre_process; subst retval.
  unfold string_length in *.
  pose proof (Zlength_nonneg input).
  entailer!.
Qed.
