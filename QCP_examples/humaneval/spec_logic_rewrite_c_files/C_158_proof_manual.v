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
From SimpleC.EE Require Import C_158_goal.
From SimpleC.EE Require Import C_158_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_158.
Local Open Scope sac.

Lemma proof_of_find_max_entail_wit_1 : find_max_entail_wit_1.
Proof.
  left. pre_process. entailer!.
  left. repeat split; lia.
Qed.

Lemma proof_of_find_max_entail_wit_2 : find_max_entail_wit_2.
Proof.
  left. pre_process.
  Exists (@nil Z).
  sep_apply (IntArray.undef_full_split_to_undef_seg ( &( "seen" ) ) 0 256).
  rewrite IntArray.seg_empty.
  rewrite (IntArray.undef_seg_empty ( &( "seen" ) ) 0).
  entailer!.
  lia.
Qed.

Lemma proof_of_find_max_entail_wit_3 : find_max_entail_wit_3.
Proof.
  left. pre_process.
  Exists (repeat_Z 0 (k + 1)).
  subst zeros_2.
  rewrite repeat_Z_tail by lia.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_4 : find_max_entail_wit_4.
Proof.
  left. pre_process.
  assert (Hk : k = 256) by lia.
  subst k.
  subst zeros.
  rewrite IntArray.undef_seg_empty.
  sep_apply_l_atomic (IntArray.seg_to_full ( &( "seen" ) ) 0 256 (repeat_Z 0 256)).
  replace ( &( "seen" ) + 0 * sizeof ( INT )) with ( &( "seen" ) ) by lia.
  replace (256 - 0) with 256 by lia.
  assert (Hrows_len : Zlength rows = words_size_pre).
  { unfold rows_well_formed_158 in PreH14. tauto. }
  assert (Hi_ptr : 0 <= i < Zlength ptrs) by lia.
  assert (Hptr_rows : Zlength ptrs = Zlength rows) by lia.
  sep_apply_l_atomic (row_stores_split_i_158 ptrs rows i Hi_ptr Hptr_rows).
  subst cur.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_5 : find_max_entail_wit_5.
Proof.
  left. pre_process.
  Exists (repeat_Z 0 256).
  entailer!.
  - pose proof (best_state_bounds_158 rows i best maxu words_size_pre ltac:(lia) ltac:(lia) PreH13).
    lia.
  - pose proof (best_state_bounds_158 rows i best maxu words_size_pre ltac:(lia) ltac:(lia) PreH13).
    lia.
  - subst retval. unfold string_length. apply Zlength_nonneg.
Qed.

Lemma proof_of_find_max_entail_wit_6 : find_max_entail_wit_6.
Proof.
  left. pre_process.
  Exists seen_l_2.
  entailer!.
  - rewrite c_string_Znth_inside by (rewrite <- PreH4; lia).
    reflexivity.
  - rewrite c_string_Znth_inside by (rewrite <- PreH4; lia).
    + assert (Hlen_rows : Zlength rows = words_size_pre).
      { unfold rows_well_formed_158 in PreH18. tauto. }
      assert (Hforall : Forall row_well_formed_158 rows).
      { unfold rows_well_formed_158 in PreH18. tauto. }
      assert (Hrowwf : row_well_formed_158 (Znth i rows nil)).
      {
        apply Forall_forall with (x := Znth i rows nil) in Hforall; auto.
        apply Znth_In_range_158. lia.
      }
      pose proof (row_well_formed_char_range_158 (Znth i rows nil) j Hrowwf
        ltac:(unfold string_length, SeparationLogic.naive_C_Rules.string_length in *; lia)).
      lia.
  - rewrite c_string_Znth_inside by (rewrite <- PreH4; lia).
    + assert (Hlen_rows : Zlength rows = words_size_pre).
      { unfold rows_well_formed_158 in PreH18. tauto. }
      assert (Hforall : Forall row_well_formed_158 rows).
      { unfold rows_well_formed_158 in PreH18. tauto. }
      assert (Hrowwf : row_well_formed_158 (Znth i rows nil)).
      {
        apply Forall_forall with (x := Znth i rows nil) in Hforall; auto.
        apply Znth_In_range_158. lia.
      }
      pose proof (row_well_formed_char_range_158 (Znth i rows nil) j Hrowwf
        ltac:(unfold string_length, SeparationLogic.naive_C_Rules.string_length in *; lia)).
      lia.
Qed.

Lemma proof_of_find_max_entail_wit_7_1 : find_max_entail_wit_7_1.
Proof.
  left. pre_process.
  Exists (replace_Znth ch 1 seen_l_2).
  entailer!.
  eapply seen_state_step_zero_158; eauto;
    unfold string_length, SeparationLogic.naive_C_Rules.string_length in *; lia.
Qed.

Lemma proof_of_find_max_entail_wit_7_2 : find_max_entail_wit_7_2.
Proof.
  left. pre_process.
  Exists seen_l_2.
  entailer!.
  eapply seen_state_step_nonzero_158; eauto;
    unfold string_length, SeparationLogic.naive_C_Rules.string_length in *; lia.
Qed.

Lemma proof_of_find_max_entail_wit_8 : find_max_entail_wit_8.
Proof.
  left. pre_process.
  assert (j = len) by lia.
  subst j.
  assert (Hunique : unique = unique_count_z_158 (Znth i rows nil)).
  {
    eapply seen_state_done_158; eauto.
  }
  assert (Hrows_len : Zlength rows = words_size_pre).
  { unfold rows_well_formed_158 in PreH18. tauto. }
  assert (Hi_ptr : 0 <= i < Zlength ptrs) by lia.
  assert (Hptr_rows : Zlength ptrs = Zlength rows) by lia.
  subst cur.
  sep_apply_l_atomic (row_stores_merge_i_158 ptrs rows i Hi_ptr Hptr_rows).
  Exists seen_l_2.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_9 : find_max_entail_wit_9.
Proof.
  left. pre_process.
  Exists seen_l_2.
  assert (Hrows_len : Zlength rows = words_size_pre).
  { unfold rows_well_formed_158 in PreH15. tauto. }
  pose proof (best_state_before_i_158 rows i best maxu PreH16 PreH1) as Hbest_before.
  assert (Hbi : 0 <= best /\ best < i /\ i < Zlength ptrs) by lia.
  assert (Hptr_rows : Zlength ptrs = Zlength rows) by lia.
  sep_apply_l_atomic (row_stores_split_two_158 ptrs rows best i Hbi Hptr_rows).
  subst cur max.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_10 : find_max_entail_wit_10.
Proof.
  left. pre_process.
  Exists seen_l_2.
  assert (Hrows_len : Zlength rows = words_size_pre).
  { unfold rows_well_formed_158 in PreH19. tauto. }
  assert (Hbi : 0 <= best /\ best < i /\ i < Zlength ptrs) by lia.
  assert (Hptr_rows : Zlength ptrs = Zlength rows) by lia.
  subst cur max.
  sep_apply_l_atomic (row_stores_merge_two_158 ptrs rows best i Hbi Hptr_rows).
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_11_1 : find_max_entail_wit_11_1.
Proof.
  left. pre_process.
  Exists seen_l_2.
  assert (Hnext : best_state_158 rows (i + 1) best maxu).
  {
    eapply best_state_keep_self_158; eauto; lia.
  }
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_11_2 : find_max_entail_wit_11_2.
Proof.
  left. pre_process.
  Exists seen_l_2.
  assert (Hnext : best_state_158 rows (i + 1) best maxu).
  {
    eapply best_state_keep_lower_158; eauto; lia.
  }
  pose proof (best_state_bounds_158 rows i best maxu words_size_pre
    ltac:(lia) ltac:(lia) PreH15) as Hbounds.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_11_3 : find_max_entail_wit_11_3.
Proof.
  left. pre_process.
  Exists seen_l_2.
  assert (Hcur_wf : row_well_formed_158 (Znth i rows nil)).
  { eapply rows_well_formed_Znth_158; eauto; lia. }
  assert (Hbest_wf : row_well_formed_158 (Znth best rows nil)).
  { eapply rows_well_formed_Znth_158; eauto; lia. }
  pose proof (strcmp_result_nonneg_string_le_158
    (Znth i rows nil) (Znth best rows nil) cmp
    Hcur_wf Hbest_wf PreH13 PreH2) as Hlex.
  assert (Hnext : best_state_158 rows (i + 1) best maxu).
  {
    eapply best_state_keep_tie_158; eauto; lia.
  }
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_11_4 : find_max_entail_wit_11_4.
Proof.
  left. pre_process.
  Exists seen_l_2.
  assert (Hcur_wf : row_well_formed_158 (Znth i rows nil)).
  { eapply rows_well_formed_Znth_158; eauto; lia. }
  assert (Hbest_wf : row_well_formed_158 (Znth best rows nil)).
  { eapply rows_well_formed_Znth_158; eauto; lia. }
  pose proof (strcmp_result_neg_string_le_158
    (Znth i rows nil) (Znth best rows nil) cmp
    Hcur_wf Hbest_wf PreH12 PreH1) as Hlex.
  assert (Hnext : best_state_158 rows (i + 1) i unique).
  {
    eapply best_state_update_tie_158; eauto; lia.
  }
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_11_5 : find_max_entail_wit_11_5.
Proof.
  left. pre_process.
  Exists seen_l_2.
  assert (Hnext : best_state_158 rows (i + 1) i unique).
  {
    eapply best_state_update_strict_158; eauto; lia.
  }
  entailer!.
Qed.

Lemma proof_of_find_max_return_wit_1 : find_max_return_wit_1.
Proof.
  left. pre_process.
  Exists best_2.
  assert (Hi_eq : i = words_size_pre) by lia.
  subst i.
  assert (Hspec : problem_158_spec_z rows (Znth best_2 rows nil)).
  {
    eapply best_state_problem_spec_z_158; eauto; lia.
  }
  entailer!.
Qed.

Lemma proof_of_find_max_partial_solve_wit_4_pure : find_max_partial_solve_wit_4_pure.
Proof.
  left. pre_process.
  assert (Hrow_wf : row_well_formed_158 (Znth i rows nil)).
  { eapply rows_well_formed_Znth_158; eauto; lia. }
  unfold row_well_formed_158 in Hrow_wf.
  destruct Hrow_wf as [Hrow_valid Hrow_len].
  entailer!.
Qed.

Lemma proof_of_find_max_partial_solve_wit_7_pure : find_max_partial_solve_wit_7_pure.
Proof.
  left. pre_process.
  assert (Hcur_wf : row_well_formed_158 (Znth i rows nil)).
  { eapply rows_well_formed_Znth_158; eauto; lia. }
  assert (Hbest_wf : row_well_formed_158 (Znth best rows nil)).
  { eapply rows_well_formed_Znth_158; eauto; lia. }
  unfold row_well_formed_158 in Hcur_wf, Hbest_wf.
  destruct Hcur_wf as [Hcur_valid Hcur_len].
  destruct Hbest_wf as [Hbest_valid Hbest_len].
  entailer!.
Qed.
