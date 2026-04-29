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
From SimpleC.EE Require Import C_96_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_96.
Local Open Scope sac.

Lemma proof_of_count_up_to_safety_wit_12 : count_up_to_safety_wit_12.
Proof.
  pre_process.
  match goal with
  | Hs : count_up_to_state i output_l |- _ =>
      pose proof (count_up_to_state_Znth_prime i output_l j Hs ltac:(lia)) as [[Hz_ge _] _]
  end.
  replace (j - 0) with j by lia.
  entailer!.
Qed. 

Lemma proof_of_count_up_to_safety_wit_13 : count_up_to_safety_wit_13.
Proof.
  pre_process.
  match goal with
  | Hs : count_up_to_state i output_l |- _ =>
      pose proof (count_up_to_state_Znth_prime i output_l j Hs ltac:(lia)) as [[Hz_ge _] _]
  end.
  replace (j - 0) with j by lia.
  entailer!.
Qed. 

Lemma proof_of_count_up_to_entail_wit_1 : count_up_to_entail_wit_1.
Proof.
  pre_process.
  Left.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  apply count_up_to_state_init.
Qed. 

Lemma proof_of_count_up_to_entail_wit_2_1 : count_up_to_entail_wit_2_1.
Proof.
  pre_process.
  Exists output_l_2.
  entailer!.
  apply Zlength_nil_inv.
  lia.
Qed. 

Lemma proof_of_count_up_to_entail_wit_2_2 : count_up_to_entail_wit_2_2.
Proof.
  pre_process.
  Exists output_l_2.
  entailer!.
  apply Zlength_nil_inv.
  lia.
Qed. 

Lemma proof_of_count_up_to_entail_wit_3 : count_up_to_entail_wit_3.
Proof.
  pre_process.
  Exists output_l_2.
  entailer!.
  apply prime_test_state_init.
  lia.
Qed. 

Lemma proof_of_count_up_to_entail_wit_4 : count_up_to_entail_wit_4.
Proof.
  pre_process.
  Exists output_l_2.
  replace (j - 0) with j in * by lia.
  entailer!.
Qed.

Lemma proof_of_count_up_to_entail_wit_5_1 : count_up_to_entail_wit_5_1.
Proof.
  pre_process.
  Exists output_l_2.
  entailer!.
  eapply prime_test_state_step_zero; eauto; try lia.
  - match goal with
    | Hs : count_up_to_state i output_l_2 |- _ =>
        pose proof (count_up_to_state_Znth_prime i output_l_2 j Hs ltac:(lia)) as [[Hz_ge _] _]
    end.
    replace (j - 0) with j in * by lia.
    rewrite Z.quot_div_nonneg in H14 by lia.
    exact H14.
  - match goal with
    | Hs : count_up_to_state i output_l_2 |- _ =>
        pose proof (count_up_to_state_Znth_prime i output_l_2 j Hs ltac:(lia)) as [[Hz_ge _] _]
    end.
    replace (j - 0) with j in * by lia.
    rewrite Z.rem_mod_nonneg in H by lia.
    exact H.
Qed. 

Lemma proof_of_count_up_to_entail_wit_5_2 : count_up_to_entail_wit_5_2.
Proof.
  pre_process.
  Exists output_l_2.
  entailer!.
  eapply prime_test_state_step_keep; eauto; try lia.
  match goal with
  | Hs : count_up_to_state i output_l_2 |- _ =>
      pose proof (count_up_to_state_Znth_prime i output_l_2 j Hs ltac:(lia)) as [[Hz_ge _] _]
  end.
  replace (j - 0) with j in * by lia.
  rewrite Z.rem_mod_nonneg in H by lia.
  exact H.
Qed. 

Lemma proof_of_count_up_to_entail_wit_6_1 : count_up_to_entail_wit_6_1.
Proof.
  pre_process.
  subst output_size.
  subst output_l_2.
  Right.
  Exists (i :: nil).
  sep_apply (IntArray.seg_single data 0 i).
  rewrite IntArray.seg_empty.
  entailer!.
  assert (i = 2).
  { eapply count_up_to_state_empty_i2; eauto; lia. }
  subst i.
  apply count_up_to_state_after_two.
Qed. 

Lemma proof_of_count_up_to_entail_wit_6_2 : count_up_to_entail_wit_6_2.
Proof.
  pre_process.
  Right.
  Exists (output_l_2 ++ i :: nil).
  sep_apply (IntArray.seg_single data output_size i).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size (output_size + 1)
               output_l_2 (i :: nil)).
  entailer!.
  - apply count_up_to_state_append_prime; auto.
    replace (j - 0) with j in * by lia.
    match goal with
    | Hq : Znth j output_l_2 0 > i ÷ Znth j output_l_2 0,
      Hs : count_up_to_state i output_l_2,
      Ht : prime_test_state i output_l_2 j isp |- _ =>
        pose proof (count_up_to_state_Znth_prime i output_l_2 j Hs ltac:(lia)) as [[Hz_ge _] _];
        rewrite Z.quot_div_nonneg in Hq by lia;
        eapply prime_test_state_exit_prime_early; eauto; lia
    end.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - lia.
Qed. 

Lemma proof_of_count_up_to_entail_wit_6_3 : count_up_to_entail_wit_6_3.
Proof.
  pre_process.
  Right.
  Exists (output_l_2 ++ i :: nil).
  sep_apply (IntArray.seg_single data output_size i).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size (output_size + 1)
               output_l_2 (i :: nil)).
  entailer!.
  - apply count_up_to_state_append_prime; auto.
    match goal with
    | Hs : count_up_to_state i output_l_2,
      Ht : prime_test_state i output_l_2 j isp |- _ =>
        eapply prime_test_state_exit_prime_full; eauto; lia
    end.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - lia.
Qed. 

Lemma proof_of_count_up_to_entail_wit_6_4 : count_up_to_entail_wit_6_4.
Proof.
  pre_process.
  Right.
  Exists output_l_2.
  entailer!.
  apply count_up_to_state_skip_not_prime; auto.
  subst isp.
  eapply prime_test_state_zero_not_prime; eauto.
Qed. 

Lemma proof_of_count_up_to_entail_wit_6_5 : count_up_to_entail_wit_6_5.
Proof.
  pre_process.
  Right.
  Exists output_l_2.
  entailer!.
  apply count_up_to_state_skip_not_prime; auto.
  subst isp.
  eapply prime_test_state_zero_not_prime; eauto.
Qed. 

Lemma proof_of_count_up_to_return_wit_1 : count_up_to_return_wit_1.
Proof.
  pre_process.
  Exists retval_2 (@nil Z) 0.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  apply problem_96_spec_z_empty.
  lia.
Qed. 

Lemma proof_of_count_up_to_return_wit_2 : count_up_to_return_wit_2.
Proof.
  pre_process.
  Exists data_2 output_l_2 output_size_2.
  entailer!.
  replace n_pre with i by lia.
  apply problem_96_spec_z_of_state.
  exact H10.
Qed. 

Lemma proof_of_count_up_to_return_wit_3 : count_up_to_return_wit_3.
Proof.
  pre_process.
  Exists data_2 output_l_2 output_size_2.
  entailer!.
  replace n_pre with i by lia.
  apply problem_96_spec_z_of_state.
  exact H10.
Qed. 
