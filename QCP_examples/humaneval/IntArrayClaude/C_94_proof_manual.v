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
From SimpleC.EE Require Import C_94_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_94.
Local Open Scope sac.

Lemma proof_of_skjkasdkd_safety_wit_21 : skjkasdkd_safety_wit_21.
Proof.
  pre_process.
  pose proof (digit_sum_state_step original_largest largest sum H8 H) as Hstep.
  unfold digit_sum_state in Hstep.
  destruct Hstep as [_ [fuel [Hcur [Hsum [_ Hbound]]]]].
  pose proof (sum_digits_fuel_z_nonneg (largest / 10) fuel) as Hnonneg.
  assert (sum + largest mod 10 <= sum + largest mod 10 + sum_digits_fuel_z (largest / 10) fuel) as Hstep_le by lia.
  assert (sum + largest mod 10 <= 100) as Hsum_le.
  { eapply Z.le_trans. exact Hstep_le. exact Hbound. }
  assert (largest % 10 = largest mod 10) as Hrem.
  { apply Z.rem_mod_nonneg; lia. }
  rewrite Hrem.
  entailer!.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_1 : skjkasdkd_entail_wit_1.
Proof.
  unfold skjkasdkd_entail_wit_1.
  intros.
  entailer!.
  - unfold digit_sum_int_range; lia.
  - apply largest_prime_prefix_init.
    rewrite <- H1; lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_2 : skjkasdkd_entail_wit_2.
Proof.
  unfold skjkasdkd_entail_wit_2.
  intros.
  entailer!.
  assert (0 <= Znth i lv 0 <= INT_MAX) as Hrange.
  {
    match goal with
    | Hrange_all: list_nonneg_int_range lv |- _ =>
        apply Hrange_all; lia
    end.
  }
  apply prime_scan_state_init; lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_3_1 : skjkasdkd_entail_wit_3_1.
Proof.
  unfold skjkasdkd_entail_wit_3_1.
  intros.
  entailer!.
  - eapply prime_scan_state_step_zero.
    + exact H18.
    + rewrite (Z.quot_div_nonneg x j) in H0 by lia.
      exact H0.
  - rewrite (Z.quot_div_nonneg x j) in H0 by lia.
    assert (x / j <= x) by (apply Z.div_le_upper_bound; nia).
    lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_3_2 : skjkasdkd_entail_wit_3_2.
Proof.
  unfold skjkasdkd_entail_wit_3_2.
  intros.
  entailer!.
  - eapply prime_scan_state_step_keep.
    + exact H18.
    + rewrite (Z.quot_div_nonneg x j) in H0 by lia.
      exact H0.
  - rewrite (Z.quot_div_nonneg x j) in H0 by lia.
    assert (x / j <= x) by (apply Z.div_le_upper_bound; nia).
    lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_4_1 : skjkasdkd_entail_wit_4_1.
Proof.
  unfold skjkasdkd_entail_wit_4_1.
  intros.
  entailer!.
  - assert (0 <= x <= INT_MAX) as Hrange.
    {
      subst x.
      match goal with
      | Hrange_all: list_nonneg_int_range lv |- _ =>
          apply Hrange_all; lia
      end.
    }
    exact Hrange.
  - assert (0 <= x <= INT_MAX) as Hrange.
    {
      subst x.
      match goal with
      | Hrange_all: list_nonneg_int_range lv |- _ =>
          apply Hrange_all; lia
      end.
    }
    eapply largest_prime_prefix_update; eauto; lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_4_2 : skjkasdkd_entail_wit_4_2.
Proof.
  unfold skjkasdkd_entail_wit_4_2.
  intros.
  entailer!.
  - assert (0 <= x <= INT_MAX) as Hrange.
    {
      subst x.
      match goal with
      | Hrange_all: list_nonneg_int_range lv |- _ =>
          apply Hrange_all; lia
      end.
    }
    exact Hrange.
  - assert (0 <= x <= INT_MAX) as Hrange.
    {
      subst x.
      match goal with
      | Hrange_all: list_nonneg_int_range lv |- _ =>
          apply Hrange_all; lia
      end.
    }
    eapply largest_prime_prefix_update; eauto; lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_4_3 : skjkasdkd_entail_wit_4_3.
Proof.
  unfold skjkasdkd_entail_wit_4_3.
  intros.
  entailer!.
  apply largest_prime_prefix_skip; auto; lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_4_4 : skjkasdkd_entail_wit_4_4.
Proof.
  unfold skjkasdkd_entail_wit_4_4.
  intros.
  entailer!.
  apply largest_prime_prefix_skip; auto; lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_4_5 : skjkasdkd_entail_wit_4_5.
Proof.
  unfold skjkasdkd_entail_wit_4_5.
  intros.
  entailer!.
  apply largest_prime_prefix_skip; auto; lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_4_6 : skjkasdkd_entail_wit_4_6.
Proof.
  unfold skjkasdkd_entail_wit_4_6.
  intros.
  entailer!.
  apply largest_prime_prefix_skip; auto; lia.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_5 : skjkasdkd_entail_wit_5.
Proof.
  pre_process.
  Exists largest.
  entailer!.
  - apply digit_sum_state_init; auto.
  - replace lst_size_pre with i by lia.
    exact H7.
Qed.

Lemma proof_of_skjkasdkd_entail_wit_6 : skjkasdkd_entail_wit_6.
Proof.
  pre_process.
  Exists original_largest_2.
  entailer!.
  assert (largest ÷ 10 = largest / 10) as Hquot.
  { apply Z.quot_div_nonneg; lia. }
  assert (largest % 10 = largest mod 10) as Hrem.
  { apply Z.rem_mod_nonneg; lia. }
  rewrite Hquot, Hrem.
  apply digit_sum_state_step; auto.
Qed.

Lemma proof_of_skjkasdkd_return_wit_1 : skjkasdkd_return_wit_1.
Proof.
  pre_process.
  assert (largest = 0).
  {
    unfold digit_sum_state in H8.
    destruct H8 as [_ [fuel [Hcur _]]].
    lia.
  }
  subst largest.
  entailer!.
  eapply problem_94_spec_z_of_digit_state.
  - rewrite H2 in H6. exact H6.
  - exact H7.
  - exact H8.
Qed.
