Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_36_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_36.
Local Open Scope sac.

Lemma proof_of_fizz_buzz_safety_wit_10 : fizz_buzz_safety_wit_10.
Proof.
  unfold fizz_buzz_safety_wit_10.
  intros.
  Intros.
  entailer!.
  assert (Hqmod : q mod 10 = 7).
  {
    rewrite <- (Z.rem_mod_nonneg q 10) by lia.
    exact H.
  }
  assert (Hqdigit : count_digit7 q = 1 + count_digit7 (q / 10)).
  {
    apply count_digit7_step_hit.
    - lia.
    - exact Hqmod.
  }
  assert (Hnonneg : 0 <= count_digit7 (q / 10)).
  { apply count_digit7_nonneg. }
  assert (Hbound : count + 1 <= i_2 * (i_2 + 1)).
  { rewrite Hqdigit in H8. lia. }
  assert (Hi2bound : i_2 * (i_2 + 1) <= 46340 * 46341) by nia.
  nia.
Qed.

Lemma proof_of_fizz_buzz_safety_wit_23 : fizz_buzz_safety_wit_23.
Proof.
  unfold fizz_buzz_safety_wit_23.
  intros.
  Intros.
  entailer!.
  assert (Hqmod : q mod 10 = 7).
  {
    rewrite <- (Z.rem_mod_nonneg q 10) by lia.
    exact H.
  }
  assert (Hqdigit : count_digit7 q = 1 + count_digit7 (q / 10)).
  {
    apply count_digit7_step_hit.
    - lia.
    - exact Hqmod.
  }
  assert (Hnonneg : 0 <= count_digit7 (q / 10)).
  { apply count_digit7_nonneg. }
  assert (Hbound : count + 1 <= i_2 * (i_2 + 1)).
  { rewrite Hqdigit in H9. lia. }
  assert (Hi2bound : i_2 * (i_2 + 1) <= 46340 * 46341) by nia.
  nia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_1 : fizz_buzz_entail_wit_1.
Proof.
  unfold fizz_buzz_entail_wit_1.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_2 : fizz_buzz_entail_wit_2.
Proof.
  unfold fizz_buzz_entail_wit_2.
  intros.
  Intros.
  entailer!.
  assert (Hdigit : count_digit7 i <= i) by (apply count_digit7_le_self; lia).
  lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_3_1 : fizz_buzz_entail_wit_3_1.
Proof.
  unfold fizz_buzz_entail_wit_3_1.
  intros.
  Intros.
  entailer!.
  - assert (Hqmod : q mod 10 = 7).
    { rewrite <- (Z.rem_mod_nonneg q 10) by lia. exact H. }
    assert (Hstep : count_digit7 q = 1 + count_digit7 (q / 10)).
    { apply count_digit7_step_hit; [lia | exact Hqmod]. }
    pose proof H8 as Hbound.
    rewrite Hstep in Hbound.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    replace
      (count_2 + 1 + count_digit7 (q / 10))
      with (count_2 + (1 + count_digit7 (q / 10))) by lia.
    exact Hbound.
  - assert (Hqmod : q mod 10 = 7).
    { rewrite <- (Z.rem_mod_nonneg q 10) by lia. exact H. }
    assert (Hstep : count_digit7 q = 1 + count_digit7 (q / 10)).
    { apply count_digit7_step_hit; [lia | exact Hqmod]. }
    pose proof H7 as Heq.
    rewrite Hstep in Heq.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    replace
      (count_2 + 1 + count_digit7 (q / 10))
      with (count_2 + (1 + count_digit7 (q / 10))) by lia.
    exact Heq.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_3_2 : fizz_buzz_entail_wit_3_2.
Proof.
  unfold fizz_buzz_entail_wit_3_2.
  intros.
  Intros.
  entailer!.
  - assert (Hqmiss : q mod 10 <> 7).
    {
      intro Hcontra.
      apply H.
      rewrite <- (Z.rem_mod_nonneg q 10) in Hcontra by lia.
      exact Hcontra.
    }
    assert (Hstep : count_digit7 q = count_digit7 (q / 10)).
    { apply count_digit7_step_miss; [lia | exact Hqmiss]. }
    pose proof H8 as Hbound.
    rewrite Hstep in Hbound.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    exact Hbound.
  - assert (Hqmiss : q mod 10 <> 7).
    {
      intro Hcontra.
      apply H.
      rewrite <- (Z.rem_mod_nonneg q 10) in Hcontra by lia.
      exact Hcontra.
    }
    assert (Hstep : count_digit7 q = count_digit7 (q / 10)).
    { apply count_digit7_step_miss; [lia | exact Hqmiss]. }
    pose proof H7 as Heq.
    rewrite Hstep in Heq.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    exact Heq.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_4 : fizz_buzz_entail_wit_4.
Proof.
  unfold fizz_buzz_entail_wit_4.
  intros.
  Intros.
  entailer!.
  assert (Hdigit : count_digit7 i <= i) by (apply count_digit7_le_self; lia).
  lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_5_1 : fizz_buzz_entail_wit_5_1.
Proof.
  unfold fizz_buzz_entail_wit_5_1.
  intros.
  Intros.
  entailer!.
  - assert (Hqmod : q mod 10 = 7).
    { rewrite <- (Z.rem_mod_nonneg q 10) by lia. exact H. }
    assert (Hstep : count_digit7 q = 1 + count_digit7 (q / 10)).
    { apply count_digit7_step_hit; [lia | exact Hqmod]. }
    pose proof H9 as Hbound.
    rewrite Hstep in Hbound.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    replace
      (count_2 + 1 + count_digit7 (q / 10))
      with (count_2 + (1 + count_digit7 (q / 10))) by lia.
    exact Hbound.
  - assert (Hqmod : q mod 10 = 7).
    { rewrite <- (Z.rem_mod_nonneg q 10) by lia. exact H. }
    assert (Hstep : count_digit7 q = 1 + count_digit7 (q / 10)).
    { apply count_digit7_step_hit; [lia | exact Hqmod]. }
    pose proof H8 as Heq.
    rewrite Hstep in Heq.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    replace
      (count_2 + 1 + count_digit7 (q / 10))
      with (count_2 + (1 + count_digit7 (q / 10))) by lia.
    exact Heq.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_5_2 : fizz_buzz_entail_wit_5_2.
Proof.
  unfold fizz_buzz_entail_wit_5_2.
  intros.
  Intros.
  entailer!.
  - assert (Hqmiss : q mod 10 <> 7).
    {
      intro Hcontra.
      apply H.
      rewrite <- (Z.rem_mod_nonneg q 10) in Hcontra by lia.
      exact Hcontra.
    }
    assert (Hstep : count_digit7 q = count_digit7 (q / 10)).
    { apply count_digit7_step_miss; [lia | exact Hqmiss]. }
    pose proof H9 as Hbound.
    rewrite Hstep in Hbound.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    exact Hbound.
  - assert (Hqmiss : q mod 10 <> 7).
    {
      intro Hcontra.
      apply H.
      rewrite <- (Z.rem_mod_nonneg q 10) in Hcontra by lia.
      exact Hcontra.
    }
    assert (Hstep : count_digit7 q = count_digit7 (q / 10)).
    { apply count_digit7_step_miss; [lia | exact Hqmiss]. }
    pose proof H8 as Heq.
    rewrite Hstep in Heq.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    exact Heq.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_6_1 : fizz_buzz_entail_wit_6_1.
Proof.
  unfold fizz_buzz_entail_wit_6_1.
  intros.
  Intros.
  entailer!;
    [ apply store_int_undef_store_int
    | (assert (Hq : q = 0) by lia;
       subst q;
       change (count_digit7 0) with 0 in H7;
       replace (count + 0) with count in H7 by lia;
       nia)
    | (assert (Hq : q = 0) by lia;
       subst q;
       change (count_digit7 0) with 0 in H6;
       replace (count + 0) with count in H6 by lia;
       assert (Himod : i mod 11 = 0) by (rewrite <- (Z.rem_mod_nonneg i 11) by lia; exact H4);
       pose proof (fizzbuzz_upto_step_div11 i H1 Himod) as Hstepfb;
       rewrite <- Hstepfb in H6;
       exact H6) ].
Qed.

Lemma proof_of_fizz_buzz_entail_wit_6_2 : fizz_buzz_entail_wit_6_2.
Proof.
  unfold fizz_buzz_entail_wit_6_2.
  intros.
  Intros.
  entailer!;
    [ apply store_int_undef_store_int
    | (assert (Hq : q = 0) by lia;
       subst q;
       change (count_digit7 0) with 0 in H8;
       replace (count + 0) with count in H8 by lia;
       nia)
    | (assert (Hq : q = 0) by lia;
       subst q;
       change (count_digit7 0) with 0 in H7;
       replace (count + 0) with count in H7 by lia;
       assert (Himod : i mod 13 = 0) by (rewrite <- (Z.rem_mod_nonneg i 13) by lia; exact H4);
       pose proof (fizzbuzz_upto_step_div13 i H1 Himod) as Hstepfb;
       rewrite <- Hstepfb in H7;
       exact H7) ].
Qed.

Lemma proof_of_fizz_buzz_entail_wit_6_3 : fizz_buzz_entail_wit_6_3.
Proof.
  unfold fizz_buzz_entail_wit_6_3.
  intros.
  Intros.
  entailer!.
  assert (Hmod11 : i mod 11 <> 0).
  {
    intro Hcontra.
    apply H0.
    rewrite <- (Z.rem_mod_nonneg i 11) in Hcontra by lia.
    exact Hcontra.
  }
  assert (Hmod13 : i mod 13 <> 0).
  {
    intro Hcontra.
    apply H.
    rewrite <- (Z.rem_mod_nonneg i 13) in Hcontra by lia.
    exact Hcontra.
  }
  pose proof (fizzbuzz_upto_step_nondiv i H2 Hmod11 Hmod13) as Hstep.
  rewrite Hstep.
  exact H4.
Qed.

Lemma proof_of_fizz_buzz_return_wit_1 : fizz_buzz_return_wit_1.
Proof.
  unfold fizz_buzz_return_wit_1.
  intros.
  Intros.
  entailer!.
  unfold problem_36_spec_z, problem_36_spec.
  assert (Hi_eq : i = n_pre) by lia.
  subst i.
  subst count.
  unfold fizzbuzz_upto.
  rewrite Nat2Z.id.
  reflexivity.
Qed.
