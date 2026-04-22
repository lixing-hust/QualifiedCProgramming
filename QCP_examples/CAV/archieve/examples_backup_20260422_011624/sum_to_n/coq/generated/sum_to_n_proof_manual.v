Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260418_153041_sum_to_n Require Import sum_to_n_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma tri_step : forall i : Z,
  1 <= i ->
  ((((i - 1) * i) ÷ 2) + i = ((i * (i + 1)) ÷ 2))%Z.
Proof.
  intros i Hi.
  destruct (Z.Even_or_Odd i) as [[k Hk] | [k Hk]].
  - subst i.
    assert (0 <= k) by nia.
    rewrite !Z.quot_div_nonneg by nia.
    replace (((2 * k - 1) * (2 * k)) / 2) with (((2 * k - 1) * k)) by
      (replace ((2 * k - 1) * (2 * k)) with ((((2 * k - 1) * k) * 2)) by ring;
       symmetry; apply Z.div_mul; lia).
    replace (((2 * k) * (2 * k + 1) / 2)) with (k * (2 * k + 1)) by
      (replace ((2 * k) * (2 * k + 1)) with (((k * (2 * k + 1)) * 2)) by ring;
       symmetry; apply Z.div_mul; lia).
    nia.
  - subst i.
    assert (0 <= k) by nia.
    rewrite !Z.quot_div_nonneg by nia.
    replace ((((2 * k + 1) - 1) * (2 * k + 1) / 2)) with (((2 * k + 1) * k)) by
      (replace (((2 * k + 1) - 1) * (2 * k + 1)) with ((((2 * k + 1) * k) * 2)) by ring;
       symmetry; apply Z.div_mul; lia).
    replace (((2 * k + 1) * ((2 * k + 1) + 1) / 2)) with (((2 * k + 1) * (k + 1))) by
      (replace ((2 * k + 1) * ((2 * k + 1) + 1)) with ((((2 * k + 1) * (k + 1)) * 2)) by ring;
       symmetry; apply Z.div_mul; lia).
    nia.
Qed.

Lemma tri_nonneg : forall z : Z, 0 <= z -> 0 <= ((z * (z + 1)) ÷ 2).
Proof.
  intros z Hz.
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_pos; lia.
Qed.

Lemma tri_monotone : forall i n : Z,
  0 <= i <= n ->
  ((i * (i + 1)) ÷ 2) <= ((n * (n + 1)) ÷ 2).
Proof.
  intros i n Hi.
  rewrite !Z.quot_div_nonneg by nia.
  apply Z.div_le_mono.
  - lia.
  - nia.
Qed.

Lemma tri_nonneg_inst : forall i : Z, 1 <= i -> 0 <= ((i * (i + 1)) ÷ 2).
Proof.
  intros i Hi.
  apply tri_nonneg.
  nia.
Qed.

Lemma proof_of_sum_to_n_safety_wit_3 : sum_to_n_safety_wit_3.
Proof.
  pre_process.
  entailer!.
  - assert (Hsum : ret + i = ((i * (i + 1)) ÷ 2)) by (subst ret; apply tri_step; lia).
    rewrite Hsum.
    pose proof (tri_nonneg_inst i H0) as Hnn.
    lia.
  - assert (Hsum : ret + i = ((i * (i + 1)) ÷ 2)) by (subst ret; apply tri_step; lia).
    rewrite Hsum.
    assert (Hmono : ((i * (i + 1)) ÷ 2) <= ((n_pre * (n_pre + 1)) ÷ 2)).
    { apply tri_monotone. lia. }
    lia.
Qed.

Lemma proof_of_sum_to_n_safety_wit_4 : sum_to_n_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  assert (Hn_bound : n_pre <= 65535).
  {
    destruct (Z_le_gt_dec n_pre 65535) as [Hle | Hgt].
    - exact Hle.
    - assert (Hmono : ((65536 * (65536 + 1)) ÷ 2) <= ((n_pre * (n_pre + 1)) ÷ 2)).
      { apply tri_monotone. lia. }
      pose proof (Z.le_trans _ _ _ Hmono H5) as Hcontra.
      vm_compute in Hcontra.
      exfalso.
      apply Hcontra.
      reflexivity.
  }
  lia.
Qed.

Lemma proof_of_sum_to_n_entail_wit_1 : sum_to_n_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_sum_to_n_entail_wit_2 : sum_to_n_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  assert (Hsum : ret + i = ((i * (i + 1)) ÷ 2)) by (subst ret; apply tri_step; lia).
  rewrite Hsum.
  replace (i + 1 - 1) with i by lia.
  lia.
Qed.

Lemma proof_of_sum_to_n_entail_wit_3 : sum_to_n_entail_wit_3.
Proof.
  pre_process.
  entailer!.
  assert (Hi : i = n_pre + 1) by lia.
  subst i.
  rewrite H2.
  replace (n_pre + 1 - 1) with n_pre by lia.
  reflexivity.
Qed.
