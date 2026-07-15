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
From SimpleC.EE Require Import C_139_goal.
From SimpleC.EE Require Import C_139_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_139.
Local Open Scope sac.

Lemma proof_of_special_factorial_safety_wit_4 : special_factorial_safety_wit_4.
Proof.
  right. intros. entailer!;
  assert (Hfact_i : fact * i = factorial_z i).
  { rewrite PreH12.
    rewrite <- factorial_z_step_139 by lia.
    reflexivity. }
  destruct (factorial_z_bound_139 n0 i PreH5 ltac:(lia)) as [Hlo Hhi].
  rewrite Hfact_i.
  unfold LLONG_MAX_139 in *.
  lia.
Qed.

Lemma proof_of_special_factorial_safety_wit_5 : special_factorial_safety_wit_5.
Proof.
  right. intros. entailer!;
  assert (Hfact_i : fact * i = factorial_z i).
  { rewrite PreH12.
    rewrite <- factorial_z_step_139 by lia.
    reflexivity. }
  assert (Hbfact_i : bfact * (fact * i) = bfact_z i).
  { rewrite PreH13.
    rewrite Hfact_i.
    rewrite <- bfact_z_step_139 by lia.
    reflexivity. }
  destruct (bfact_z_bound_139 n0 i PreH5 ltac:(lia)) as [Hlo Hhi].
  rewrite Hbfact_i.
  unfold LLONG_MAX_139 in *.
  lia.
Qed.

Lemma proof_of_special_factorial_entail_wit_1 : special_factorial_entail_wit_1.
Proof.
  right. intros. entailer!.
Qed.

Lemma proof_of_special_factorial_entail_wit_2 : special_factorial_entail_wit_2.
Proof.
  right. intros. entailer!.
  - assert (Hfact_i : fact * i = factorial_z i).
    { rewrite PreH12.
      rewrite <- factorial_z_step_139 by lia.
      reflexivity. }
    destruct (factorial_z_bound_139 n0 i PreH5 ltac:(lia)) as [_ Hhi].
    rewrite Hfact_i.
    unfold LLONG_MAX_139 in *.
    lia.
  - assert (Hfact_i : fact * i = factorial_z i).
    { rewrite PreH12.
      rewrite <- factorial_z_step_139 by lia.
      reflexivity. }
    assert (Hbfact_i : bfact * (fact * i) = bfact_z i).
    { rewrite PreH13.
      rewrite Hfact_i.
      rewrite <- bfact_z_step_139 by lia.
      reflexivity. }
    destruct (bfact_z_bound_139 n0 i PreH5 ltac:(lia)) as [_ Hhi].
    rewrite Hbfact_i.
    unfold LLONG_MAX_139 in *.
    lia.
  - rewrite PreH12.
    rewrite <- factorial_z_step_139 by lia.
    replace (i + 1 - 1) with i by lia.
    reflexivity.
  - rewrite PreH13, PreH12.
    rewrite <- factorial_z_step_139 by lia.
    rewrite <- bfact_z_step_139 by lia.
    replace (i + 1 - 1) with i by lia.
    reflexivity.
Qed.

Lemma proof_of_special_factorial_return_wit_1 : special_factorial_return_wit_1.
Proof.
  right. intros. entailer!.
  assert (Hi_eq : i - 1 = n0) by lia.
  rewrite PreH13.
  rewrite Hi_eq.
  apply problem_139_spec_z_bfact.
  exact PreH5.
Qed.
