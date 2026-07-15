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
From SimpleC.EE Require Import C_131_goal.
From SimpleC.EE Require Import C_131_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_131.
Local Open Scope sac.

Lemma proof_of_digits_safety_wit_19_split_goal_1 : digits_safety_wit_19_split_goal_1.
Proof.
  pre_process; entailer!.
  eapply digits_state_odd_product_bound_131; eauto.
Qed.

Lemma proof_of_digits_safety_wit_19_split_goal_2 : digits_safety_wit_19_split_goal_2.
Proof.
  pre_process; entailer!.
  pose proof (Z.rem_bound_pos n 10 ltac:(lia)).
  nia.
Qed.

Lemma proof_of_digits_safety_wit_19 : digits_safety_wit_19.
Proof.
  right. intros. entailer!.
  - pose proof (Z.rem_bound_pos n 10 ltac:(lia)).
    nia.
  - eapply digits_state_odd_product_bound_131; eauto.
Qed.

Lemma proof_of_digits_safety_wit_20_split_goal_1 : digits_safety_wit_20_split_goal_1.
Proof.
  pre_process; entailer!.
  eapply digits_state_odd_product_bound_131; eauto.
Qed.

Lemma proof_of_digits_safety_wit_20_split_goal_2 : digits_safety_wit_20_split_goal_2.
Proof.
  pre_process; entailer!.
  pose proof (Z.rem_bound_pos n 10 ltac:(lia)).
  nia.
Qed.

Lemma proof_of_digits_safety_wit_20 : digits_safety_wit_20.
Proof.
  right. intros. entailer!.
  - pose proof (Z.rem_bound_pos n 10 ltac:(lia)).
    nia.
  - eapply digits_state_odd_product_bound_131; eauto.
Qed.

Lemma proof_of_digits_entail_wit_1 : digits_entail_wit_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  entailer!.
  apply digits_state_init_131; lia || assumption.
Qed.

Lemma proof_of_digits_entail_wit_2_1 : digits_entail_wit_2_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  - eapply digits_state_step_odd_131 with (has := has); eauto.
  - eapply digits_state_odd_product_bound_131; eauto.
  - pose proof (Z.rem_bound_pos n 10 ltac:(lia)); nia.
  - pose proof (zquot10_le_self_131 n ltac:(lia)); lia.
  - apply zquot10_nonneg_131; lia.
Qed.

Lemma proof_of_digits_entail_wit_2_2 : digits_entail_wit_2_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  - eapply digits_state_step_odd_131 with (has := has); eauto.
  - eapply digits_state_odd_product_bound_131; eauto.
  - pose proof (Z.rem_bound_pos n 10 ltac:(lia)); nia.
  - pose proof (zquot10_le_self_131 n ltac:(lia)); lia.
  - apply zquot10_nonneg_131; lia.
Qed.

Lemma proof_of_digits_entail_wit_2_3 : digits_entail_wit_2_3.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  entailer!.
  - eapply digits_state_step_even_131 with (has := has); eauto.
  - pose proof (zquot10_le_self_131 n ltac:(lia)); lia.
  - apply zquot10_nonneg_131; lia.
Qed.

Lemma proof_of_digits_entail_wit_2_4 : digits_entail_wit_2_4.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  - eapply digits_state_step_even_131 with (has := has); eauto.
  - pose proof (zquot10_le_self_131 n ltac:(lia)); lia.
  - apply zquot10_nonneg_131; lia.
Qed.

Lemma proof_of_digits_return_wit_1_split_goal_1 : digits_return_wit_1_split_goal_1.
Proof.
  pre_process; entailer!.
  assert (n = 0) by lia. subst n has.
  apply digits_state_done_some_131; assumption.
Qed.

Lemma proof_of_digits_return_wit_1 : digits_return_wit_1.
Proof.
  right. intros. entailer!.
  assert (n = 0) by lia. subst n has.
  apply digits_state_done_some_131; assumption.
Qed.

Lemma proof_of_digits_return_wit_2_split_goal_1 : digits_return_wit_2_split_goal_1.
Proof.
  pre_process; entailer!.
  assert (n = 0) by lia. subst n has.
  apply digits_state_done_none_131 with (prod := prod); assumption.
Qed.

Lemma proof_of_digits_return_wit_2 : digits_return_wit_2.
Proof.
  right. intros. entailer!.
  assert (n = 0) by lia. subst n has.
  apply digits_state_done_none_131 with (prod := prod); assumption.
Qed.
