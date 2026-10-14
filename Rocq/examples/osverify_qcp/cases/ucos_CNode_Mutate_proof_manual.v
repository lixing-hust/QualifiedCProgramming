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
From SimpleC.EE.osverify_qcp.cases Require Import ucos_CNode_Mutate_goal.
From SimpleC.EE.osverify_qcp.cases Require Import ucos_CNode_Mutate_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.osverify_qcp.cases.ucos_CNode_Mutate_lib.
Local Open Scope sac.

Lemma proof_of_ucos_CNode_Mutate_return_wit_1_distinct_cspaces_split_goal_1 : ucos_CNode_Mutate_return_wit_1_distinct_cspaces_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutate_distinct_fields, mutate_distinct_transition,
    mutate_authorized, mutate_source, mutate_destination.
  intros; cbn.
  left; repeat split; auto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_1_distinct_cspaces : ucos_CNode_Mutate_return_wit_1_distinct_cspaces.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_1_distinct_cspaces_split_goal_1.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_2_shared_cspace_split_goal_1 : ucos_CNode_Mutate_return_wit_2_shared_cspace_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutate_alias_fields, mutate_alias_transition, mutate_authorized.
  intros; cbn.
  rewrite Z.land_lnot_diag.
  left; repeat split; auto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_2_shared_cspace : ucos_CNode_Mutate_return_wit_2_shared_cspace.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_2_shared_cspace_split_goal_1.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_3_same_priority_split_goal_1 : ucos_CNode_Mutate_return_wit_3_same_priority_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutate_alias_fields, mutate_alias_transition, mutate_authorized.
  intros; cbn.
  rewrite Z.land_lnot_diag.
  left; repeat split; auto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_3_same_priority : ucos_CNode_Mutate_return_wit_3_same_priority.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_3_same_priority_split_goal_1.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_4_distinct_cspaces_split_goal_1 : ucos_CNode_Mutate_return_wit_4_distinct_cspaces_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutate_distinct_fields, mutate_distinct_transition, mutate_authorized.
  intros src_ptr dst_tag dst_ptr. cbn.
  right. repeat split; try reflexivity; tauto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_4_distinct_cspaces : ucos_CNode_Mutate_return_wit_4_distinct_cspaces.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_4_distinct_cspaces_split_goal_1.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_5_shared_cspace_split_goal_1 : ucos_CNode_Mutate_return_wit_5_shared_cspace_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutate_alias_fields, mutate_alias_transition, mutate_authorized.
  intros ptr. cbn.
  right. repeat split; try reflexivity; tauto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_5_shared_cspace : ucos_CNode_Mutate_return_wit_5_shared_cspace.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_5_shared_cspace_split_goal_1.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_6_same_priority_split_goal_1 : ucos_CNode_Mutate_return_wit_6_same_priority_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutate_alias_fields, mutate_alias_transition, mutate_authorized.
  intros ptr. cbn.
  right. repeat split; try reflexivity; tauto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_6_same_priority : ucos_CNode_Mutate_return_wit_6_same_priority.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_6_same_priority_split_goal_1.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_7_same_priority_split_goal_1 : ucos_CNode_Mutate_return_wit_7_same_priority_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutate_alias_fields, mutate_alias_transition, mutate_authorized.
  intros; cbn.
  right; repeat split; try reflexivity; tauto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_7_same_priority : ucos_CNode_Mutate_return_wit_7_same_priority.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_7_same_priority_split_goal_1.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_8_shared_cspace_split_goal_1 : ucos_CNode_Mutate_return_wit_8_shared_cspace_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutate_alias_fields, mutate_alias_transition, mutate_authorized.
  intros; cbn.
  right; repeat split; try reflexivity; tauto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_8_shared_cspace : ucos_CNode_Mutate_return_wit_8_shared_cspace.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_8_shared_cspace_split_goal_1.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_9_distinct_cspaces_split_goal_1 : ucos_CNode_Mutate_return_wit_9_distinct_cspaces_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutate_distinct_fields, mutate_distinct_transition, mutate_authorized.
  intros; cbn.
  right; repeat split; try reflexivity; tauto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_9_distinct_cspaces : ucos_CNode_Mutate_return_wit_9_distinct_cspaces.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_9_distinct_cspaces_split_goal_1.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_10_distinct_cspaces_split_goal_1 : ucos_CNode_Mutate_return_wit_10_distinct_cspaces_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutate_distinct_fields, mutate_distinct_transition, mutate_authorized.
  intros; cbn.
  right; repeat split; try reflexivity; tauto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_10_distinct_cspaces : ucos_CNode_Mutate_return_wit_10_distinct_cspaces.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_10_distinct_cspaces_split_goal_1.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_11_shared_cspace_split_goal_1 : ucos_CNode_Mutate_return_wit_11_shared_cspace_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutate_alias_fields, mutate_alias_transition, mutate_authorized.
  intros; cbn.
  right; repeat split; try reflexivity; tauto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_11_shared_cspace : ucos_CNode_Mutate_return_wit_11_shared_cspace.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_11_shared_cspace_split_goal_1.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_12_same_priority_split_goal_1 : ucos_CNode_Mutate_return_wit_12_same_priority_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold mutate_alias_fields, mutate_alias_transition, mutate_authorized.
  intros; cbn.
  right; repeat split; try reflexivity; tauto.
Qed.

Lemma proof_of_ucos_CNode_Mutate_return_wit_12_same_priority : ucos_CNode_Mutate_return_wit_12_same_priority.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Mutate_return_wit_12_same_priority_split_goal_1.
Qed.
