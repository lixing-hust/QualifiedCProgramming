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
From SimpleC.EE.osverify_qcp.cases Require Import ucos_cnode_delete_inferred_20261011_goal.
From SimpleC.EE.osverify_qcp.cases Require Import ucos_cnode_delete_inferred_20261011_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.osverify_qcp.cases.ucos_cnode_delete_inferred_20261011_lib.
Local Open Scope sac.

Lemma proof_of_ucos_CNode_Delete_return_wit_1_split_goal_1 : ucos_CNode_Delete_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cd_result.
  right. split; [assumption|]. split; [assumption|].
  right. split; [assumption|].
  left. split; [auto|reflexivity].
Qed.

Lemma proof_of_ucos_CNode_Delete_return_wit_1_split_goal_2 : ucos_CNode_Delete_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_ucos_CNode_Delete_return_wit_1 : ucos_CNode_Delete_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Delete_return_wit_1_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Delete_return_wit_1_split_goal_2.
Qed. 

Lemma proof_of_ucos_CNode_Delete_return_wit_2_split_goal_1 : ucos_CNode_Delete_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cd_result.
  right. split; [assumption|]. split; [assumption|].
  right. split; [assumption|].
  left. split; [auto|reflexivity].
Qed.

Lemma proof_of_ucos_CNode_Delete_return_wit_2_split_goal_2 : ucos_CNode_Delete_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_ucos_CNode_Delete_return_wit_2 : ucos_CNode_Delete_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Delete_return_wit_2_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Delete_return_wit_2_split_goal_2.
Qed. 

Lemma proof_of_ucos_CNode_Delete_return_wit_3_split_goal_1 : ucos_CNode_Delete_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cd_result.
  right. split; [assumption|]. split; [assumption|].
  right. split; [assumption|].
  right. repeat split; assumption || reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Delete_return_wit_3_split_goal_2 : ucos_CNode_Delete_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cd_cap_type_after.
  assert (Hone : (Z.eqb old_type 1) = false) by (apply Z.eqb_neq; assumption).
  assert (Htwo : (Z.eqb old_type 2) = false) by (apply Z.eqb_neq; assumption).
  rewrite Hone, Htwo. reflexivity.
Qed.

Lemma proof_of_ucos_CNode_Delete_return_wit_3 : ucos_CNode_Delete_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_ucos_CNode_Delete_return_wit_3_split_goal_1.
  - Goal_apply proof_of_ucos_CNode_Delete_return_wit_3_split_goal_2.
Qed. 

Lemma proof_of_ucos_CNode_Delete_return_wit_4_split_goal_1 : ucos_CNode_Delete_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cd_result.
  right; repeat split; try lia; left; auto.
Qed.

Lemma proof_of_ucos_CNode_Delete_return_wit_4 : ucos_CNode_Delete_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Delete_return_wit_4_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Delete_return_wit_5_split_goal_1 : ucos_CNode_Delete_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cd_result.
  left; split; [right; lia | reflexivity].
Qed.

Lemma proof_of_ucos_CNode_Delete_return_wit_5 : ucos_CNode_Delete_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_CNode_Delete_return_wit_5_split_goal_1.
Qed. 

Lemma proof_of_ucos_CNode_Delete_return_wit_6 : ucos_CNode_Delete_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia).
  Left.
  split_pure_spatial.
  - cancel emp.
  - split_pures; dump_pre_spatial.
    + unfold cd_result. left; split; [left; lia | reflexivity].
    + lia.
Qed. 

Lemma proof_of_ucos_CNode_Delete_return_wit_7 : ucos_CNode_Delete_return_wit_7.
Proof.
  LLM_pre_process ltac:(lia).
  Left.
  split_pure_spatial.
  - cancel emp.
  - split_pures; dump_pre_spatial.
    + unfold cd_result. left; split; [left; lia | reflexivity].
    + lia.
Qed. 

