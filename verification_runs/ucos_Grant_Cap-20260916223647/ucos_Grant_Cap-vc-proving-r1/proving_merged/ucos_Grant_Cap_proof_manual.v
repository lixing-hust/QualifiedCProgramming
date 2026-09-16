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
From SimpleC.EE.osverify_qcp.cases Require Import ucos_Grant_Cap_goal.
From SimpleC.EE.osverify_qcp.cases Require Import ucos_Grant_Cap_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.osverify_qcp.cap_model.
Local Open Scope sac.

Lemma proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_1 : ucos_Grant_Cap_return_wit_1_valid_target_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold grant_cap_transition, grant_slot_result.
  intros slot ptr.
  reflexivity.
Qed.

Lemma proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial : ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst destTask_Prio_pre cap_Class_pre cap_Right_pre.
  cancel.
Qed.

Lemma proof_of_ucos_Grant_Cap_return_wit_1_valid_target : ucos_Grant_Cap_return_wit_1_valid_target.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial
      cap_Right_pre cap_Class_pre destTask_Prio_pre old_right_valid_target
      right_valid_target class_valid_target dest_valid_target target_valid_target
      PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22).
  - Goal_apply (proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_1
      cap_Right_pre cap_Class_pre destTask_Prio_pre old_right_valid_target
      old_content_valid_target old_type_valid_target right_valid_target
      class_valid_target dest_valid_target target_valid_target
      PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22).
Qed.
