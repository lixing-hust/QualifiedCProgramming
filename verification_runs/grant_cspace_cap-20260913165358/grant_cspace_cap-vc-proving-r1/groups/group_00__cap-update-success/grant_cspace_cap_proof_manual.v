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
From SimpleC.EE.osverify_qcp.cases Require Import grant_cspace_cap_goal.
From SimpleC.EE.osverify_qcp.cases Require Import grant_cspace_cap_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial : ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst dest_valid_target class_valid_target right_valid_target.
  cancel.
Qed.

Lemma proof_of_ucos_Grant_Cap_return_wit_1_valid_target : ucos_Grant_Cap_return_wit_1_valid_target.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial.
Qed.

Lemma proof_of_grant_cspace_cap_return_wit_1_split_goal_1 : grant_cspace_cap_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_return_wit_1 : grant_cspace_cap_return_wit_1.
Proof. Admitted. 

Lemma proof_of_grant_cspace_cap_return_wit_2_split_goal_1 : grant_cspace_cap_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_return_wit_2 : grant_cspace_cap_return_wit_2.
Proof. Admitted. 

Lemma proof_of_grant_cspace_cap_return_wit_3_split_goal_1 : grant_cspace_cap_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_return_wit_3 : grant_cspace_cap_return_wit_3.
Proof. Admitted. 

Lemma proof_of_grant_cspace_cap_return_wit_4 : grant_cspace_cap_return_wit_4.
Proof. Admitted. 

Lemma proof_of_grant_cspace_cap_return_wit_5 : grant_cspace_cap_return_wit_5.
Proof. Admitted. 

Lemma proof_of_grant_cspace_cap_return_wit_6 : grant_cspace_cap_return_wit_6.
Proof. Admitted. 

Lemma proof_of_grant_cspace_cap_return_wit_7_callee_null : grant_cspace_cap_return_wit_7_callee_null.
Proof. Admitted. 

Lemma proof_of_grant_cspace_cap_return_wit_8_callee_invalid : grant_cspace_cap_return_wit_8_callee_invalid.
Proof. Admitted. 

Lemma proof_of_grant_cspace_cap_return_wit_11_callee_success : grant_cspace_cap_return_wit_11_callee_success.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&( "OSRunning" )) running).
  Intros_p Hrunning_range.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hrunning_range by reflexivity.
  rewrite unsigned_last_nbits_eq in PreH3 by lia.
  subst running.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; lia.
Qed.
