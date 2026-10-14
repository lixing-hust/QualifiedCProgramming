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
From SimpleC.EE.osverify_qcp.cases Require Import ucos_Grant_Cap_inferred_goal.
From SimpleC.EE.osverify_qcp.cases Require Import ucos_Grant_Cap_inferred_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.osverify_qcp.cases.ucos_Grant_Cap_inferred_lib.
Local Open Scope sac.

Lemma proof_of_ucos_Grant_Cap_return_wit_1_split_goal_1 : ucos_Grant_Cap_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold grant_success_fields, grant_rights; repeat split; reflexivity).
Qed.

Lemma proof_of_ucos_Grant_Cap_return_wit_1 : ucos_Grant_Cap_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_Grant_Cap_return_wit_1_split_goal_1.
Qed.
