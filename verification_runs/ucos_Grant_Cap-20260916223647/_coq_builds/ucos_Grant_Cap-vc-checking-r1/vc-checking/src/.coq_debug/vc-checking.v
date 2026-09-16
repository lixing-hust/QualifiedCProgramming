Require Import SimpleC.EE.osverify_qcp.cases.ucos_Grant_Cap_goal.
Require Import Coq.ZArith.ZArith Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.
Goal SimpleC.EE.osverify_qcp.cases.ucos_Grant_Cap_goal.ucos_Grant_Cap_return_wit_1_valid_target_split_goal_1.
Show.
unfold ucos_Grant_Cap_return_wit_1_valid_target_split_goal_1.
intros.
unfold cap_model.grant_cap_transition.
unfold cap_model.grant_slot_result.
Show.
Abort.

Goal SimpleC.EE.osverify_qcp.cases.ucos_Grant_Cap_goal.ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial.
Show.
Abort.
