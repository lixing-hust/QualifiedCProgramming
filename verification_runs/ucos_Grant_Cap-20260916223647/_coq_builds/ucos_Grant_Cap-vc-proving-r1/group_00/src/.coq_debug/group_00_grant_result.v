From SimpleC.EE.osverify_qcp.cases Require Import ucos_Grant_Cap_goal.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import naive_C_Rules.
Goal ucos_Grant_Cap_return_wit_1_valid_target.
Proof.
  aggressive_pre_process.
  Show.
Abort.
