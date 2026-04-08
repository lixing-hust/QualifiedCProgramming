From SimpleC.EE.humaneval Require Import C_75_goal C_75_auto C_75_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_75_auto.
  Include C_75_manual.
End VC_Correctness.
