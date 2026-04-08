From SimpleC.EE.humaneval Require Import C_139_goal C_139_auto C_139_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_139_auto.
  Include C_139_manual.
End VC_Correctness.
