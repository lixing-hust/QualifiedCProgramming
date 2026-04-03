From SimpleC.EE Require Import C_138_goal C_138_auto C_138_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_138_auto.
  Include C_138_manual.
End VC_Correctness.
