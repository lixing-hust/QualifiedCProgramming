From SimpleC.EE Require Import C_131_goal C_131_auto C_131_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_131_auto.
  Include C_131_manual.
End VC_Correctness.
