From SimpleC.EE Require Import C_39_goal C_39_auto C_39_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_39_auto.
  Include C_39_manual.
End VC_Correctness.
