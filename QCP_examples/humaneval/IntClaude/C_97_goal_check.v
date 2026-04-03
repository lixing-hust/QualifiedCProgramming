From SimpleC.EE Require Import C_97_goal C_97_auto C_97_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_97_auto.
  Include C_97_manual.
End VC_Correctness.
