From SimpleC.EE Require Import C_31_goal C_31_auto C_31_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_31_auto.
  Include C_31_manual.
End VC_Correctness.
