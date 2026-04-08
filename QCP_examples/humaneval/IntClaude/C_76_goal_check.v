From SimpleC.EE.humaneval Require Import C_76_goal C_76_auto C_76_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_76_auto.
  Include C_76_manual.
End VC_Correctness.
