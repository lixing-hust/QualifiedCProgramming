Require Import C_59_goal C_59_auto C_59_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_59_auto.
  Include C_59_manual.
End VC_Correctness.
