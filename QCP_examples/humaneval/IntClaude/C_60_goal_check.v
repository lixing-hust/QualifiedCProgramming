From SimpleC.EE Require Import C_60_goal C_60_auto C_60_manual.

Module VC_Correctness : VC_Correct.
  Include C_60_auto.
  Include C_60_manual.
End VC_Correctness.
