From SimpleC.EE Require Import C_102_goal C_102_auto C_102_manual.

Module VC_Correctness : VC_Correct.
  Include C_102_auto.
  Include C_102_manual.
End VC_Correctness.
