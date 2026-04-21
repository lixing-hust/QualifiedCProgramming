From SimpleC.EE Require Import C_41_goal C_41_auto C_41_manual.

Module VC_Correctness : VC_Correct.
  Include C_41_auto.
  Include C_41_manual.
End VC_Correctness.
