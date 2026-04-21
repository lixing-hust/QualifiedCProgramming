From SimpleC.EE Require Import C_83_goal C_83_auto C_83_manual.

Module VC_Correctness : VC_Correct.
  Include C_83_auto.
  Include C_83_manual.
End VC_Correctness.
