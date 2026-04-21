From SimpleC.EE Require Import C_77_goal C_77_auto C_77_manual.

Module VC_Correctness : VC_Correct.
  Include C_77_auto.
  Include C_77_manual.
End VC_Correctness.
