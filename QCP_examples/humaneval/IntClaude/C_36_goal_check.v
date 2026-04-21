From SimpleC.EE Require Import C_36_goal C_36_auto C_36_manual.

Module VC_Correctness : VC_Correct.
  Include C_36_auto.
  Include C_36_manual.
End VC_Correctness.
