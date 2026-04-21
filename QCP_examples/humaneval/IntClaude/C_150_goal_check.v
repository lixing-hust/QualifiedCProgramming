From SimpleC.EE Require Import C_150_goal C_150_auto C_150_manual.

Module VC_Correctness : VC_Correct.
  Include C_150_auto.
  Include C_150_manual.
End VC_Correctness.
