From SimpleC.EE Require Import C_53_goal C_53_auto C_53_manual.

Module VC_Correctness : VC_Correct.
  Include C_53_auto.
  Include C_53_manual.
End VC_Correctness.
