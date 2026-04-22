From SimpleC.EE Require Import C_46_goal C_46_proof_auto C_46_proof_manual.

Module VC_Correctness : VC_Correct.
  Include C_46_proof_auto.
  Include C_46_proof_manual.
End VC_Correctness.
