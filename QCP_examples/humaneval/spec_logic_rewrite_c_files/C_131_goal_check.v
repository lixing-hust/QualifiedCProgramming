From SimpleC.EE Require Import C_131_goal C_131_proof_auto C_131_proof_manual.

Module VC_Correctness : VC_Correct.
  Include C_131_proof_auto.
  Include C_131_proof_manual.
End VC_Correctness.
