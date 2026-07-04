From SimpleC.EE Require Import C_147_goal C_147_proof_auto C_147_proof_manual.

Module VC_Correctness : VC_Correct.
  Include C_147_proof_auto.
  Include C_147_proof_manual.
End VC_Correctness.
