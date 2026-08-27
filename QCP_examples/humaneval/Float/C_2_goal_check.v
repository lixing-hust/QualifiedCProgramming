From SimpleC.EE Require Import C_2_goal C_2_proof_auto C_2_proof_manual.

Module VC_Correctness : VC_Correct.
  Include C_2_proof_auto.
  Include C_2_proof_manual.
End VC_Correctness.
