From SimpleC.EE Require Import C_45_goal C_45_proof_auto C_45_proof_manual.

Module VC_Correctness : VC_Correct.
  Include C_45_proof_auto.
  Include C_45_proof_manual.
End VC_Correctness.
