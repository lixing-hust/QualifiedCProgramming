From SimpleC.EE Require Import C_63_goal C_63_proof_auto C_63_proof_manual.

Module VC_Correctness : VC_Correct.
  Include C_63_proof_auto.
  Include C_63_proof_manual.
End VC_Correctness.
