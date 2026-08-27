From SimpleC.EE Require Import C_157_goal C_157_proof_auto C_157_proof_manual.

Module VC_Correctness : VC_Correct.
  Include C_157_proof_auto.
  Include C_157_proof_manual.
End VC_Correctness.
