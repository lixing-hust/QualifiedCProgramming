From SimpleC.EE Require Import C_92_goal C_92_proof_auto C_92_proof_manual.

Module VC_Correctness : VC_Correct.
  Include C_92_proof_auto.
  Include C_92_proof_manual.
End VC_Correctness.
