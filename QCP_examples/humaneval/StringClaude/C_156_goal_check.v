From SimpleC.EE Require Import C_156_goal C_156_proof_auto C_156_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_156_proof_auto.
  Include C_156_proof_manual.
End VC_Correctness.
