From SimpleC.EE Require Import C_16_goal C_16_proof_auto C_16_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_16_proof_auto.
  Include C_16_proof_manual.
End VC_Correctness.
