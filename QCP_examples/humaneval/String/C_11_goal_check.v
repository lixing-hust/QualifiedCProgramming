From SimpleC.EE Require Import C_11_goal C_11_proof_auto C_11_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include C_11_proof_auto.
  Include C_11_proof_manual.
End VC_Correctness.
