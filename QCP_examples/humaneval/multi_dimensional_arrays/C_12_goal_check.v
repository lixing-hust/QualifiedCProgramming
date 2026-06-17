From SimpleC.EE Require Import C_12_goal C_12_proof_auto C_12_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include C_12_proof_auto.
  Include C_12_proof_manual.
End VC_Correctness.
