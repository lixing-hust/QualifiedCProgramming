From SimpleC.EE Require Import C_117_goal C_117_proof_auto C_117_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include C_117_proof_auto.
  Include C_117_proof_manual.
End VC_Correctness.
