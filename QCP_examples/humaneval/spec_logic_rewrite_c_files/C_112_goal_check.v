From SimpleC.EE Require Import C_112_goal C_112_proof_auto C_112_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include C_112_proof_auto.
  Include C_112_proof_manual.
End VC_Correctness.
