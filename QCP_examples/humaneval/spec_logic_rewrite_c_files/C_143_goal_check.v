From SimpleC.EE Require Import C_143_goal C_143_proof_auto C_143_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include C_143_proof_auto.
  Include C_143_proof_manual.
End VC_Correctness.
