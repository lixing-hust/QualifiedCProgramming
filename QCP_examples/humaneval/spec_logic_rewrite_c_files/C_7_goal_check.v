From SimpleC.EE Require Import C_7_goal C_7_proof_auto C_7_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include C_7_proof_auto.
  Include C_7_proof_manual.
End VC_Correctness.
