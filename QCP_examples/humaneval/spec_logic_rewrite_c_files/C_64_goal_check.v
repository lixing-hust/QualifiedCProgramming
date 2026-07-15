From SimpleC.EE Require Import C_64_goal C_64_proof_auto C_64_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include C_64_proof_auto.
  Include C_64_proof_manual.
End VC_Correctness.
