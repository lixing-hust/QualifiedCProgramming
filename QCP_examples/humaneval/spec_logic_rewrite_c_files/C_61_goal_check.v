From SimpleC.EE Require Import C_61_goal C_61_proof_auto C_61_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include C_61_proof_auto.
  Include C_61_proof_manual.
End VC_Correctness.
