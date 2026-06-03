From SimpleC.EE Require Import C_65_goal C_65_proof_auto C_65_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_65_proof_auto.
  Include C_65_proof_manual.
End VC_Correctness.
