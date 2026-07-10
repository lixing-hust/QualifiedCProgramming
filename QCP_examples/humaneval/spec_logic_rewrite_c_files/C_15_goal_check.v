From SimpleC.EE Require Import C_15_goal C_15_proof_auto C_15_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_15_proof_auto.
  Include C_15_proof_manual.
End VC_Correctness.
