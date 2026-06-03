From SimpleC.EE Require Import C_10_goal C_10_proof_auto C_10_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_10_proof_auto.
  Include C_10_proof_manual.
End VC_Correctness.
