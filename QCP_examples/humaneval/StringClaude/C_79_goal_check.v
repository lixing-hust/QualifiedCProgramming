From SimpleC.EE Require Import C_79_goal C_79_proof_auto C_79_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_79_proof_auto.
  Include C_79_proof_manual.
End VC_Correctness.
