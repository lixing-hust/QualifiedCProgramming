Require Import C_84_goal C_84_proof_auto C_84_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_84_proof_auto.
  Include C_84_proof_manual.
End VC_Correctness.
