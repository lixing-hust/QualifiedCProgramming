From SimpleC.EE Require Import C_82_goal C_82_proof_auto C_82_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_82_proof_auto.
  Include C_82_proof_manual.
End VC_Correctness.
