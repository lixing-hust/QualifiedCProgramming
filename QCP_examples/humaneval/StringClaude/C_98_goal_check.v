From SimpleC.EE Require Import C_98_goal C_98_proof_auto C_98_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_98_proof_auto.
  Include C_98_proof_manual.
End VC_Correctness.
