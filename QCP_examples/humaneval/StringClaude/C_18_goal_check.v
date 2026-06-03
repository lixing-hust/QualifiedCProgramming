From SimpleC.EE Require Import C_18_goal C_18_proof_auto C_18_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_18_proof_auto.
  Include C_18_proof_manual.
End VC_Correctness.
