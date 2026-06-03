From SimpleC.EE Require Import C_161_goal C_161_proof_auto C_161_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_161_proof_auto.
  Include C_161_proof_manual.
End VC_Correctness.
