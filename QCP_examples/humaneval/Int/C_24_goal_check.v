From SimpleC.EE Require Import C_24_goal C_24_proof_auto C_24_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_24_proof_auto.
  Include C_24_proof_manual.
End VC_Correctness.
