From SimpleC.EE Require Import C_39_goal C_39_proof_auto C_39_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_39_proof_auto.
  Include C_39_proof_manual.
End VC_Correctness.
