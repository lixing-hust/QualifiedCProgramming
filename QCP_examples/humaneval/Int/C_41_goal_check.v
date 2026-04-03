From SimpleC.EE Require Import C_41_goal C_41_proof_auto C_41_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_41_proof_auto.
  Include C_41_proof_manual.
End VC_Correctness.
