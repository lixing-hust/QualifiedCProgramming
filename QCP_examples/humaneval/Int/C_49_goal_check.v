From SimpleC.EE Require Import C_49_goal C_49_proof_auto C_49_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_49_proof_auto.
  Include C_49_proof_manual.
End VC_Correctness.
