From SimpleC.EE Require Import C_13_goal C_13_proof_auto C_13_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_13_proof_auto.
  Include C_13_proof_manual.
End VC_Correctness.
