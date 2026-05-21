From SimpleC.EE Require Import C_93_goal C_93_proof_auto C_93_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_93_proof_auto.
  Include C_93_proof_manual.
End VC_Correctness.
