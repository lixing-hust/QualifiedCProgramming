From SimpleC.EE Require Import C_54_goal C_54_proof_auto C_54_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_54_proof_auto.
  Include C_54_proof_manual.
End VC_Correctness.
