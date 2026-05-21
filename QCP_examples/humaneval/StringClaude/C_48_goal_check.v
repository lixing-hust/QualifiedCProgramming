From SimpleC.EE Require Import C_48_goal C_48_proof_auto C_48_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_48_proof_auto.
  Include C_48_proof_manual.
End VC_Correctness.
