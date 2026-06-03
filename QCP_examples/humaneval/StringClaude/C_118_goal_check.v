From SimpleC.EE Require Import C_118_goal C_118_proof_auto C_118_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_118_proof_auto.
  Include C_118_proof_manual.
End VC_Correctness.
