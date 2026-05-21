From SimpleC.EE Require Import C_91_goal C_91_proof_auto C_91_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_91_proof_auto.
  Include C_91_proof_manual.
End VC_Correctness.
