From SimpleC.EE Require Import C_51_goal C_51_proof_auto C_51_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_51_proof_auto.
  Include C_51_proof_manual.
End VC_Correctness.
