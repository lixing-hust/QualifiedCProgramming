From SimpleC.EE Require Import C_114_goal C_114_proof_auto C_114_proof_manual.

Module VC_Correctness : VC_Correct.
  Include long_array_strategy_proof.
  Include C_114_proof_auto.
  Include C_114_proof_manual.
End VC_Correctness.
