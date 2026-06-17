From SimpleC.EE Require Import C_95_goal C_95_proof_auto C_95_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include C_95_proof_auto.
  Include C_95_proof_manual.
End VC_Correctness.
