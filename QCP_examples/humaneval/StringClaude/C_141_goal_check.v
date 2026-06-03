From SimpleC.EE Require Import C_141_goal C_141_proof_auto C_141_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_141_proof_auto.
  Include C_141_proof_manual.
End VC_Correctness.
