From SimpleC.EE Require Import C_154_goal C_154_proof_auto C_154_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_154_proof_auto.
  Include C_154_proof_manual.
End VC_Correctness.
