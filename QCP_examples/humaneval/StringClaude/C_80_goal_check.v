From SimpleC.EE Require Import C_80_goal C_80_proof_auto C_80_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_80_proof_auto.
  Include C_80_proof_manual.
End VC_Correctness.
