From SimpleC.EE Require Import C_144_goal C_144_proof_auto C_144_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_144_proof_auto.
  Include C_144_proof_manual.
End VC_Correctness.
