From SimpleC.EE Require Import C_44_goal C_44_proof_auto C_44_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_44_proof_auto.
  Include C_44_proof_manual.
End VC_Correctness.
