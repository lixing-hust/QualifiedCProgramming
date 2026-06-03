From SimpleC.EE Require Import C_103_goal C_103_proof_auto C_103_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_103_proof_auto.
  Include C_103_proof_manual.
End VC_Correctness.
