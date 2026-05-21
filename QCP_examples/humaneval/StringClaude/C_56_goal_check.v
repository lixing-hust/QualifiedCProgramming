From SimpleC.EE Require Import C_56_goal C_56_proof_auto C_56_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_56_proof_auto.
  Include C_56_proof_manual.
End VC_Correctness.
