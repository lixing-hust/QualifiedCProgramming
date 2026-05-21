From SimpleC.EE Require Import C_23_goal C_23_proof_auto C_23_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_23_proof_auto.
  Include C_23_proof_manual.
End VC_Correctness.
