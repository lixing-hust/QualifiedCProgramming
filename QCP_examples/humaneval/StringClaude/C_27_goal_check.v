From SimpleC.EE Require Import C_27_goal C_27_proof_auto C_27_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_27_proof_auto.
  Include C_27_proof_manual.
End VC_Correctness.
