From SimpleC.EE Require Import C_134_goal C_134_proof_auto C_134_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_134_proof_auto.
  Include C_134_proof_manual.
End VC_Correctness.
