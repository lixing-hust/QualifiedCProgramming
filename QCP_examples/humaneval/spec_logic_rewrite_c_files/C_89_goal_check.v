From SimpleC.EE Require Import C_89_goal C_89_proof_auto C_89_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include C_89_proof_auto.
  Include C_89_proof_manual.
End VC_Correctness.
