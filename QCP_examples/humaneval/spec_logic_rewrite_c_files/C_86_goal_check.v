From SimpleC.EE Require Import C_86_goal C_86_proof_auto C_86_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include C_86_proof_auto.
  Include C_86_proof_manual.
End VC_Correctness.
