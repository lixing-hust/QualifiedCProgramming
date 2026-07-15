From SimpleC.EE Require Import C_67_goal C_67_proof_auto C_67_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include C_67_proof_auto.
  Include C_67_proof_manual.
End VC_Correctness.
