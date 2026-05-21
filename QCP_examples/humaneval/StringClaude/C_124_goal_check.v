From SimpleC.EE Require Import C_124_goal C_124_proof_auto C_124_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_124_proof_auto.
  Include C_124_proof_manual.
End VC_Correctness.
