From SimpleC.EE Require Import C_132_goal C_132_proof_auto C_132_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_132_proof_auto.
  Include C_132_proof_manual.
End VC_Correctness.
