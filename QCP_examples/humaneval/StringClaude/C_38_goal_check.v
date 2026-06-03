From SimpleC.EE Require Import C_38_goal C_38_proof_auto C_38_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_38_proof_auto.
  Include C_38_proof_manual.
End VC_Correctness.
