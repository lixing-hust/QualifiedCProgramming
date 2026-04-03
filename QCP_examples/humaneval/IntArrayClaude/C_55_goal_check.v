Require Import C_55_goal C_55_proof_auto C_55_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include C_55_proof_auto.
  Include C_55_proof_manual.
End VC_Correctness.
