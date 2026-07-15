From SimpleC.EE Require Import C_78_goal C_78_proof_auto C_78_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include C_78_proof_auto.
  Include C_78_proof_manual.
End VC_Correctness.
