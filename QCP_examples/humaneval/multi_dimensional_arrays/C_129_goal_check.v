From SimpleC.EE Require Import C_129_goal C_129_proof_auto C_129_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_ptr_array2_strategy_proof.
  Include int_array_strategy_proof.
  Include C_129_proof_auto.
  Include C_129_proof_manual.
End VC_Correctness.
