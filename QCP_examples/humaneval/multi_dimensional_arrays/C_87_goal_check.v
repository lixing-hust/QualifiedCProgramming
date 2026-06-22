From SimpleC.EE Require Import C_87_goal C_87_proof_auto C_87_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_ptr_array2_strategy_proof.
  Include int_array_strategy_proof.
  Include C_87_proof_auto.
  Include C_87_proof_manual.
End VC_Correctness.
