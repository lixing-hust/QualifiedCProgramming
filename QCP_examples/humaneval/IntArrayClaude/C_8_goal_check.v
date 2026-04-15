From SimpleC.EE Require Import C_8_goal C_8_proof_auto C_8_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include C_8_proof_auto.
  Include C_8_proof_manual.
End VC_Correctness.
