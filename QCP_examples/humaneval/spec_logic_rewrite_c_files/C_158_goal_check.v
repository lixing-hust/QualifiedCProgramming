Require Import C_158_goal C_158_proof_auto C_158_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include string_strategy_proof.
  Include C_158_proof_auto.
  Include C_158_proof_manual.
End VC_Correctness.
