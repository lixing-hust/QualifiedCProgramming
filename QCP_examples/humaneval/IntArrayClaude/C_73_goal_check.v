Require Import C_73_goal C_73_proof_auto C_73_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include C_73_proof_auto.
  Include C_73_proof_manual.
End VC_Correctness.
