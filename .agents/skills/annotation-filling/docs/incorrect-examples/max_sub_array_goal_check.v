From SimpleC.EE.QCP_demos_LLM Require Import max_sub_array_goal max_sub_array_proof_auto max_sub_array_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include max_sub_array_proof_auto.
  Include max_sub_array_proof_manual.
End VC_Correctness.
