From SimpleC.EE.LLM_friendly_cases Require Import sortArray2_goal sortArray2_proof_auto sortArray2_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include sortArray2_proof_auto.
  Include sortArray2_proof_manual.
End VC_Correctness.
