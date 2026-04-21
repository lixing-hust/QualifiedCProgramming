From SimpleC.EE.LLM_friendly_cases Require Import array_cases_goal array_cases_proof_auto array_cases_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include sll_strategy_proof.
  Include array_cases_proof_auto.
  Include array_cases_proof_manual.
End VC_Correctness.
