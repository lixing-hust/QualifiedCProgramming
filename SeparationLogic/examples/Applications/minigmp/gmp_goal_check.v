From SimpleC.EE.Applications.minigmp Require Import gmp_goal gmp_proof_auto gmp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include gmp_proof_auto.
  Include gmp_proof_manual.
End VC_Correctness.
