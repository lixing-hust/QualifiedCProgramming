From SimpleC.EE.Applications.cnf_trans Require Import cnf_trans_goal cnf_trans_proof_auto cnf_trans_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include cnf_trans_proof_auto.
  Include cnf_trans_proof_manual.
End VC_Correctness.
