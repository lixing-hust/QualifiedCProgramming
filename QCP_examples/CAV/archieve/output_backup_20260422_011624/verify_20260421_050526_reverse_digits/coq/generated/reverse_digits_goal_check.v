From SimpleC.EE.CAV.verify_20260421_050526_reverse_digits Require Import reverse_digits_goal reverse_digits_proof_auto reverse_digits_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include reverse_digits_proof_auto.
  Include reverse_digits_proof_manual.
End VC_Correctness.
