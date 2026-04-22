From SimpleC.EE.CAV.verify_20260421_052410_count_digits Require Import count_digits_goal count_digits_proof_auto count_digits_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include count_digits_proof_auto.
  Include count_digits_proof_manual.
End VC_Correctness.
