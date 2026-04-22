From SimpleC.EE.leetcode.output.verify_20260414_153520_factorial.annotated Require Import factorial_goal factorial_proof_auto factorial_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include factorial_proof_auto.
  Include factorial_proof_manual.
End VC_Correctness.
