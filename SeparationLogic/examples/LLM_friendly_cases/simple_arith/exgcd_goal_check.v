From SimpleC.EE.LLM_friendly_cases.simple_arith Require Import exgcd_goal exgcd_proof_auto exgcd_proof_manual.

Module VC_Correctness : VC_Correct.
  Include exgcd_proof_auto.
  Include exgcd_proof_manual.
End VC_Correctness.
