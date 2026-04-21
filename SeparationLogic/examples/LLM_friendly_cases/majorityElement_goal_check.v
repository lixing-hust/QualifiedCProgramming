From SimpleC.EE.LLM_friendly_cases Require Import majorityElement_goal majorityElement_proof_auto majorityElement_proof_manual.

Module VC_Correctness : VC_Correct.
  Include majorityElement_proof_auto.
  Include majorityElement_proof_manual.
End VC_Correctness.
