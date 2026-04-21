From SimpleC.EE.LLM_friendly_cases Require Import sortArray_goal sortArray_proof_auto sortArray_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sortArray_proof_auto.
  Include sortArray_proof_manual.
End VC_Correctness.
