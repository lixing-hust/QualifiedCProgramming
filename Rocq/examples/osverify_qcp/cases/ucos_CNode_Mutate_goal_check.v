From SimpleC.EE.osverify_qcp.cases Require Import ucos_CNode_Mutate_goal ucos_CNode_Mutate_proof_auto ucos_CNode_Mutate_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ucos_CNode_Mutate_proof_auto.
  Include ucos_CNode_Mutate_proof_manual.
End VC_Correctness.
