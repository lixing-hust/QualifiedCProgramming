From SimpleC.EE.osverify_qcp.cases Require Import ucos_Grant_Cap_goal ucos_Grant_Cap_proof_auto ucos_Grant_Cap_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ucos_Grant_Cap_proof_auto.
  Include ucos_Grant_Cap_proof_manual.
End VC_Correctness.
