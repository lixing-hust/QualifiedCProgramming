From SimpleC.EE.osverify_qcp.cases Require Import grant_cspace_cap_goal grant_cspace_cap_proof_auto grant_cspace_cap_proof_manual.

Module VC_Correctness : VC_Correct.
  Include grant_cspace_cap_proof_auto.
  Include grant_cspace_cap_proof_manual.
End VC_Correctness.
