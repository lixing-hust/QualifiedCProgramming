From SimpleC.EE.osverify_qcp.cases Require Import UserAddrCheck_goal UserAddrCheck_proof_auto UserAddrCheck_proof_manual.

Module VC_Correctness : VC_Correct.
  Include UserAddrCheck_proof_auto.
  Include UserAddrCheck_proof_manual.
End VC_Correctness.
