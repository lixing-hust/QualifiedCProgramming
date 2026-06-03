From SimpleC.EE Require Import C_119_goal C_119_proof_auto C_119_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include C_119_proof_auto.
  Include C_119_proof_manual.
End VC_Correctness.
