Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.osverify_qcp.cases Require Import grant_cspace_cap_goal.
From SimpleC.EE.osverify_qcp.cases Require Import grant_cspace_cap_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial : ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst dest_valid_target class_valid_target right_valid_target.
  cancel.
Qed.

Lemma proof_of_ucos_Grant_Cap_return_wit_1_valid_target : ucos_Grant_Cap_return_wit_1_valid_target.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial.
Qed.

Lemma proof_of_grant_cspace_cap_return_wit_1_split_goal_1 : grant_cspace_cap_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intro Hrunning.
  apply PreH3.
  subst running.
  reflexivity.
Qed.

Lemma proof_of_grant_cspace_cap_return_wit_1 : grant_cspace_cap_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_grant_cspace_cap_return_wit_2_split_goal_1 : grant_cspace_cap_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intro Hrunning.
  apply PreH3.
  subst running.
  reflexivity.
Qed.

Lemma proof_of_grant_cspace_cap_return_wit_2 : grant_cspace_cap_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_grant_cspace_cap_return_wit_3_split_goal_1 : grant_cspace_cap_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intro Hrunning.
  apply PreH3.
  subst running.
  reflexivity.
Qed.

Lemma proof_of_grant_cspace_cap_return_wit_3 : grant_cspace_cap_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_grant_cspace_cap_return_wit_4 : grant_cspace_cap_return_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrunning : running <> 0).
  {
    intro Hzero.
    apply PreH2.
    subst running.
    reflexivity.
  }
  Right.
  split_pure_spatial.
  - cancel ((( &( "OSTCBCur" ) )) # Ptr |-> current_tcb);
    cancel ((&((current_tcb) # "os_tcb" ->ₛ "OSTCBPrio")) # UChar |-> current_prio);
    cancel ((( &( "OSPrioCur" ) )) # UChar |-> current_prio);
    cancel (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr |-> current_space);
    cancel ((( &( "OSRunning" ) )) # UChar |-> running);
    cancel ((&(((&((current_space) # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" )))) # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt |-> grant_right);
    cancel (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar |-> parent).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_grant_cspace_cap_return_wit_5 : grant_cspace_cap_return_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrunning : running <> 0).
  {
    intro Hzero.
    apply PreH2.
    subst running.
    reflexivity.
  }
  Right.
  split_pure_spatial.
  - cancel ((( &( "OSTCBCur" ) )) # Ptr |-> current_tcb);
    cancel ((&((current_tcb) # "os_tcb" ->ₛ "OSTCBPrio")) # UChar |-> current_prio);
    cancel ((( &( "OSPrioCur" ) )) # UChar |-> current_prio);
    cancel (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr |-> current_space);
    cancel ((( &( "OSRunning" ) )) # UChar |-> running);
    cancel ((&(((&((current_space) # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" )))) # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt |-> grant_right);
    cancel (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar |-> parent);
    cancel (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr |-> target);
    cancel ((&(((&((target) # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" )))) # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt |-> old_type);
    cancel ((&(((&((target) # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" )))) # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt |-> old_content);
    cancel ((&(((&((target) # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" )))) # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt |-> old_right).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_grant_cspace_cap_return_wit_6 : grant_cspace_cap_return_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrunning : running <> 0).
  {
    intro Hzero.
    apply PreH2.
    subst running.
    reflexivity.
  }
  Right.
  split_pure_spatial.
  - cancel ((( &( "OSTCBCur" ) )) # Ptr |-> current_tcb);
    cancel ((&((current_tcb) # "os_tcb" ->ₛ "OSTCBPrio")) # UChar |-> current_prio);
    cancel ((( &( "OSPrioCur" ) )) # UChar |-> current_prio);
    cancel (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr |-> current_space);
    cancel ((( &( "OSRunning" ) )) # UChar |-> running);
    cancel ((&(((&((current_space) # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" )))) # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt |-> grant_right);
    cancel (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar |-> parent);
    cancel (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr |-> target).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_grant_cspace_cap_return_wit_7_callee_null : grant_cspace_cap_return_wit_7_callee_null.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&( "OSRunning" )) running).
  Intros_p Hrunning_range.
  replace Byte.max_unsigned with 255 in Hrunning_range by reflexivity.
  assert (Hrunning_bits : unsigned_last_nbits running 32 = running).
  { apply unsigned_last_nbits_eq.
    replace (2 ^ 32) with 4294967296 by reflexivity.
    lia. }
  rewrite Hrunning_bits in PreH3.
  subst running.
  subst target.
  Right.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia; try int_auto.
Qed.

Lemma proof_of_grant_cspace_cap_return_wit_8_callee_invalid : grant_cspace_cap_return_wit_8_callee_invalid.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&( "OSRunning" )) running).
  Intros_p Hrunning_range.
  replace Byte.max_unsigned with 255 in Hrunning_range by reflexivity.
  assert (Hrunning_bits : unsigned_last_nbits running 32 = running).
  { apply unsigned_last_nbits_eq.
    replace (2 ^ 32) with 4294967296 by reflexivity.
    lia. }
  rewrite Hrunning_bits in PreH3.
  subst running.
  Right.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia; try int_auto.
Qed.

Lemma proof_of_grant_cspace_cap_return_wit_11_callee_success : grant_cspace_cap_return_wit_11_callee_success.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&( "OSRunning" )) running).
  Intros_p Hrunning_range.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hrunning_range by reflexivity.
  rewrite unsigned_last_nbits_eq in PreH3 by lia.
  subst running.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; lia.
Qed.
