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
From SimpleC.EE.osverify_qcp.cases Require Import grant_cspace_cap_inferred_goal.
From SimpleC.EE.osverify_qcp.cases Require Import grant_cspace_cap_inferred_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.osverify_qcp.cases.grant_cspace_cap_inferred_lib.
Local Open Scope sac.

Lemma proof_of_ucos_Grant_Cap_entail_wit_2 : ucos_Grant_Cap_entail_wit_2.
Proof.
LLM_pre_process ltac:(lia).
unfold grant_call_pre, grant_table_cell, grant_type_cell, grant_category_cell, grant_slot_cell.
destruct (Z.leb cap_Class_pre 16) eqn:Hclass.
- apply Z.leb_le in Hclass.
  destruct (Z.ltb destTask_Prio_pre 64) eqn:Hdest.
  + apply Z.ltb_lt in Hdest.
    destruct (Z.eqb dp 0) eqn:Hdp.
    * apply Z.eqb_eq in Hdp.
      Left. Left. Right.
      split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia].
    * apply Z.eqb_neq in Hdp.
      Left. Left. Left.
      split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia].
      reflexivity.
  + apply Z.ltb_ge in Hdest.
    Left. Right.
    split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia].
- apply Z.leb_gt in Hclass.
  Right.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia].
Qed. 

Lemma proof_of_ucos_Grant_Cap_return_wit_1_split_goal_1 : ucos_Grant_Cap_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold grant_rights; reflexivity).
Qed.

Lemma proof_of_ucos_Grant_Cap_return_wit_1 : ucos_Grant_Cap_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_ucos_Grant_Cap_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_1_1_split_goal_1 : grant_cspace_cap_entail_wit_1_1_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_1_1 : grant_cspace_cap_entail_wit_1_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&("destTask_Prio")) destTask_Prio_pre).
  Intros_p Hdest.
  change (0 <= destTask_Prio_pre <= 255) in Hdest.
  prop_apply_p (store_uint_range (&("cap_Class")) cap_Class_pre).
  Intros_p Hclass.
  change (0 <= cap_Class_pre <= 4294967295) in Hclass.
  prop_apply_p (store_uint_range (&("cap_Right")) cap_Right_pre).
  Intros_p Hright.
  change (0 <= cap_Right_pre <= 4294967295) in Hright.
  prop_apply_p (store_uint_range (&(((&((p) # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof("slot")))) # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) auth).
  Intros_p Hauth.
  change (0 <= auth <= 4294967295) in Hauth.
  prop_apply_p (store_uint_range (&(((&((dp) # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof("slot")))) # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) oldright).
  Intros_p Holdright.
  change (0 <= oldright <= 4294967295) in Holdright.
  entailer_with ltac:(lia).
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_1_2_split_goal_1 : grant_cspace_cap_entail_wit_1_2_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_1_2 : grant_cspace_cap_entail_wit_1_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&("destTask_Prio")) destTask_Prio_pre).
  Intros_p Hdest.
  change (0 <= destTask_Prio_pre <= 255) in Hdest.
  prop_apply_p (store_uint_range (&("cap_Class")) cap_Class_pre).
  Intros_p Hclass.
  change (0 <= cap_Class_pre <= 4294967295) in Hclass.
  prop_apply_p (store_uint_range (&("cap_Right")) cap_Right_pre).
  Intros_p Hright.
  change (0 <= cap_Right_pre <= 4294967295) in Hright.
  prop_apply_p (store_uint_range (&(((&((p) # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof("slot")))) # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) auth).
  Intros_p Hauth.
  change (0 <= auth <= 4294967295) in Hauth.
  prop_apply_p (store_uint_range (&(((&((dp) # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof("slot")))) # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) oldright).
  Intros_p Holdright.
  change (0 <= oldright <= 4294967295) in Holdright.
  entailer_with ltac:(lia).
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_1_3_split_goal_1 : grant_cspace_cap_entail_wit_1_3_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_1_3 : grant_cspace_cap_entail_wit_1_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&("destTask_Prio")) destTask_Prio_pre).
  Intros_p Hdest.
  change (0 <= destTask_Prio_pre <= 255) in Hdest.
  prop_apply_p (store_uint_range (&("cap_Class")) cap_Class_pre).
  Intros_p Hclass.
  change (0 <= cap_Class_pre <= 4294967295) in Hclass.
  prop_apply_p (store_uint_range (&("cap_Right")) cap_Right_pre).
  Intros_p Hright.
  change (0 <= cap_Right_pre <= 4294967295) in Hright.
  prop_apply_p (store_uint_range (&(((&((dp) # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof("slot")))) # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) oldright).
  Intros_p Holdright.
  change (0 <= oldright <= 4294967295) in Holdright.
  entailer_with ltac:(lia).
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_1_4_split_goal_1 : grant_cspace_cap_entail_wit_1_4_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_1_4 : grant_cspace_cap_entail_wit_1_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&("destTask_Prio")) destTask_Prio_pre).
  Intros_p Hdest.
  change (0 <= destTask_Prio_pre <= 255) in Hdest.
  prop_apply_p (store_uint_range (&("cap_Class")) cap_Class_pre).
  Intros_p Hclass.
  change (0 <= cap_Class_pre <= 4294967295) in Hclass.
  prop_apply_p (store_uint_range (&("cap_Right")) cap_Right_pre).
  Intros_p Hright.
  change (0 <= cap_Right_pre <= 4294967295) in Hright.
  prop_apply_p (store_uint_range (&(((&((p) # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof("slot")))) # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) auth).
  Intros_p Hauth.
  change (0 <= auth <= 4294967295) in Hauth.
  entailer_with ltac:(lia).
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_1_7_split_goal_1 : grant_cspace_cap_entail_wit_1_7_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_1_7 : grant_cspace_cap_entail_wit_1_7.
Proof.
LLM_pre_process ltac:(lia || nia || int_auto).
prop_apply_p (store_uchar_range (&("destTask_Prio")) destTask_Prio_pre).
Intros_p Hdest.
prop_apply_p (store_uint_range (&("cap_Class")) cap_Class_pre).
Intros_p Hclass.
prop_apply_p (store_uint_range (&("cap_Right")) cap_Right_pre).
Intros_p Hright.
prop_apply_p (store_uint_range (&(((&((p) # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof("slot")))) # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) auth).
Intros_p Hauth.
split_pure_spatial.
- cancel.
- split_pures; dump_pre_spatial; unfold Byte.max_unsigned, Int.max_unsigned in *; simpl in *; lia.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_1_8_split_goal_1 : grant_cspace_cap_entail_wit_1_8_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_1_8 : grant_cspace_cap_entail_wit_1_8.
Proof.
LLM_pre_process ltac:(lia || nia || int_auto).
prop_apply_p (store_uchar_range (&("destTask_Prio")) destTask_Prio_pre).
Intros_p Hdest.
prop_apply_p (store_uint_range (&("cap_Class")) cap_Class_pre).
Intros_p Hclass.
prop_apply_p (store_uint_range (&("cap_Right")) cap_Right_pre).
Intros_p Hright.
prop_apply_p (store_uint_range (&(((&((dp) # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof("slot")))) # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) oldright).
Intros_p Holdright.
split_pure_spatial.
- cancel.
- split_pures; dump_pre_spatial; unfold Byte.max_unsigned, Int.max_unsigned in *; simpl in *; lia.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_1_9_split_goal_1 : grant_cspace_cap_entail_wit_1_9_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_1_9 : grant_cspace_cap_entail_wit_1_9.
Proof.
LLM_pre_process ltac:(lia || nia || int_auto).
prop_apply_p (store_uchar_range (&("destTask_Prio")) destTask_Prio_pre).
Intros_p Hdest.
prop_apply_p (store_uint_range (&("cap_Class")) cap_Class_pre).
Intros_p Hclass.
prop_apply_p (store_uint_range (&("cap_Right")) cap_Right_pre).
Intros_p Hright.
split_pure_spatial.
- cancel.
- split_pures; dump_pre_spatial; unfold Byte.max_unsigned, Int.max_unsigned in *; simpl in *; lia.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_1_11_split_goal_1 : grant_cspace_cap_entail_wit_1_11_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_1_11 : grant_cspace_cap_entail_wit_1_11.
Proof.
LLM_pre_process ltac:(lia || nia || int_auto).
prop_apply_p (store_uchar_range (&("destTask_Prio")) destTask_Prio_pre).
Intros_p Hdest.
prop_apply_p (store_uint_range (&("cap_Class")) cap_Class_pre).
Intros_p Hclass.
prop_apply_p (store_uint_range (&("cap_Right")) cap_Right_pre).
Intros_p Hright.
split_pure_spatial.
- cancel.
- split_pures; dump_pre_spatial; unfold Byte.max_unsigned, Int.max_unsigned in *; simpl in *; lia.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_1_12_split_goal_1 : grant_cspace_cap_entail_wit_1_12_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_1_12 : grant_cspace_cap_entail_wit_1_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&("destTask_Prio")) destTask_Prio_pre).
  Intros.
  prop_apply_p (store_uint_range (&("cap_Class")) cap_Class_pre).
  Intros.
  prop_apply_p (store_uint_range (&("cap_Right")) cap_Right_pre).
  Intros.
  prop_apply_p (store_uint_range
    (&(((&((p) # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof("slot"))))
      # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) auth).
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; unfold Byte.max_unsigned, Int.max_unsigned in *; simpl in *; lia.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_1_13_split_goal_1 : grant_cspace_cap_entail_wit_1_13_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_1_13 : grant_cspace_cap_entail_wit_1_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&("destTask_Prio")) destTask_Prio_pre).
  Intros.
  prop_apply_p (store_uint_range (&("cap_Class")) cap_Class_pre).
  Intros.
  prop_apply_p (store_uint_range (&("cap_Right")) cap_Right_pre).
  Intros.
  prop_apply_p (store_uint_range
    (&(((&((p) # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof("slot"))))
      # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) auth).
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; unfold Byte.max_unsigned, Int.max_unsigned in *; simpl in *; lia.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_1_14_split_goal_1 : grant_cspace_cap_entail_wit_1_14_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_1_14 : grant_cspace_cap_entail_wit_1_14.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&("destTask_Prio")) destTask_Prio_pre).
  Intros.
  prop_apply_p (store_uint_range (&("cap_Class")) cap_Class_pre).
  Intros.
  prop_apply_p (store_uint_range (&("cap_Right")) cap_Right_pre).
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; unfold Byte.max_unsigned, Int.max_unsigned in *; simpl in *; lia.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_1_15_split_goal_1 : grant_cspace_cap_entail_wit_1_15_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_1_15 : grant_cspace_cap_entail_wit_1_15.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&("destTask_Prio")) destTask_Prio_pre).
  Intros.
  prop_apply_p (store_uint_range (&("cap_Class")) cap_Class_pre).
  Intros.
  prop_apply_p (store_uint_range (&("cap_Right")) cap_Right_pre).
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; unfold Byte.max_unsigned, Int.max_unsigned in *; simpl in *; lia.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_3_1_split_goal_1 : grant_cspace_cap_entail_wit_3_1_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_1_split_goal_2 : grant_cspace_cap_entail_wit_3_1_split_goal_2.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_1 : grant_cspace_cap_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&( "OSRunning" )) run).
  Intros_p Hrun.
  change (0 <= run <= 255) in Hrun.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_3_2_split_goal_1 : grant_cspace_cap_entail_wit_3_2_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_2_split_goal_2 : grant_cspace_cap_entail_wit_3_2_split_goal_2.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_2 : grant_cspace_cap_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&( "OSRunning" )) run).
  Intros_p Hrun.
  change (0 <= run <= 255) in Hrun.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_3_3_split_goal_1 : grant_cspace_cap_entail_wit_3_3_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_3_split_goal_2 : grant_cspace_cap_entail_wit_3_3_split_goal_2.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_3 : grant_cspace_cap_entail_wit_3_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&( "OSRunning" )) run).
  Intros_p Hrun.
  change (0 <= run <= 255) in Hrun.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_3_4_split_goal_1 : grant_cspace_cap_entail_wit_3_4_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_4_split_goal_2 : grant_cspace_cap_entail_wit_3_4_split_goal_2.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_4 : grant_cspace_cap_entail_wit_3_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&( "OSRunning" )) run).
  Intros_p Hrun.
  change (0 <= run <= 255) in Hrun.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_3_5_split_goal_1 : grant_cspace_cap_entail_wit_3_5_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_5_split_goal_2 : grant_cspace_cap_entail_wit_3_5_split_goal_2.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_5 : grant_cspace_cap_entail_wit_3_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_uchar.
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | assert (Byte.max_unsigned = 255) by reflexivity; lia].
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_3_6_split_goal_1 : grant_cspace_cap_entail_wit_3_6_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_6_split_goal_2 : grant_cspace_cap_entail_wit_3_6_split_goal_2.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_6 : grant_cspace_cap_entail_wit_3_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_uchar.
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | assert (Byte.max_unsigned = 255) by reflexivity; lia].
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_3_7_split_goal_1 : grant_cspace_cap_entail_wit_3_7_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_7_split_goal_2 : grant_cspace_cap_entail_wit_3_7_split_goal_2.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_7 : grant_cspace_cap_entail_wit_3_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_uchar.
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | assert (Byte.max_unsigned = 255) by reflexivity; lia].
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_3_12_split_goal_1 : grant_cspace_cap_entail_wit_3_12_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_12_split_goal_2 : grant_cspace_cap_entail_wit_3_12_split_goal_2.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_12 : grant_cspace_cap_entail_wit_3_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_uchar.
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | assert (Byte.max_unsigned = 255) by reflexivity; lia].
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_3_13_split_goal_1 : grant_cspace_cap_entail_wit_3_13_split_goal_1.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_13_split_goal_2 : grant_cspace_cap_entail_wit_3_13_split_goal_2.
Proof. Abort.

Lemma proof_of_grant_cspace_cap_entail_wit_3_13 : grant_cspace_cap_entail_wit_3_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_uchar.
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | assert (Byte.max_unsigned = 255) by reflexivity; lia].
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_4_1_split_goal_1 : grant_cspace_cap_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold unsigned_last_nbits.
  apply Z.mod_small.
  cbn; lia.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_4_1 : grant_cspace_cap_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_4_1_split_goal_1.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_4_2_split_goal_1 : grant_cspace_cap_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold unsigned_last_nbits.
  apply Z.mod_small.
  cbn; lia.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_4_2 : grant_cspace_cap_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_4_2_split_goal_1.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_4_3_split_goal_1 : grant_cspace_cap_entail_wit_4_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold unsigned_last_nbits.
  apply Z.mod_small.
  cbn; lia.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_4_3 : grant_cspace_cap_entail_wit_4_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_4_3_split_goal_1.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_4_4_split_goal_1 : grant_cspace_cap_entail_wit_4_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold unsigned_last_nbits.
  apply Z.mod_small.
  cbn; lia.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_4_4 : grant_cspace_cap_entail_wit_4_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_4_4_split_goal_1.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_4_5_split_goal_1 : grant_cspace_cap_entail_wit_4_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold unsigned_last_nbits.
  apply Z.mod_small.
  change (0 <= run < 4294967296).
  lia.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_4_5 : grant_cspace_cap_entail_wit_4_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_4_5_split_goal_1.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_4_6_split_goal_1 : grant_cspace_cap_entail_wit_4_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold unsigned_last_nbits.
  apply Z.mod_small.
  change (0 <= run < 4294967296).
  lia.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_4_6 : grant_cspace_cap_entail_wit_4_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_4_6_split_goal_1.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_4_7_split_goal_1 : grant_cspace_cap_entail_wit_4_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold unsigned_last_nbits.
  apply Z.mod_small.
  change (0 <= run < 4294967296).
  lia.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_4_7 : grant_cspace_cap_entail_wit_4_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_4_7_split_goal_1.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_4_12_split_goal_1 : grant_cspace_cap_entail_wit_4_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold unsigned_last_nbits.
  apply Z.mod_small.
  change (0 <= run < 4294967296).
  lia.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_4_12 : grant_cspace_cap_entail_wit_4_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_4_12_split_goal_1.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_4_13_split_goal_1 : grant_cspace_cap_entail_wit_4_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold unsigned_last_nbits.
  apply Z.mod_small.
  change (0 <= run < 4294967296).
  lia.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_4_13 : grant_cspace_cap_entail_wit_4_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_4_13_split_goal_1.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_5_1_split_goal_spatial : grant_cspace_cap_entail_wit_5_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  unfold grant_call_pre.
  repeat match goal with
  | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec0 x y); try lia
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec0 x y); try lia
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y); try lia
  end.
  unfold grant_table_cell, grant_type_cell, grant_category_cell, grant_slot_cell.
  cancel.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_5_1 : grant_cspace_cap_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_5_1_split_goal_spatial.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_5_2_split_goal_spatial : grant_cspace_cap_entail_wit_5_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  unfold grant_call_pre.
  repeat match goal with
  | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec0 x y); try lia
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec0 x y); try lia
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y); try lia
  end.
  unfold grant_table_cell, grant_type_cell, grant_category_cell, grant_slot_cell.
  cancel.
  repeat match goal with |- ?P ** ?Q |-- _ => cancel P end.
  try match goal with |- ?P |-- ?P => cancel P end.
Qed.


Lemma proof_of_grant_cspace_cap_entail_wit_5_2 : grant_cspace_cap_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_5_2_split_goal_spatial.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_5_3_split_goal_spatial : grant_cspace_cap_entail_wit_5_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  unfold grant_call_pre.
  repeat match goal with
  | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec0 x y); try lia
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec0 x y); try lia
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y); try lia
  end.
  unfold grant_table_cell, grant_type_cell, grant_category_cell, grant_slot_cell.
  cancel.
  repeat match goal with |- ?P ** ?Q |-- _ => cancel P end.
  try match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_5_3 : grant_cspace_cap_entail_wit_5_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_5_3_split_goal_spatial.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_5_4_split_goal_spatial : grant_cspace_cap_entail_wit_5_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  unfold grant_call_pre.
  repeat match goal with
  | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec0 x y); try lia
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec0 x y); try lia
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y); try lia
  end.
  unfold grant_table_cell, grant_type_cell, grant_category_cell, grant_slot_cell.
  cancel.
  repeat match goal with |- ?P ** ?Q |-- _ => cancel P end.
  try match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_5_4 : grant_cspace_cap_entail_wit_5_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_5_4_split_goal_spatial.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_5_5_split_goal_spatial : grant_cspace_cap_entail_wit_5_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  unfold grant_call_pre.
  repeat match goal with
  | |- context [Z.leb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.leb x y) eqn:H;
      [apply Z.leb_le in H | apply Z.leb_gt in H]; try lia
  | |- context [Z.ltb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.ltb x y) eqn:H;
      [apply Z.ltb_lt in H | apply Z.ltb_ge in H]; try lia
  | |- context [Z.eqb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.eqb x y) eqn:H;
      [apply Z.eqb_eq in H | apply Z.eqb_neq in H]; try lia
  end.
  all: unfold grant_table_cell, grant_type_cell, grant_category_cell, grant_slot_cell; cancel.
  all: repeat match goal with
  | |- ?P ** _ |-- _ => cancel P
  | |- ?P |-- ?P => cancel P
  end.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_5_5 : grant_cspace_cap_entail_wit_5_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_5_5_split_goal_spatial.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_5_6_split_goal_spatial : grant_cspace_cap_entail_wit_5_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  unfold grant_call_pre.
  repeat match goal with
  | |- context [Z.leb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.leb x y) eqn:H;
      [apply Z.leb_le in H | apply Z.leb_gt in H]; try lia
  | |- context [Z.ltb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.ltb x y) eqn:H;
      [apply Z.ltb_lt in H | apply Z.ltb_ge in H]; try lia
  | |- context [Z.eqb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.eqb x y) eqn:H;
      [apply Z.eqb_eq in H | apply Z.eqb_neq in H]; try lia
  end.
  all: unfold grant_table_cell, grant_type_cell, grant_category_cell, grant_slot_cell; cancel.
  all: repeat match goal with
  | |- ?P ** _ |-- _ => cancel P
  | |- ?P |-- ?P => cancel P
  end.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_5_6 : grant_cspace_cap_entail_wit_5_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_5_6_split_goal_spatial.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_5_7_split_goal_spatial : grant_cspace_cap_entail_wit_5_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  unfold grant_call_pre.
  repeat match goal with
  | |- context [Z.leb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.leb x y) eqn:H;
      [apply Z.leb_le in H | apply Z.leb_gt in H]; try lia
  | |- context [Z.ltb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.ltb x y) eqn:H;
      [apply Z.ltb_lt in H | apply Z.ltb_ge in H]; try lia
  | |- context [Z.eqb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.eqb x y) eqn:H;
      [apply Z.eqb_eq in H | apply Z.eqb_neq in H]; try lia
  end.
  all: unfold grant_table_cell, grant_type_cell, grant_category_cell, grant_slot_cell; cancel.
  all: repeat match goal with
  | |- ?P ** _ |-- _ => cancel P
  | |- ?P |-- ?P => cancel P
  end.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_5_7 : grant_cspace_cap_entail_wit_5_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_5_7_split_goal_spatial.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_5_8_split_goal_spatial : grant_cspace_cap_entail_wit_5_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  unfold grant_call_pre.
  repeat match goal with
  | |- context [Z.leb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.leb x y) eqn:H;
      [apply Z.leb_le in H | apply Z.leb_gt in H]; try lia
  | |- context [Z.ltb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.ltb x y) eqn:H;
      [apply Z.ltb_lt in H | apply Z.ltb_ge in H]; try lia
  | |- context [Z.eqb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.eqb x y) eqn:H;
      [apply Z.eqb_eq in H | apply Z.eqb_neq in H]; try lia
  end.
  all: unfold grant_table_cell, grant_type_cell, grant_category_cell, grant_slot_cell; cancel.
  all: repeat match goal with
  | |- ?P ** _ |-- _ => cancel P
  | |- ?P |-- ?P => cancel P
  end.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_5_8 : grant_cspace_cap_entail_wit_5_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_5_8_split_goal_spatial.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_5_9_split_goal_spatial : grant_cspace_cap_entail_wit_5_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  unfold grant_call_pre.
  repeat match goal with
  | |- context [Z.leb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.leb x y) eqn:H;
      [apply Z.leb_le in H | apply Z.leb_gt in H]; try lia
  | |- context [Z.ltb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.ltb x y) eqn:H;
      [apply Z.ltb_lt in H | apply Z.ltb_ge in H]; try lia
  | |- context [Z.eqb ?x ?y] =>
      let H := fresh "Htest" in destruct (Z.eqb x y) eqn:H;
      [apply Z.eqb_eq in H | apply Z.eqb_neq in H]; try lia
  end.
  all: unfold grant_table_cell, grant_type_cell, grant_category_cell, grant_slot_cell; cancel.
  all: repeat match goal with
  | |- ?P ** _ |-- _ => cancel P
  | |- ?P |-- ?P => cancel P
  end.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_5_9 : grant_cspace_cap_entail_wit_5_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_5_9_split_goal_spatial.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_5_10_split_goal_spatial : grant_cspace_cap_entail_wit_5_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  unfold grant_call_pre.
  repeat match goal with
  | |- context [Z.leb ?x ?y] => let E := fresh "E" in destruct (Z.leb x y) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E]; try lia
  | |- context [Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; try lia
  | |- context [Z.eqb ?x ?y] => let E := fresh "E" in destruct (Z.eqb x y) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; try lia
  end.
  unfold grant_table_cell, grant_type_cell, grant_category_cell, grant_slot_cell.
  cbn.
  cancel.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_5_10 : grant_cspace_cap_entail_wit_5_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_5_10_split_goal_spatial.
Qed. 

Lemma proof_of_grant_cspace_cap_entail_wit_5_11_split_goal_spatial : grant_cspace_cap_entail_wit_5_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  unfold grant_call_pre.
  repeat match goal with
  | |- context [Z.leb ?x ?y] => let E := fresh "E" in destruct (Z.leb x y) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E]; try lia
  | |- context [Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; try lia
  | |- context [Z.eqb ?x ?y] => let E := fresh "E" in destruct (Z.eqb x y) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; try lia
  end.
  unfold grant_table_cell, grant_type_cell, grant_category_cell, grant_slot_cell.
  cbn.
  cancel.
Qed.

Lemma proof_of_grant_cspace_cap_entail_wit_5_11 : grant_cspace_cap_entail_wit_5_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_grant_cspace_cap_entail_wit_5_11_split_goal_spatial.
Qed. 

