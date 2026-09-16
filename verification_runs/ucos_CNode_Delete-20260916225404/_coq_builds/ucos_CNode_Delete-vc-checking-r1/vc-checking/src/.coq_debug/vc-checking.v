From SimpleC.EE.osverify_qcp.cases Require Import ucos_CNode_Delete_goal.
From SimpleC.EE.osverify_qcp.cases Require Import ucos_CNode_Delete_lib.
Require Import Coq.micromega.Psatz.
Goal SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_goal.ucos_CNode_Delete_return_wit_1_category_cap_split_goal_1.
Show.
unfold ucos_CNode_Delete_return_wit_1_category_cap_split_goal_1.
intros.
unfold delete_slot_transition, delete_slot_result; cbn.
Show.
reflexivity.
Abort.
Goal SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_goal.ucos_CNode_Delete_return_wit_2_object_cap_split_goal_1.
Show.
unfold ucos_CNode_Delete_return_wit_2_object_cap_split_goal_1.
intros.
unfold delete_slot_transition, delete_slot_result; cbn.
Show.
reflexivity.
Abort.
Goal SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_goal.ucos_CNode_Delete_return_wit_3_unsupported_cap_split_goal_1.
Show.
unfold ucos_CNode_Delete_return_wit_3_unsupported_cap_split_goal_1.
intros.
unfold delete_slot_transition, delete_slot_result; cbn.
Show.
destruct (Z.eq_dec old_cap_unsupported_cap 1); [contradiction |].
destruct (Z.eq_dec old_cap_unsupported_cap 2); [contradiction | reflexivity].
Abort.
