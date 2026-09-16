From Coq Require Import ZArith.
Require Import SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_goal.
Require Import SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_lib.
Local Open Scope Z_scope.

Goal SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_goal.ucos_CNode_Delete_return_wit_1_category_cap_split_goal_1.
Show.
unfold ucos_CNode_Delete_return_wit_1_category_cap_split_goal_1.
intros.
unfold delete_slot_transition, delete_slot_result.
cbn.
reflexivity.
Abort.

Goal SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_goal.ucos_CNode_Delete_return_wit_2_object_cap_split_goal_1.
Show.
unfold ucos_CNode_Delete_return_wit_2_object_cap_split_goal_1.
intros.
unfold delete_slot_transition, delete_slot_result.
cbn.
reflexivity.
Abort.

Goal SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_goal.ucos_CNode_Delete_return_wit_3_unsupported_cap_split_goal_1.
Show.
unfold ucos_CNode_Delete_return_wit_3_unsupported_cap_split_goal_1.
intros.
unfold delete_slot_transition, delete_slot_result.
cbn.
repeat match goal with
| |- context [Z.eq_dec ?a ?b] => destruct (Z.eq_dec a b)
end; congruence.
Abort.
