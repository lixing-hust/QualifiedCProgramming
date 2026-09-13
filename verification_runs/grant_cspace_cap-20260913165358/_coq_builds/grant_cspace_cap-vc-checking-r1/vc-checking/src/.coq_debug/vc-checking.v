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
Require Import SetsClass.SetsClass.
Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.osverify_qcp.cases Require Import grant_cspace_cap_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.
Set Printing All.

Goal SimpleC.EE.osverify_qcp.cases.grant_cspace_cap_goal.ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial.
Show.
assert_succeeds (intros; pre_process; entailer!).
Abort.

Goal SimpleC.EE.osverify_qcp.cases.grant_cspace_cap_goal.grant_cspace_cap_return_wit_1_split_goal_1.
Show.
assert_succeeds (intros; pre_process; entailer!).
Abort.

Goal SimpleC.EE.osverify_qcp.cases.grant_cspace_cap_goal.grant_cspace_cap_return_wit_2_split_goal_1.
Show.
assert_succeeds (intros; pre_process; entailer!).
Abort.

Goal SimpleC.EE.osverify_qcp.cases.grant_cspace_cap_goal.grant_cspace_cap_return_wit_3_split_goal_1.
Show.
assert_succeeds (intros; pre_process; entailer!).
Abort.

Goal SimpleC.EE.osverify_qcp.cases.grant_cspace_cap_goal.grant_cspace_cap_return_wit_4.
Show.
assert_succeeds (intros; pre_process; entailer!).
Abort.

Goal SimpleC.EE.osverify_qcp.cases.grant_cspace_cap_goal.grant_cspace_cap_return_wit_5.
Show.
assert_succeeds (intros; pre_process; entailer!).
Abort.

Goal SimpleC.EE.osverify_qcp.cases.grant_cspace_cap_goal.grant_cspace_cap_return_wit_6.
Show.
assert_succeeds (intros; pre_process; entailer!).
Abort.

Goal SimpleC.EE.osverify_qcp.cases.grant_cspace_cap_goal.grant_cspace_cap_return_wit_7_callee_null.
Show.
assert_succeeds (intros; pre_process; entailer!).
Abort.

Goal SimpleC.EE.osverify_qcp.cases.grant_cspace_cap_goal.grant_cspace_cap_return_wit_8_callee_invalid.
Show.
assert_succeeds (intros; pre_process; entailer!).
Abort.

Goal SimpleC.EE.osverify_qcp.cases.grant_cspace_cap_goal.grant_cspace_cap_return_wit_11_callee_success.
Show.
assert_succeeds (intros; pre_process; entailer!).
Abort.
