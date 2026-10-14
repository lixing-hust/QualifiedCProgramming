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
From SimpleC.EE.osverify_qcp.cases Require Import ucos_get_obj_slot_copy_independent_20261013_goal.
From SimpleC.EE.osverify_qcp.cases Require Import ucos_get_obj_slot_copy_independent_20261013_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.osverify_qcp.cases.ucos_get_obj_slot_copy_independent_20261013_lib.
Local Open Scope sac.

Lemma proof_of_Get_Obj_Slot_entail_wit_1_split_goal_1 : Get_Obj_Slot_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold copy_lookup_input_safe in *.
  unfold copy_lookup_scan_inv.
  assert (Hcount : 0 <= copy_lookup_count xs).
  { unfold copy_lookup_count. apply Nat2Z.is_nonneg. }
  split; [lia |].
  split; [apply Z.le_max_l |].
  split; [lia |].
  split.
  - unfold copy_lookup_prefix_absent. intros j Hj. lia.
  - match goal with H : _ /\ (_ -> _ -> copy_lookup_read_safe _ _ _) |- _ =>
      apply (proj2 H); assumption end.
Qed.

Lemma proof_of_Get_Obj_Slot_entail_wit_1 : Get_Obj_Slot_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_Get_Obj_Slot_entail_wit_2_split_goal_1 : Get_Obj_Slot_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (copy_lookup_active_bound__cells_scan _ _ _ _ PreH5 PreH1) as Hb.
  destruct PreH5 as [_ [_ [_ [_ [_ [Hcount _]]]]]].
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_Get_Obj_Slot_entail_wit_2_split_goal_spatial : Get_Obj_Slot_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (copy_lookup_active_bound__cells_scan _ _ _ _ PreH5 PreH1) as Hb.
  destruct PreH5 as [Hlo _].
  unfold copy_lookup_count in Hb.
  change (copy_lookup_cells p sizeof("slot") 17 xs |--
    copy_lookup_cells_hole p sizeof("slot") 17 xs i **
    store_ptr (copy_lookup_object_address p sizeof("slot") i) (nth (Z.to_nat(i-17)) xs 0)).
  apply copy_lookup_cells_extract__cells_scan. lia.
Qed.

Lemma proof_of_Get_Obj_Slot_entail_wit_2 : Get_Obj_Slot_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_entail_wit_2_split_goal_spatial.
  Goal_apply proof_of_Get_Obj_Slot_entail_wit_2_split_goal_1.
Qed. 

Lemma proof_of_Get_Obj_Slot_entail_wit_3_split_goal_1 : Get_Obj_Slot_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (copy_lookup_active_bound__cells_scan _ _ _ _ PreH5 PreH6) as Hb.
  destruct PreH5 as [Hlo [Hm [Hbound [Habs Hsafe]]]].
  dump_pre_spatial. unfold copy_lookup_scan_inv.
  split; [lia|]. split.
  - pose proof (Z.le_max_r 17 finish). lia.
  - split; [lia|]. split; [|exact Hsafe].
    intros j Hj. destruct (Z_lt_ge_dec j i).
    + apply Habs. lia.
    + assert (j=i) by lia. subst j. congruence.
Qed.

Lemma proof_of_Get_Obj_Slot_entail_wit_3_split_goal_spatial : Get_Obj_Slot_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (copy_lookup_active_bound__cells_scan _ _ _ _ PreH5 PreH6) as Hb.
  destruct PreH5 as [Hlo _].
  unfold copy_lookup_count in Hb.
  rewrite PreH8.
  change (copy_lookup_cells_hole p sizeof("slot") 17 xs i **
    store_ptr (copy_lookup_object_address p sizeof("slot") i) (nth (Z.to_nat(i-17)) xs 0)
    |-- copy_lookup_cells p sizeof("slot") 17 xs).
  apply copy_lookup_cells_restore__cells_scan. lia.
Qed.

Lemma proof_of_Get_Obj_Slot_entail_wit_3 : Get_Obj_Slot_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_entail_wit_3_split_goal_spatial.
  Goal_apply proof_of_Get_Obj_Slot_entail_wit_3_split_goal_1.
Qed. 

Lemma proof_of_Get_Obj_Slot_return_wit_1_split_goal_1 : Get_Obj_Slot_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold copy_lookup_result. right. right.
  split; [assumption |]. split; [assumption |].
  unfold copy_lookup_search_result. right.
  unfold copy_lookup_scan_inv in *.
  match goal with H : 17 <= _ /\ _ |- _ =>
    destruct H as [Hlo [Hmax [Hbound [Habs Hsafe]]]] end.
  split; [reflexivity |]. split; [lia |].
  unfold copy_lookup_prefix_absent in *.
  intros j Hj. apply Habs. lia.
Qed.

Lemma proof_of_Get_Obj_Slot_return_wit_1 : Get_Obj_Slot_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_Get_Obj_Slot_return_wit_2_split_goal_1 : Get_Obj_Slot_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (copy_lookup_active_bound__cells_scan _ _ _ _ PreH5 PreH6) as Hb.
  destruct PreH5 as [Hlo [Hm [Hbound [Habs Hsafe]]]].
  dump_pre_spatial. unfold copy_lookup_result, copy_lookup_search_result, copy_lookup_first.
  right. right. split; [assumption|]. split; [assumption|]. left.
  repeat split; try lia; try congruence; assumption.
Qed.

Lemma proof_of_Get_Obj_Slot_return_wit_2_split_goal_spatial : Get_Obj_Slot_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (copy_lookup_active_bound__cells_scan _ _ _ _ PreH5 PreH6) as Hb.
  destruct PreH5 as [Hlo _].
  unfold copy_lookup_count in Hb.
  rewrite PreH8.
  change (copy_lookup_cells_hole p sizeof("slot") 17 xs i **
    store_ptr (copy_lookup_object_address p sizeof("slot") i) (nth (Z.to_nat(i-17)) xs 0)
    |-- copy_lookup_cells p sizeof("slot") 17 xs).
  apply copy_lookup_cells_restore__cells_scan. lia.
Qed.

Lemma proof_of_Get_Obj_Slot_return_wit_2 : Get_Obj_Slot_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_return_wit_2_split_goal_spatial.
  Goal_apply proof_of_Get_Obj_Slot_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_Get_Obj_Slot_return_wit_3_split_goal_1 : Get_Obj_Slot_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold copy_lookup_result. right. left. repeat split; auto.
Qed.

Lemma proof_of_Get_Obj_Slot_return_wit_3 : Get_Obj_Slot_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_return_wit_3_split_goal_1.
Qed. 

Lemma proof_of_Get_Obj_Slot_return_wit_4_split_goal_1 : Get_Obj_Slot_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold copy_lookup_result. left. split; [lia | reflexivity].
Qed.

Lemma proof_of_Get_Obj_Slot_return_wit_4 : Get_Obj_Slot_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_return_wit_4_split_goal_1.
Qed. 

