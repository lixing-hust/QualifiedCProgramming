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
From SimpleC.EE Require Import C_129_goal.
From SimpleC.EE Require Import C_129_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_129.
Local Open Scope sac.

Ltac c129_basic :=
  pre_process_default; try entailer!; try lia; try nia.

Lemma proof_of_minPath_safety_wit_9_split_goal_1 : minPath_safety_wit_9_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_safety_wit_9_split_goal_2 : minPath_safety_wit_9_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_safety_wit_9 : minPath_safety_wit_9.
Proof.
  c129_basic.
Qed. 

Lemma proof_of_minPath_entail_wit_1_split_goal_1 : minPath_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_1_split_goal_2 : minPath_entail_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_1_split_goal_spatial : minPath_entail_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_1 : minPath_entail_wit_1.
Proof.
  pre_process_default.
  unfold find_one_scan_state_129, no_one_before_129, scanned_before_129.
  entailer!.
  right.
  intros r c [[? ?] [? Hscan]].
  destruct Hscan as [? | [? ?]]; lia.
Qed. 

Lemma proof_of_minPath_entail_wit_2_split_goal_1 : minPath_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_2_split_goal_2 : minPath_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_2_split_goal_spatial : minPath_entail_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_2 : minPath_entail_wit_2.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre i n_pre rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows i nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows __default__List_Z))
      (Znth i rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth i rows __default__List_Z))
        (Znth i rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed. 

Lemma proof_of_minPath_entail_wit_4_1_split_goal_1 : minPath_entail_wit_4_1_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_4_1_split_goal_spatial : minPath_entail_wit_4_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_4_1 : minPath_entail_wit_4_1.
Proof.
  pre_process_default.
  Exists row_ptr_2.
  unfold find_one_scan_state_129, one_pos_z_129.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_4_2_split_goal_1 : minPath_entail_wit_4_2_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_4_2_split_goal_spatial : minPath_entail_wit_4_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_4_2 : minPath_entail_wit_4_2.
Proof.
  pre_process_default.
  Exists row_ptr_2.
  entailer!.
  apply find_one_scan_state_step_not_one_129; try lia; assumption.
Qed. 

Lemma proof_of_minPath_entail_wit_5_split_goal_1 : minPath_entail_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_5_split_goal_2 : minPath_entail_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_5_split_goal_spatial : minPath_entail_wit_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_5 : minPath_entail_wit_5.
Proof.
  pre_process_default.
  pose proof (find_one_scan_state_finish_row_129
    rows n_pre i j x y ltac:(lia) ltac:(lia) ltac:(lia) PreH21)
    as Hscan_next.
  rewrite (Znth_indep rows i nil __default__List_Z) by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre i n_pre row_ptr rows
    (Znth i rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth i rows __default__List_Z))
    (Znth i rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth i rows __default__List_Z))
      (Znth i rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_6_split_goal_1 : minPath_entail_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_6_split_goal_2 : minPath_entail_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_6_split_goal_spatial : minPath_entail_wit_6_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_6 : minPath_entail_wit_6.
Proof.
  c129_basic.
Qed. 

Lemma proof_of_minPath_entail_wit_7_split_goal_1 : minPath_entail_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_7_split_goal_2 : minPath_entail_wit_7_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_7_split_goal_3 : minPath_entail_wit_7_split_goal_3.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_7_split_goal_spatial : minPath_entail_wit_7_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_7 : minPath_entail_wit_7.
Proof.
  pre_process_default.
  pose proof (find_one_scan_state_found_129
    rows n_pre i x y one_x one_y __default__List_Z
    PreH11 PreH13 ltac:(lia) ltac:(lia) PreH19
    ltac:(lia) ltac:(lia) PreH20) as Hfound.
  assert (i = n_pre) by lia; subst i.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_8_split_goal_1 : minPath_entail_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_8_split_goal_2 : minPath_entail_wit_8_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_8_split_goal_3 : minPath_entail_wit_8_split_goal_3.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_8_split_goal_spatial : minPath_entail_wit_8_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_8 : minPath_entail_wit_8.
Proof.
  pre_process_default.
  pose proof (checked_neighbor_min_init_129 rows n_pre x y PreH1 PreH17) as Hchecked.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_9 : minPath_entail_wit_9.
Proof.
  pre_process_default.
  pose proof PreH14 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre (x - 1) n_pre rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows (x - 1) nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth (x - 1) rows __default__List_Z))
      (Znth (x - 1) rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth (x - 1) rows __default__List_Z))
        (Znth (x - 1) rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed. 

Lemma proof_of_minPath_entail_wit_10_1_split_goal_1 : minPath_entail_wit_10_1_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_10_1_split_goal_2 : minPath_entail_wit_10_1_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_10_1_split_goal_spatial : minPath_entail_wit_10_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_10_1 : minPath_entail_wit_10_1.
Proof.
  pre_process_default.
  set (v := Znth y (Znth (x - 1) rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 0 v).
  {
    unfold v, dir_neighbor_value_129.
    left; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_keep_129
    rows n_pre x y 0 min v ltac:(lia) PreH20 Hdir ltac:(lia))
    as Hchecked.
  rewrite (Znth_indep rows (x - 1) nil __default__List_Z) by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre (x - 1) n_pre row_ptr rows
    (Znth (x - 1) rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth (x - 1) rows __default__List_Z))
    (Znth (x - 1) rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth (x - 1) rows __default__List_Z))
      (Znth (x - 1) rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_10_2_split_goal_1 : minPath_entail_wit_10_2_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_10_2_split_goal_2 : minPath_entail_wit_10_2_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_10_2_split_goal_3 : minPath_entail_wit_10_2_split_goal_3.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_10_2_split_goal_spatial : minPath_entail_wit_10_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_10_2 : minPath_entail_wit_10_2.
Proof.
  pre_process_default.
  set (v := Znth y (Znth (x - 1) rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 0 v).
  {
    unfold v, dir_neighbor_value_129.
    left; repeat split; lia.
  }
  assert (Hv : 1 <= v <= n_pre * n_pre).
  {
    unfold v.
    rewrite (Znth_indep rows (x - 1) nil __default__List_Z) by lia.
    apply PreH17; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_update_129
    rows n_pre x y 0 min v ltac:(lia) PreH20 Hdir ltac:(lia) Hv)
    as Hchecked.
  rewrite (Znth_indep rows (x - 1) nil __default__List_Z) in * by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre (x - 1) n_pre row_ptr rows
    (Znth (x - 1) rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth (x - 1) rows __default__List_Z))
    (Znth (x - 1) rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth (x - 1) rows __default__List_Z))
      (Znth (x - 1) rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_11_1 : minPath_entail_wit_11_1.
Proof.
  pre_process_default.
  assert (Habsent : forall v, ~ dir_neighbor_value_129 rows n_pre x y 0 v).
  {
    intros v Hdir.
    unfold dir_neighbor_value_129 in Hdir.
    repeat
      match goal with
      | H : _ \/ _ |- _ => destruct H as [H | H]
      | H : _ /\ _ |- _ => destruct H as [? H]
      end; lia.
  }
  pose proof (checked_neighbor_min_step_absent_129
    rows n_pre x y 0 min ltac:(lia) PreH16 Habsent) as Hchecked.
  pose proof PreH15 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre (x + 1) n_pre rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows (x + 1) nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth (x + 1) rows __default__List_Z))
      (Znth (x + 1) rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth (x + 1) rows __default__List_Z))
        (Znth (x + 1) rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed. 

Lemma proof_of_minPath_entail_wit_11_2 : minPath_entail_wit_11_2.
Proof.
  pre_process_default.
  pose proof PreH14 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre (x + 1) n_pre rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows (x + 1) nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth (x + 1) rows __default__List_Z))
      (Znth (x + 1) rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth (x + 1) rows __default__List_Z))
        (Znth (x + 1) rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed. 

Lemma proof_of_minPath_entail_wit_12_1_split_goal_1 : minPath_entail_wit_12_1_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_12_1_split_goal_2 : minPath_entail_wit_12_1_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_12_1_split_goal_spatial : minPath_entail_wit_12_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_12_1 : minPath_entail_wit_12_1.
Proof.
  pre_process_default.
  set (v := Znth y (Znth (x + 1) rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 1 v).
  {
    unfold v, dir_neighbor_value_129.
    right; left; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_keep_129
    rows n_pre x y 1 min v ltac:(lia) PreH20 Hdir ltac:(lia))
    as Hchecked.
  rewrite (Znth_indep rows (x + 1) nil __default__List_Z) by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre (x + 1) n_pre row_ptr rows
    (Znth (x + 1) rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth (x + 1) rows __default__List_Z))
    (Znth (x + 1) rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth (x + 1) rows __default__List_Z))
      (Znth (x + 1) rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_12_2_split_goal_1 : minPath_entail_wit_12_2_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_12_2_split_goal_2 : minPath_entail_wit_12_2_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_12_2_split_goal_3 : minPath_entail_wit_12_2_split_goal_3.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_12_2_split_goal_spatial : minPath_entail_wit_12_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_12_2 : minPath_entail_wit_12_2.
Proof.
  pre_process_default.
  set (v := Znth y (Znth (x + 1) rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 1 v).
  {
    unfold v, dir_neighbor_value_129.
    right; left; repeat split; lia.
  }
  assert (Hv : 1 <= v <= n_pre * n_pre).
  {
    unfold v.
    rewrite (Znth_indep rows (x + 1) nil __default__List_Z) by lia.
    apply PreH17; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_update_129
    rows n_pre x y 1 min v ltac:(lia) PreH20 Hdir ltac:(lia) Hv)
    as Hchecked.
  rewrite (Znth_indep rows (x + 1) nil __default__List_Z) in * by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre (x + 1) n_pre row_ptr rows
    (Znth (x + 1) rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth (x + 1) rows __default__List_Z))
    (Znth (x + 1) rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth (x + 1) rows __default__List_Z))
      (Znth (x + 1) rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_13_1 : minPath_entail_wit_13_1.
Proof.
  pre_process_default.
  assert (Habsent : forall v, ~ dir_neighbor_value_129 rows n_pre x y 1 v).
  {
    intros v Hdir.
    unfold dir_neighbor_value_129 in Hdir.
    repeat
      match goal with
      | H : _ \/ _ |- _ => destruct H as [H | H]
      | H : _ /\ _ |- _ => destruct H as [? H]
      end; lia.
  }
  pose proof (checked_neighbor_min_step_absent_129
    rows n_pre x y 1 min ltac:(lia) PreH16 Habsent) as Hchecked.
  pose proof PreH15 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre x n_pre rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
        (Znth x rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed. 

Lemma proof_of_minPath_entail_wit_13_2 : minPath_entail_wit_13_2.
Proof.
  pre_process_default.
  pose proof PreH14 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre x n_pre rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
        (Znth x rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed. 

Lemma proof_of_minPath_entail_wit_14_1_split_goal_1 : minPath_entail_wit_14_1_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_14_1_split_goal_2 : minPath_entail_wit_14_1_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_14_1_split_goal_spatial : minPath_entail_wit_14_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_14_1 : minPath_entail_wit_14_1.
Proof.
  pre_process_default.
  set (v := Znth (y - 1) (Znth x rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 2 v).
  {
    unfold v, dir_neighbor_value_129.
    right; right; left; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_keep_129
    rows n_pre x y 2 min v ltac:(lia) PreH20 Hdir ltac:(lia))
    as Hchecked.
  rewrite (Znth_indep rows x nil __default__List_Z) by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre x n_pre row_ptr rows
    (Znth x rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth x rows __default__List_Z))
    (Znth x rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_14_2_split_goal_1 : minPath_entail_wit_14_2_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_14_2_split_goal_2 : minPath_entail_wit_14_2_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_14_2_split_goal_3 : minPath_entail_wit_14_2_split_goal_3.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_14_2_split_goal_spatial : minPath_entail_wit_14_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_14_2 : minPath_entail_wit_14_2.
Proof.
  pre_process_default.
  set (v := Znth (y - 1) (Znth x rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 2 v).
  {
    unfold v, dir_neighbor_value_129.
    right; right; left; repeat split; lia.
  }
  assert (Hv : 1 <= v <= n_pre * n_pre).
  {
    unfold v.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    apply PreH17; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_update_129
    rows n_pre x y 2 min v ltac:(lia) PreH20 Hdir ltac:(lia) Hv)
    as Hchecked.
  rewrite (Znth_indep rows x nil __default__List_Z) in * by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre x n_pre row_ptr rows
    (Znth x rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth x rows __default__List_Z))
    (Znth x rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_15_1 : minPath_entail_wit_15_1.
Proof.
  pre_process_default.
  assert (Habsent1 : forall v, ~ dir_neighbor_value_129 rows n_pre x y 1 v).
  {
    intros v Hdir; unfold dir_neighbor_value_129 in Hdir.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    | H : _ /\ _ |- _ => destruct H as [? H]
    end; lia.
  }
  pose proof (checked_neighbor_min_step_absent_129
    rows n_pre x y 1 min ltac:(lia) PreH17 Habsent1) as Hchecked2.
  assert (Habsent2 : forall v, ~ dir_neighbor_value_129 rows n_pre x y 2 v).
  {
    intros v Hdir; unfold dir_neighbor_value_129 in Hdir.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    | H : _ /\ _ |- _ => destruct H as [? H]
    end; lia.
  }
  pose proof (checked_neighbor_min_step_absent_129
    rows n_pre x y 2 min ltac:(lia) Hchecked2 Habsent2) as Hchecked.
  pose proof PreH16 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i grid_pre x n_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
        (Znth x rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed. 

Lemma proof_of_minPath_entail_wit_15_2 : minPath_entail_wit_15_2.
Proof.
  pre_process_default.
  assert (Habsent : forall v, ~ dir_neighbor_value_129 rows n_pre x y 2 v).
  {
    intros v Hdir; unfold dir_neighbor_value_129 in Hdir.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    | H : _ /\ _ |- _ => destruct H as [? H]
    end; lia.
  }
  pose proof (checked_neighbor_min_step_absent_129
    rows n_pre x y 2 min ltac:(lia) PreH16 Habsent) as Hchecked.
  pose proof PreH15 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i grid_pre x n_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
        (Znth x rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed. 

Lemma proof_of_minPath_entail_wit_15_3 : minPath_entail_wit_15_3.
Proof.
  pre_process_default.
  pose proof PreH14 as Hfind.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [[Hx0 Hxn] [[Hy0 Hyn] _]]]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i grid_pre x n_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
        (Znth x rows __default__List_Z)).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
Qed. 

Lemma proof_of_minPath_entail_wit_16_1_split_goal_1 : minPath_entail_wit_16_1_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_16_1_split_goal_2 : minPath_entail_wit_16_1_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_16_1_split_goal_spatial : minPath_entail_wit_16_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_16_1 : minPath_entail_wit_16_1.
Proof.
  pre_process_default.
  set (v := Znth (y + 1) (Znth x rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 3 v).
  {
    unfold v, dir_neighbor_value_129.
    right; right; right; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_keep_129
    rows n_pre x y 3 min v ltac:(lia) PreH20 Hdir ltac:(lia))
    as Hchecked.
  rewrite (Znth_indep rows x nil __default__List_Z) by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre x n_pre row_ptr rows
    (Znth x rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth x rows __default__List_Z))
    (Znth x rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_16_2_split_goal_1 : minPath_entail_wit_16_2_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_16_2_split_goal_2 : minPath_entail_wit_16_2_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_16_2_split_goal_3 : minPath_entail_wit_16_2_split_goal_3.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_16_2_split_goal_spatial : minPath_entail_wit_16_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_16_2 : minPath_entail_wit_16_2.
Proof.
  pre_process_default.
  set (v := Znth (y + 1) (Znth x rows nil) 0).
  assert (Hdir : dir_neighbor_value_129 rows n_pre x y 3 v).
  {
    unfold v, dir_neighbor_value_129.
    right; right; right; repeat split; lia.
  }
  assert (Hv : 1 <= v <= n_pre * n_pre).
  {
    unfold v.
    rewrite (Znth_indep rows x nil __default__List_Z) by lia.
    apply PreH17; repeat split; lia.
  }
  pose proof (checked_neighbor_min_step_update_129
    rows n_pre x y 3 min v ltac:(lia) PreH20 Hdir ltac:(lia) Hv)
    as Hchecked.
  rewrite (Znth_indep rows x nil __default__List_Z) in * by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre x n_pre row_ptr rows
    (Znth x rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth x rows __default__List_Z))
    (Znth x rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth x rows __default__List_Z))
      (Znth x rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_17_1_split_goal_1 : minPath_entail_wit_17_1_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_17_1_split_goal_2 : minPath_entail_wit_17_1_split_goal_2.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_17_1_split_goal_spatial : minPath_entail_wit_17_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_17_1 : minPath_entail_wit_17_1.
Proof.
  pre_process_default.
  assert (Habsent : forall v, ~ dir_neighbor_value_129 rows n_pre x y 3 v).
  {
    intros v Hdir; unfold dir_neighbor_value_129 in Hdir.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    | H : _ /\ _ |- _ => destruct H as [? H]
    end; lia.
  }
  pose proof (checked_neighbor_min_step_absent_129
    rows n_pre x y 3 min ltac:(lia) PreH15 Habsent) as Hchecked.
  assert (Hrow_nil :
    forall r, 0 <= r < n_pre -> Zlength (Znth r rows nil) = n_pre).
  {
    intros r Hr.
    rewrite (Znth_indep rows r nil __default__List_Z) by lia.
    apply PreH12; lia.
  }
  assert (Hrange_nil :
    forall r c, 0 <= r < n_pre -> 0 <= c < n_pre ->
      1 <= Znth c (Znth r rows nil) 0 <= n_pre * n_pre).
  {
    intros r c Hr Hc.
    rewrite (Znth_indep rows r nil __default__List_Z) by lia.
    apply PreH13; lia.
  }
  pose proof (checked_neighbor_min_to_spec_129
    rows n_pre x y min PreH2 PreH10 Hrow_nil Hrange_nil PreH14 Hchecked)
    as Hspec.
  unfold min_neighbor_state_129.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_17_2_split_goal_1 : minPath_entail_wit_17_2_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_17_2_split_goal_spatial : minPath_entail_wit_17_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_17_2 : minPath_entail_wit_17_2.
Proof.
  pre_process_default.
  assert (Hrow_nil :
    forall r, 0 <= r < n_pre -> Zlength (Znth r rows nil) = n_pre).
  {
    intros r Hr.
    rewrite (Znth_indep rows r nil __default__List_Z) by lia.
    apply PreH11; lia.
  }
  assert (Hrange_nil :
    forall r c, 0 <= r < n_pre -> 0 <= c < n_pre ->
      1 <= Znth c (Znth r rows nil) 0 <= n_pre * n_pre).
  {
    intros r c Hr Hc.
    rewrite (Znth_indep rows r nil __default__List_Z) by lia.
    apply PreH12; lia.
  }
  pose proof (checked_neighbor_min_to_spec_129
    rows n_pre x y min PreH1 PreH9 Hrow_nil Hrange_nil PreH13 PreH14)
    as Hspec.
  unfold min_neighbor_state_129.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_18_split_goal_1 : minPath_entail_wit_18_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_18 : minPath_entail_wit_18.
Proof.
  pre_process_default.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  unfold output_prefix_129.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_19_1_split_goal_1 : minPath_entail_wit_19_1_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_19_1 : minPath_entail_wit_19_1.
Proof.
  pre_process_default.
  Exists (output_l_2 ++ 1 :: nil).
  assert (Hval : 1 = output_value_129 t min).
  {
    assert (Hmod : t mod 2 = 0).
    {
      rewrite <- Z.rem_mod_nonneg; lia.
    }
    unfold output_value_129.
    rewrite Zeven_mod.
    rewrite Hmod.
    reflexivity.
  }
  pose proof (output_prefix_snoc_129
    k_pre min t output_l_2 1 PreH14 ltac:(lia) Hval) as Hprefix.
  entailer!.
Qed. 

Lemma proof_of_minPath_entail_wit_19_2_split_goal_1 : minPath_entail_wit_19_2_split_goal_1.
Proof. Abort.

Lemma proof_of_minPath_entail_wit_19_2 : minPath_entail_wit_19_2.
Proof.
  pre_process_default.
  Exists (output_l_2 ++ min :: nil).
  assert (Hmod : t mod 2 = 1).
  {
    pose proof (Z.mod_pos_bound t 2 ltac:(lia)).
    assert (t mod 2 <> 0).
    {
      intro Hzero.
      apply PreH1.
      rewrite Z.rem_mod_nonneg by lia.
      exact Hzero.
    }
    lia.
  }
  assert (Hval : min = output_value_129 t min).
  {
    unfold output_value_129.
    rewrite Zeven_mod.
    rewrite Hmod.
    reflexivity.
  }
  pose proof (output_prefix_snoc_129
    k_pre min t output_l_2 min PreH14 ltac:(lia) Hval) as Hprefix.
  entailer!.
Qed. 

Lemma proof_of_minPath_return_wit_1 : minPath_return_wit_1.
Proof.
  pre_process_default.
  - assert (Ht_eq : t = k_pre) by lia.
    subst t.
    pose proof (min_neighbor_output_spec_129
      rows n_pre x y min k_pre output_l_2 ltac:(lia) PreH12 PreH13)
      as Hspec.
    Exists data_2 output_l_2 min.
    rewrite (IntArray.undef_seg_empty data_2 k_pre).
    sep_apply (IntArray.seg_to_full data_2 0 k_pre output_l_2).
    replace (data_2 + 0 * sizeof(INT)) with data_2 by lia.
    replace (k_pre - 0) with k_pre by lia.
    entailer!.
Qed. 
