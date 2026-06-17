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
From SimpleC.EE Require Import C_115_goal.
From SimpleC.EE Require Import C_115_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_115.
Local Open Scope sac.

Ltac c115_default_rows :=
  repeat match goal with
  | Hlen : forall r : Z, _ -> Zlength (Znth r ?rs ?d) = ?m
    |- context[Zlength (Znth ?r ?rs ?d2)] =>
      rewrite (Znth_indep rs r d2 d) by lia
  | Hcell : forall r c : Z, _ -> 0 <= Znth c (Znth r ?rs ?d) 0 <= 1
    |- context[Znth ?c (Znth ?r ?rs nil) 0] =>
      rewrite (Znth_indep rs r nil d) by lia
  end.

Ltac c115_cell_bound :=
  match goal with
  | Hcell : forall r c : Z, _ -> _ |- context[Znth ?c (Znth ?r ?rs ?d) 0] =>
      pose proof (Hcell r c ltac:(repeat split; lia))
  end.

Ltac c115_quot_bound :=
  match goal with
  | |- context[Z.quot (?s - 1) ?cap] =>
      assert (0 <= Z.quot (s - 1) cap <= s - 1) by
        (split; [apply Z.quot_pos; lia | apply Z.quot_le_upper_bound; nia])
  end.

Ltac c115_basic :=
  pre_process_default; try entailer!;
  try c115_default_rows; try c115_cell_bound; try c115_quot_bound;
  try lia; try nia.

Lemma proof_of_max_fill_safety_wit_6_split_goal_1 : max_fill_safety_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_safety_wit_6_split_goal_2 : max_fill_safety_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_safety_wit_6 : max_fill_safety_wit_6.
Proof.
  c115_basic.
Qed.

Lemma proof_of_max_fill_safety_wit_8_split_goal_1 : max_fill_safety_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_safety_wit_8_split_goal_2 : max_fill_safety_wit_8_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_safety_wit_8 : max_fill_safety_wit_8.
Proof.
  c115_basic.
Qed.

Lemma proof_of_max_fill_safety_wit_9_split_goal_1 : max_fill_safety_wit_9_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_safety_wit_9_split_goal_2 : max_fill_safety_wit_9_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_safety_wit_9 : max_fill_safety_wit_9.
Proof.
  c115_basic.
Qed.

Lemma proof_of_max_fill_entail_wit_1_split_goal_1 : max_fill_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_1_split_goal_2 : max_fill_entail_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_1 : max_fill_entail_wit_1.
Proof.
  pre_process_default; try entailer!.
Qed.

Lemma proof_of_max_fill_entail_wit_2_split_goal_1 : max_fill_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_2_split_goal_2 : max_fill_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_2_split_goal_3 : max_fill_entail_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_2_split_goal_spatial : max_fill_entail_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_2 : max_fill_entail_wit_2.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre i grid_rows_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite row_sum_prefix_z_0.
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

Lemma proof_of_max_fill_entail_wit_3_split_goal_1 : max_fill_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_3 : max_fill_entail_wit_3.
Proof.
  pre_process_default.
  Exists row_ptr_2.
  entailer!.
Qed.

Lemma proof_of_max_fill_entail_wit_4_split_goal_1 : max_fill_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_4_split_goal_2 : max_fill_entail_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_4_split_goal_3 : max_fill_entail_wit_4_split_goal_3.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_4 : max_fill_entail_wit_4.
Proof.
  pre_process_default.
  rewrite (Znth_indep rows i nil __default__List_Z) by lia.
  rewrite (Znth_indep rows i nil __default__List_Z) in PreH17 by lia.
  pose proof (PreH15 i j ltac:(repeat split; lia)).
  assert (Hrow_len : Zlength (Znth i rows __default__List_Z) = grid_cols_pre)
    by (apply PreH14; lia).
  rewrite (row_sum_prefix_z_step (Znth i rows __default__List_Z) j)
    by (rewrite Hrow_len; lia).
  Exists row_ptr_2.
  entailer!.
Qed.

Lemma proof_of_max_fill_entail_wit_5_split_goal_1 : max_fill_entail_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_5_split_goal_2 : max_fill_entail_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_5_split_goal_spatial : max_fill_entail_wit_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_5 : max_fill_entail_wit_5.
Proof.
  pre_process_default.
  assert (j = grid_cols_pre) by lia; subst j.
  rewrite (Znth_indep rows i nil __default__List_Z) by lia.
  rewrite (Znth_indep rows i nil __default__List_Z) in PreH17 by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre i grid_rows_pre row_ptr rows
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

Lemma proof_of_max_fill_entail_wit_6_1_split_goal_1 : max_fill_entail_wit_6_1_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_6_1_split_goal_2 : max_fill_entail_wit_6_1_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_6_1_split_goal_3 : max_fill_entail_wit_6_1_split_goal_3.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_6_1_split_goal_4 : max_fill_entail_wit_6_1_split_goal_4.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_6_1 : max_fill_entail_wit_6_1.
Proof.
  pre_process_default; try entailer!.
  - pose proof (trips_prefix_z_nonneg_bound_step
      i grid_cols_pre capacity_pre out sum ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
    replace (Z.eqb sum 0) with false in Hbound
      by (symmetry; apply Z.eqb_neq; lia).
    destruct Hbound as [_ Hbound_hi]. exact Hbound_hi.
  - pose proof (trips_prefix_z_nonneg_bound_step
      i grid_cols_pre capacity_pre out sum ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
    replace (Z.eqb sum 0) with false in Hbound
      by (symmetry; apply Z.eqb_neq; lia).
    destruct Hbound as [Hbound_lo _]. exact Hbound_lo.
  - assert (Hstep :
      trips_prefix_z rows (i + 1) capacity_pre =
      trips_prefix_z rows i capacity_pre +
      (if Z.eqb sum 0 then 0 else Z.quot (sum - 1) capacity_pre + 1)).
    { apply trips_prefix_z_step_from_sum with (n := grid_cols_pre); try lia. }
    rewrite Hstep.
    replace (Z.eqb sum 0) with false by (symmetry; apply Z.eqb_neq; lia).
    lia.
Qed.

Lemma proof_of_max_fill_entail_wit_6_2_split_goal_1 : max_fill_entail_wit_6_2_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_6_2_split_goal_2 : max_fill_entail_wit_6_2_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_6_2_split_goal_3 : max_fill_entail_wit_6_2_split_goal_3.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_6_2 : max_fill_entail_wit_6_2.
Proof.
  pre_process_default; try entailer!.
  assert (sum = 0) by lia; subst sum.
  assert (Hstep :
    trips_prefix_z rows (i + 1) capacity_pre =
    trips_prefix_z rows i capacity_pre +
    (if Z.eqb 0 0 then 0 else Z.quot (0 - 1) capacity_pre + 1)).
  { apply trips_prefix_z_step_from_sum with (n := grid_cols_pre); try lia. }
  rewrite Hstep.
  simpl.
  entailer!.
Qed.

Lemma proof_of_max_fill_return_wit_1_split_goal_1 : max_fill_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_return_wit_1 : max_fill_return_wit_1.
Proof.
  pre_process_default; try entailer!.
  apply problem_115_spec_z_of_trips_prefix; try lia.
  - exact PreH11.
  - rewrite PreH14.
    replace i with grid_rows_pre by lia.
    rewrite <- PreH10.
    reflexivity.
  - intros r c Hr Hc.
    assert (Hr_grid : 0 <= r < grid_rows_pre) by lia.
    assert (Hrow_eq : Znth r rows nil = Znth r rows __default__List_Z).
    { apply Znth_indep. lia. }
    assert (Hrow_len : Zlength (Znth r rows __default__List_Z) = grid_cols_pre).
    { apply PreH12. exact Hr_grid. }
    rewrite Hrow_eq in Hc.
    pose proof (PreH13 r c ltac:(repeat split; try lia)) as Hcell.
    rewrite Hrow_eq.
    tauto.
Qed.
