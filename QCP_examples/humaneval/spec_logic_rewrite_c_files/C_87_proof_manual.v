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
From SimpleC.EE Require Import C_87_goal.
From SimpleC.EE Require Import C_87_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_87.
Local Open Scope sac.

Lemma proof_of_get_row_entail_wit_1_split_goal_1 : get_row_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_1 : get_row_entail_wit_1.
Proof.
  pre_process_default; try entailer!.
  apply count_outer_0_87.
Qed.

Lemma proof_of_get_row_entail_wit_2_split_goal_1 : get_row_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_2_split_goal_2 : get_row_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_2_split_goal_3 : get_row_entail_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_2_split_goal_spatial : get_row_entail_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_2 : get_row_entail_wit_2.
Proof.
  pre_process_default.
  - sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
      lst_pre i rows_pre input_l).
    + dump_pre_spatial; lia.
    + Intros row_ptr.
    pose proof (row_sizes_87_Znth input_l i 0 ltac:(lia)) as Hsize.
    pose proof (row_length_safe_87 input_l i PreH6 ltac:(lia)) as Hsafe.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i input_l nil))
      (Znth i input_l nil)) with
      (IntArray.full row_ptr (Zlength (Znth i input_l nil))
        (Znth i input_l nil)).
    rewrite Hsize.
    entailer!; rewrite sizeof_ptr; cancel.
Qed.

Lemma proof_of_get_row_entail_wit_3_split_goal_1 : get_row_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_3 : get_row_entail_wit_3.
Proof.
  pre_process_default; try entailer!.
  - Exists row_ptr_2; entailer!.
    rewrite PreH7.
    apply count_outer_to_inner_87; try lia.
    exact PreH6.
Qed.

Lemma proof_of_get_row_entail_wit_4_1_split_goal_1 : get_row_entail_wit_4_1_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_4_1_split_goal_2 : get_row_entail_wit_4_1_split_goal_2.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_4_1 : get_row_entail_wit_4_1.
Proof.
  pre_process_default; try entailer!.
  - pose proof (coord_hits_current_87 input_l x_pre i j ltac:(lia)
      ltac:(rewrite <- PreH11; lia) PreH1) as Hhit.
    pose proof (proj1 (proj2 PreH9) x_pre i j count PreH10) as Hbound.
    Exists row_ptr_2; entailer!.
    apply count_inner_hit_87; assumption.
Qed.

Lemma proof_of_get_row_entail_wit_4_2_split_goal_1 : get_row_entail_wit_4_2_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_4_2 : get_row_entail_wit_4_2.
Proof.
  pre_process_default; try entailer!.
  - assert (Hmiss : ~ coord_hits input_l x_pre (i, j)).
    { intro Hhit; apply PreH1.
      apply coord_hits_current_inv_87.
      - lia.
      - rewrite <- PreH11; lia.
      - exact Hhit. }
    Exists row_ptr_2; entailer!.
    apply count_inner_miss_87; assumption.
Qed.

Lemma proof_of_get_row_entail_wit_5_split_goal_1 : get_row_entail_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_5_split_goal_spatial : get_row_entail_wit_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_5 : get_row_entail_wit_5.
Proof.
  pre_process_default.
  - assert (j = -1) by lia; subst j.
    pose proof (IntPtrArray2.missing_i_merge_to_full
      lst_pre i rows_pre row_ptr input_l (Znth i input_l nil)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i input_l nil)) (Znth i input_l nil)) with
      (IntArray.full row_ptr (Zlength (Znth i input_l nil))
        (Znth i input_l nil)) in Hmerge.
    rewrite PreH10, sizeof_ptr.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    entailer!.
    apply count_inner_to_outer_87; exact PreH9.
Qed.

Lemma proof_of_get_row_entail_wit_6 : get_row_entail_wit_6.
Proof.
  pre_process_default.
  assert (i = rows_pre) by lia; subst i.
  sep_apply IntArray.undef_full_to_undef_seg.
  Exists (@nil (Z * Z)).
  rewrite IntArray.seg_empty.
  entailer!.
  apply fill_outer_0_87.
Qed.

Lemma proof_of_get_row_entail_wit_7 : get_row_entail_wit_7.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    lst_pre i rows_pre input_l).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    pose proof (row_sizes_87_Znth input_l i 0 ltac:(lia)) as Hsize.
    pose proof (row_length_safe_87 input_l i PreH6 ltac:(lia)) as Hsafe.
    Exists row_ptr coords_2.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i input_l nil)) (Znth i input_l nil)) with
      (IntArray.full row_ptr (Zlength (Znth i input_l nil))
        (Znth i input_l nil)).
    rewrite Hsize.
    entailer!; rewrite sizeof_ptr; cancel.
Qed.

Lemma proof_of_get_row_entail_wit_8 : get_row_entail_wit_8.
Proof.
  pre_process_default.
  Exists row_ptr_2 coords_2.
  entailer!.
  rewrite PreH8.
  apply fill_outer_to_inner_87; try lia.
  exact PreH7.
Qed.

Lemma proof_of_get_row_entail_wit_9 : get_row_entail_wit_9.
Proof.
  pre_process_default.
  pose proof (coord_hits_current_87 input_l x_pre i j ltac:(lia)
    ltac:(rewrite <- PreH12; lia) PreH1) as Hhit.
  pose proof (fill_inner_room_87 input_l x_pre i j count coords_2
    ltac:(lia) Hhit ltac:(rewrite <- PreH7; exact PreH10) PreH11) as Hroom.
  Exists row_ptr_2 coords_2.
  entailer!.
Qed.

Lemma proof_of_get_row_entail_wit_10_1 : get_row_entail_wit_10_1.
Proof.
  pre_process_default.
  pose proof (coord_hits_current_87 input_l x_pre i j ltac:(lia)
    ltac:(rewrite <- PreH11; lia) PreH10) as Hhit.
  Exists row_ptr_2 (coords_2 ++ cons (i, j) nil).
  rewrite coords_flat_87_app_single.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!.
  - replace (2 * (size + 1)) with (2 * size + 1 + 1) by lia.
    replace (coords_flat_87 coords_2 ++ i :: j :: nil) with
      ((coords_flat_87 coords_2 +:: i) +:: j)
      by (rewrite <- app_assoc; reflexivity).
    cancel.
  - apply fill_inner_hit_87; assumption.
Qed.

Lemma proof_of_get_row_entail_wit_10_2 : get_row_entail_wit_10_2.
Proof.
  pre_process_default.
  assert (Hmiss : ~ coord_hits input_l x_pre (i, j)).
  { intro Hhit; apply PreH1.
    apply coord_hits_current_inv_87.
    - lia.
    - rewrite <- PreH12; lia.
    - exact Hhit. }
  Exists row_ptr_2 coords_2.
  entailer!.
  apply fill_inner_miss_87; assumption.
Qed.

Lemma proof_of_get_row_entail_wit_11 : get_row_entail_wit_11.
Proof.
  pre_process_default.
  assert (j = -1) by lia; subst j.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    lst_pre i rows_pre row_ptr input_l (Znth i input_l nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth i input_l nil)) (Znth i input_l nil)) with
    (IntArray.full row_ptr (Zlength (Znth i input_l nil))
      (Znth i input_l nil)) in Hmerge.
  rewrite PreH11, sizeof_ptr.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  Exists coords_2.
  entailer!.
  apply fill_inner_to_outer_87; exact PreH10.
Qed.

Lemma proof_of_get_row_entail_wit_12 : get_row_entail_wit_12.
Proof.
  pre_process_default.
  assert (i = rows_pre) by lia; subst i.
  pose proof (count_fill_length_87 input_l x_pre count coords_2
    ltac:(rewrite <- PreH4; exact PreH7)
    ltac:(rewrite <- PreH4; exact PreH8)) as Hlen.
  pose proof (fill_finished_87 input_l x_pre coords_2
    ltac:(rewrite <- PreH4; exact PreH8)) as Hfinished.
  assert (size = count) by lia; subst count.
  replace (2 * Zlength coords_2) with (2 * size) by lia.
  rewrite IntArray.undef_seg_empty.
  sep_apply IntArray.seg_to_full.
  Exists coords_2.
  entailer!.
  rewrite sizeof_int.
  replace (data + 0 * 4) with data by lia.
  replace (2 * size - 0) with (2 * size) by lia.
  cancel.
Qed.

Lemma proof_of_get_row_return_wit_1 : get_row_return_wit_1.
Proof.
  pre_process_default.
  Exists coords_2 (coords_flat_87 coords_2) size_2 data_2.
  pose proof (Zlength_coords_flat_87 coords_2) as Hflat.
  entailer!.
Qed.
