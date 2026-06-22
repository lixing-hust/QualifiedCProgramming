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

Ltac c87_basic :=
  pre_process_default;
  try rewrite total_cells_prefix_87_0 in *;
  try match goal with
  | H : forall r : Z, 0 <= r < ?rows -> 0 <= Znth r ?sizes 0 <= 100,
    Hlo : 0 <= ?i, Hhi : ?i < ?rows |- _ =>
      pose proof (H i ltac:(lia))
  end;
  try entailer!;
  try lia; try nia.

Lemma proof_of_get_row_safety_wit_3_split_goal_1 : get_row_safety_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_safety_wit_3_split_goal_2 : get_row_safety_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_get_row_safety_wit_3 : get_row_safety_wit_3.
Proof.
  pre_process_default.
  pose proof PreH8 as Hmatch_all.
  destruct Hmatch_all as [_ Hsizes].
  pose proof (Hsizes i ltac:(lia)) as Hsize_i.
  rewrite Hsize_i.
  subst total.
  rewrite <- total_cells_prefix_87_step by lia.
  pose proof (total_cells_prefix_87_nonneg_monotone matrix (i + 1) ltac:(lia)).
  rewrite PreH6 in H.
  entailer!.
Qed. 

Lemma proof_of_get_row_safety_wit_13_split_goal_1 : get_row_safety_wit_13_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_safety_wit_13_split_goal_2 : get_row_safety_wit_13_split_goal_2.
Proof. Abort.

Lemma proof_of_get_row_safety_wit_13 : get_row_safety_wit_13.
Proof.
  c87_basic.
Qed. 

Lemma proof_of_get_row_entail_wit_1_split_goal_1 : get_row_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_1_split_goal_2 : get_row_entail_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_1 : get_row_entail_wit_1.
Proof.
  c87_basic.
Qed. 

Lemma proof_of_get_row_entail_wit_2_split_goal_1 : get_row_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_2_split_goal_2 : get_row_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_2_split_goal_3 : get_row_entail_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_2 : get_row_entail_wit_2.
Proof.
  pre_process_default.
  pose proof PreH8 as Hmatch_all.
  destruct Hmatch_all as [_ Hsizes].
  pose proof (Hsizes i ltac:(lia)) as Hsize_i.
  rewrite Hsize_i.
  subst total.
  rewrite <- total_cells_prefix_87_step by lia.
  pose proof (total_cells_prefix_87_nonneg_monotone matrix (i + 1) ltac:(lia)).
  rewrite PreH6 in H.
  entailer!.
Qed. 

Lemma proof_of_get_row_entail_wit_3_split_goal_1 : get_row_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_3_split_goal_2 : get_row_entail_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_3_split_goal_3 : get_row_entail_wit_3_split_goal_3.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_3_split_goal_4 : get_row_entail_wit_3_split_goal_4.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_3 : get_row_entail_wit_3.
Proof.
  pre_process_default.
  assert (i = rows_pre) by lia; subst i.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  unfold prefix_state_87; simpl.
  entailer!.
Qed. 

Lemma proof_of_get_row_entail_wit_4_split_goal_1 : get_row_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_4_split_goal_2 : get_row_entail_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_4_split_goal_3 : get_row_entail_wit_4_split_goal_3.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_4_split_goal_spatial : get_row_entail_wit_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_4 : get_row_entail_wit_4.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    lst_pre i rows_pre matrix).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr output_l_2.
    rewrite (Znth_indep matrix i nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i matrix __default__List_Z))
      (Znth i matrix __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth i matrix __default__List_Z))
        (Znth i matrix __default__List_Z)).
    pose proof PreH13 as Hmatch.
    assert (Zlength (Znth i matrix nil) = Znth i sizes 0).
    {
      destruct Hmatch as [_ Hsizes].
      symmetry. apply Hsizes. lia.
    }
    pose proof (scan_state_87_start matrix sizes x_pre i output_l_2
      PreH13 ltac:(rewrite PreH11; lia) PreH15).
    entailer!.
    rewrite sizeof_ptr.
    cancel.
    rewrite (Znth_indep matrix i __default__List_Z nil) by lia.
    exact H.
Qed. 

Lemma proof_of_get_row_entail_wit_5_split_goal_1 : get_row_entail_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_5_split_goal_2 : get_row_entail_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_5 : get_row_entail_wit_5.
Proof.
  pre_process_default.
  Exists row_ptr_2 output_l_2.
  pose proof (PreH21 i ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_get_row_entail_wit_6_split_goal_1 : get_row_entail_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_6_split_goal_2 : get_row_entail_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_6_split_goal_3 : get_row_entail_wit_6_split_goal_3.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_6 : get_row_entail_wit_6.
Proof.
  pre_process_default.
  Exists row_ptr_2 output_l_2.
  pose proof (scan_state_87_match_room matrix x_pre i j output_l_2
    ltac:(rewrite PreH14; lia)
    ltac:(rewrite PreH24; lia)
    PreH1
    PreH18) as Hroom.
  rewrite PreH14 in Hroom.
  rewrite <- PreH12 in Hroom.
  rewrite <- PreH19 in Hroom.
  entailer!.
Qed. 

Lemma proof_of_get_row_entail_wit_7_1 : get_row_entail_wit_7_1.
Proof.
  pre_process_default.
  Exists row_ptr_2 (app output_l_2 (cons i (cons j nil))).
  pose proof (scan_state_87_match_step matrix x_pre i j output_l_2
    ltac:(rewrite PreH18; lia)
    ltac:(rewrite PreH22; lia)
    ltac:(exact PreH9)
    PreH23).
  pose proof (scan_state_87_match_room matrix x_pre i j output_l_2
    ltac:(rewrite PreH18; lia)
    ltac:(rewrite PreH22; lia)
    PreH9
    PreH23) as Hroom.
  rewrite PreH18 in Hroom.
  rewrite <- PreH11 in Hroom.
  rewrite <- PreH24 in Hroom.
  rewrite Zlength_app, PreH24.
  simpl.
  entailer!.
  replace (Zlength output_l_2 + 1 + 1) with (Zlength output_l_2 + 2) by lia.
  replace ((output_l_2 +:: i) +:: j) with (output_l_2 ++ i :: j :: nil)
    by (rewrite <- app_assoc; reflexivity).
  cancel; try lia; auto.
  all: try lia; auto.
Qed. 

Lemma proof_of_get_row_entail_wit_7_2_split_goal_1 : get_row_entail_wit_7_2_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_7_2 : get_row_entail_wit_7_2.
Proof.
  pre_process_default.
  Exists row_ptr_2 output_l_2.
  pose proof (scan_state_87_nomatch_step matrix x_pre i j output_l_2
    ltac:(rewrite PreH14; lia)
    ltac:(rewrite PreH24; lia)
    PreH1
    PreH18).
  entailer!.
Qed. 

Lemma proof_of_get_row_entail_wit_8_split_goal_1 : get_row_entail_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_8_split_goal_2 : get_row_entail_wit_8_split_goal_2.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_8_split_goal_spatial : get_row_entail_wit_8_split_goal_spatial.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_8 : get_row_entail_wit_8.
Proof.
  right.
  pre_process_default.
  assert (j = -1) by lia; subst j.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    lst_pre i rows_pre row_ptr matrix (Znth i matrix nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth i matrix nil)) (Znth i matrix nil)) with
    (IntArray.full row_ptr (Zlength (Znth i matrix nil))
      (Znth i matrix nil)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
  all: try solve [exact PreH25].
  all: try solve [eapply scan_state_87_done; eauto; rewrite PreH13; lia].
  all: try solve [eapply scan_state_87_done; eauto; lia].
Qed. 

Lemma proof_of_get_row_entail_wit_9_split_goal_1 : get_row_entail_wit_9_split_goal_1.
Proof. Abort.

Lemma proof_of_get_row_entail_wit_9 : get_row_entail_wit_9.
Proof.
  right.
  c87_basic.
Qed. 

Lemma proof_of_get_row_return_wit_1 : get_row_return_wit_1.
Proof.
  right.
  pre_process_default.
  assert (i = rows_pre) by lia; subst i.
  Exists output_l_2.
  rewrite <- PreH8.
  entailer!.
  apply (prefix_state_87_complete matrix x_pre rows_pre output_l_2).
  - symmetry. exact PreH11.
  - exact PreH15.
Qed. 
