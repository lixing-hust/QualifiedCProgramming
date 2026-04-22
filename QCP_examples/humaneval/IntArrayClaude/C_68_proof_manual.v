Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_68_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_68.
Local Open Scope sac.

Lemma proof_of_pluck_entail_wit_1 : pluck_entail_wit_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  Exists (@nil Z) 0.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_prefix_result_0.
Qed.

Lemma proof_of_pluck_entail_wit_2_1 : pluck_entail_wit_2_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  Exists (Znth i input_l 0) i (cons (Znth i input_l 0) (cons i nil)) 2.
  sep_apply (IntArray.seg_single data 1 i).
  sep_apply (IntArray.seg_single data 0 (Znth i input_l 0)).
  sep_apply (IntArray.seg_merge_to_full data 0 1 2
               (Znth i input_l 0 :: nil) (i :: nil)); [ | lia].
  replace (data + 0 * sizeof (INT)) with data by lia.
  replace (2 - 0) with 2 by lia.
  simpl.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_loop_state_update_empty with (output := output_l_2); auto; lia.
Qed.

Lemma proof_of_pluck_entail_wit_2_2 : pluck_entail_wit_2_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  Exists (Znth i input_l 0) i
         (replace_Znth 1 i (replace_Znth 0 (Znth i input_l 0) output_l_2)) 2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - rewrite replace_Znth_two by lia. reflexivity.
  - rewrite replace_Znth_two by lia.
    apply pluck_loop_state_update_less with
      (output := output_l_2) (value := value_2) (index := index_2);
      auto; lia.
  - rewrite replace_Znth_two by lia. reflexivity.
Qed.

Lemma proof_of_pluck_entail_wit_2_3 : pluck_entail_wit_2_3.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  Exists output_l_2 0.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_loop_state_skip_odd; auto; lia.
Qed.

Lemma proof_of_pluck_entail_wit_2_4 : pluck_entail_wit_2_4.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  Exists value_2 index_2 output_l_2 2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_loop_state_skip_odd; auto; lia.
Qed.

Lemma proof_of_pluck_entail_wit_2_5 : pluck_entail_wit_2_5.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  Exists value_2 index_2 output_l_2 2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_loop_state_skip_ge with
    (value := value_2) (index := index_2); auto; lia.
Qed.

Lemma proof_of_pluck_return_wit_1 : pluck_return_wit_1.
Proof.
  pre_process.
  subst output_l_2 output_size_2.
  rewrite <- derivable1_orp_intros1.
  Exists data_2 (@nil Z) 0.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_loop_state_full_spec with (i := i); auto; lia.
Qed.

Lemma proof_of_pluck_return_wit_2 : pluck_return_wit_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  Exists data_2 output_l_2 2.
  sep_apply (IntArray.full_to_seg data_2 2 output_l_2).
  rewrite (IntArray.undef_seg_empty data_2 2).
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_loop_state_full_spec with (i := i); auto; lia.
Qed.
