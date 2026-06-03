Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_154_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_154.
Local Open Scope sac.

Ltac c154_prep :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Lemma proof_of_rotation_match_at_safety_wit_3 : rotation_match_at_safety_wit_3.
Proof. unfold rotation_match_at_safety_wit_3; intros; c154_prep; entailer!; change (Z.quot 2147483647 2) with 1073741823 in *; lia. Qed. 

Lemma proof_of_rotation_match_at_safety_wit_4 : rotation_match_at_safety_wit_4.
Proof. unfold rotation_match_at_safety_wit_4; intros; c154_prep; entailer!; change (Z.quot 2147483647 2) with 1073741823 in *; lia. Qed. 

Lemma proof_of_rotation_match_at_entail_wit_1 : rotation_match_at_entail_wit_1.
Proof.
  unfold rotation_match_at_entail_wit_1; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  apply rotation_match_progress_init.
Qed. 

Lemma proof_of_rotation_match_at_entail_wit_2_1 : rotation_match_at_entail_wit_2_1.
Proof.
  unfold rotation_match_at_entail_wit_2_1; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  unfold rot_index_z.
  destruct (Z.ltb_spec (shift_pre + j) (Zlength b_l)) as [Hlt | Hge].
  - lia.
  - entailer!.
Qed. 

Lemma proof_of_rotation_match_at_entail_wit_2_2 : rotation_match_at_entail_wit_2_2.
Proof.
  unfold rotation_match_at_entail_wit_2_2; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  unfold rot_index_z.
  destruct (Z.ltb_spec (shift_pre + j) (Zlength b_l)) as [Hlt | Hge].
  - lia.
  - entailer!.
Qed. 

Lemma proof_of_rotation_match_at_entail_wit_2_3 : rotation_match_at_entail_wit_2_3.
Proof.
  unfold rotation_match_at_entail_wit_2_3; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  unfold rot_index_z.
  destruct (Z.ltb_spec (shift_pre + j) (Zlength b_l)) as [Hlt | Hge].
  - entailer!.
  - lia.
Qed. 

Lemma proof_of_rotation_match_at_entail_wit_2_4 : rotation_match_at_entail_wit_2_4.
Proof.
  unfold rotation_match_at_entail_wit_2_4; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  unfold rot_index_z.
  destruct (Z.ltb_spec (shift_pre + j) (Zlength b_l)) as [Hlt | Hge].
  - entailer!.
  - lia.
Qed. 

Lemma proof_of_rotation_match_at_entail_wit_3_1 : rotation_match_at_entail_wit_3_1.
Proof.
  unfold rotation_match_at_entail_wit_3_1; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  entailer!.
  apply rotation_match_progress_step_new_mismatch; [lia | exact H].
Qed. 

Lemma proof_of_rotation_match_at_entail_wit_3_2 : rotation_match_at_entail_wit_3_2.
Proof.
  unfold rotation_match_at_entail_wit_3_2; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  entailer!.
  apply rotation_match_progress_step_keep_mismatch; [lia | assumption].
Qed. 

Lemma proof_of_rotation_match_at_entail_wit_3_3 : rotation_match_at_entail_wit_3_3.
Proof.
  unfold rotation_match_at_entail_wit_3_3; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  entailer!.
  apply rotation_match_progress_step_keep_mismatch; [lia | assumption].
Qed. 

Lemma proof_of_rotation_match_at_entail_wit_3_4 : rotation_match_at_entail_wit_3_4.
Proof.
  unfold rotation_match_at_entail_wit_3_4; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  apply rotation_match_progress_step_same; try assumption; try lia.
Qed. 

Lemma proof_of_rotation_match_at_return_wit_1 : rotation_match_at_return_wit_1.
Proof.
  unfold rotation_match_at_return_wit_1; intros; c154_prep.
  assert (j = Zlength b_l) by lia.
  subst j.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  entailer!.
  apply not_rotation_match_at_from_progress.
  assumption.
Qed. 

Lemma proof_of_rotation_match_at_return_wit_2 : rotation_match_at_return_wit_2.
Proof.
  unfold rotation_match_at_return_wit_2; intros; c154_prep.
  assert (j = Zlength b_l) by lia.
  subst j.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  eapply rotation_match_at_from_progress; eauto; lia.
Qed. 

Lemma proof_of_rotation_occurs_at_shift_entail_wit_1 : rotation_occurs_at_shift_entail_wit_1.
Proof.
  unfold rotation_occurs_at_shift_entail_wit_1; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  entailer!.
  apply rotation_shift_search_init.
Qed. 

Lemma proof_of_rotation_occurs_at_shift_entail_wit_2_1 : rotation_occurs_at_shift_entail_wit_2_1.
Proof.
  unfold rotation_occurs_at_shift_entail_wit_2_1; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  eapply rotation_shift_search_step_hit; eauto; lia.
Qed. 

Lemma proof_of_rotation_occurs_at_shift_entail_wit_2_2 : rotation_occurs_at_shift_entail_wit_2_2.
Proof.
  unfold rotation_occurs_at_shift_entail_wit_2_2; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  eapply rotation_shift_search_step_hit; eauto; lia.
Qed. 

Lemma proof_of_rotation_occurs_at_shift_entail_wit_2_3 : rotation_occurs_at_shift_entail_wit_2_3.
Proof.
  unfold rotation_occurs_at_shift_entail_wit_2_3; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  entailer!.
  eapply rotation_shift_search_step_miss_zero; eauto; lia.
Qed. 

Lemma proof_of_rotation_occurs_at_shift_entail_wit_2_4 : rotation_occurs_at_shift_entail_wit_2_4.
Proof.
  unfold rotation_occurs_at_shift_entail_wit_2_4; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  eapply rotation_shift_search_step_miss_one; eauto; lia.
Qed. 

Lemma proof_of_rotation_occurs_at_shift_return_wit_1 : rotation_occurs_at_shift_return_wit_1.
Proof.
  unfold rotation_occurs_at_shift_return_wit_1; intros; c154_prep.
  assert (pos = Zlength a_l - Zlength b_l + 1) by lia.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  entailer!.
  eapply rotation_shift_search_final_miss; eauto.
Qed. 

Lemma proof_of_rotation_occurs_at_shift_return_wit_2 : rotation_occurs_at_shift_return_wit_2.
Proof.
  unfold rotation_occurs_at_shift_return_wit_2; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  apply rotation_shift_search_final_hit with (pos := pos); assumption.
Qed. 

Lemma proof_of_cycpattern_check_entail_wit_1 : cycpattern_check_entail_wit_1.
Proof.
  unfold cycpattern_check_entail_wit_1; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  entailer!.
  apply rotation_any_search_init.
Qed. 

Lemma proof_of_cycpattern_check_entail_wit_2_1 : cycpattern_check_entail_wit_2_1.
Proof.
  unfold cycpattern_check_entail_wit_2_1; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  eapply rotation_any_search_step_hit; eauto; lia.
Qed. 

Lemma proof_of_cycpattern_check_entail_wit_2_2 : cycpattern_check_entail_wit_2_2.
Proof.
  unfold cycpattern_check_entail_wit_2_2; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  eapply rotation_any_search_step_hit; eauto; lia.
Qed. 

Lemma proof_of_cycpattern_check_entail_wit_2_3 : cycpattern_check_entail_wit_2_3.
Proof.
  unfold cycpattern_check_entail_wit_2_3; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  entailer!.
  eapply rotation_any_search_step_miss_zero; eauto; lia.
Qed. 

Lemma proof_of_cycpattern_check_entail_wit_2_4 : cycpattern_check_entail_wit_2_4.
Proof.
  unfold cycpattern_check_entail_wit_2_4; intros; c154_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  eapply rotation_any_search_step_miss_one; eauto; lia.
Qed. 

Lemma proof_of_cycpattern_check_return_wit_1 : cycpattern_check_return_wit_1.
Proof.
  unfold cycpattern_check_return_wit_1; intros; c154_prep.
  assert (shift = Zlength b_l) by lia.
  subst shift.
  entailer!.
  apply problem_154_spec_z_false_of_no_any_match; try assumption.
  eapply rotation_any_search_final_miss; eauto; lia.
Qed. 

Lemma proof_of_cycpattern_check_return_wit_2 : cycpattern_check_return_wit_2.
Proof.
  unfold cycpattern_check_return_wit_2; intros; c154_prep.
  entailer!.
  apply problem_154_spec_z_true_of_any_match.
  apply rotation_any_search_final_hit with (shift := shift).
  assumption.
Qed. 

Lemma proof_of_cycpattern_check_return_wit_3 : cycpattern_check_return_wit_3.
Proof.
  unfold cycpattern_check_return_wit_3; intros; c154_prep.
  entailer!.
  apply problem_154_spec_z_false_too_long.
  lia.
Qed. 

Lemma proof_of_cycpattern_check_return_wit_4 : cycpattern_check_return_wit_4.
Proof.
  unfold cycpattern_check_return_wit_4; intros; c154_prep.
  entailer!.
  apply problem_154_spec_z_true_of_any_match.
  left. lia.
Qed. 
