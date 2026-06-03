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
From SimpleC.EE Require Import C_18_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_18.
Local Open Scope sac.

Ltac c18_prep :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Lemma proof_of_how_many_times_safety_wit_26 : how_many_times_safety_wit_26.
Proof.
  unfold how_many_times_safety_wit_26.
  intros.
  c18_prep.
  pose proof (count_matches_upto_nonneg i l sub).
  pose proof (count_matches_upto_le i l sub ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_how_many_times_entail_wit_1 : how_many_times_entail_wit_1.
Proof.
  unfold how_many_times_entail_wit_1.
  intros.
  c18_prep.
  entailer!.
Qed.

Lemma proof_of_how_many_times_entail_wit_2 : how_many_times_entail_wit_2.
Proof.
  unfold how_many_times_entail_wit_2.
  intros.
  c18_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  entailer!.
  apply match_progress_init.
Qed.

Lemma proof_of_how_many_times_entail_wit_3_1 : how_many_times_entail_wit_3_1.
Proof.
  unfold how_many_times_entail_wit_3_1.
  intros.
  c18_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  apply match_progress_step_new_mismatch; lia.
Qed.

Lemma proof_of_how_many_times_entail_wit_3_2 : how_many_times_entail_wit_3_2.
Proof.
  unfold how_many_times_entail_wit_3_2.
  intros.
  c18_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  apply match_progress_step_keep_mismatch; assumption.
Qed.

Lemma proof_of_how_many_times_entail_wit_3_3 : how_many_times_entail_wit_3_3.
Proof.
  unfold how_many_times_entail_wit_3_3.
  intros.
  c18_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  apply match_progress_step_keep_mismatch; assumption.
Qed.

Lemma proof_of_how_many_times_entail_wit_3_4 : how_many_times_entail_wit_3_4.
Proof.
  unfold how_many_times_entail_wit_3_4.
  intros.
  c18_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  entailer!.
  apply match_progress_step_same; try assumption; lia.
Qed.

Lemma proof_of_how_many_times_entail_wit_4_1 : how_many_times_entail_wit_4_1.
Proof.
  unfold how_many_times_entail_wit_4_1.
  intros.
  pre_process.
  assert (j = m) by lia.
  subst j.
  subst.
  repeat rewrite app_Znth1 in * by lia.
  assert (Hhit : match_at_zb i l sub = true).
  {
    apply match_progress_true_at_end; try lia.
    assumption.
  }
  rewrite count_matches_upto_step_hit by (try lia; exact Hhit).
  entailer!.
Qed.

Lemma proof_of_how_many_times_entail_wit_4_2 : how_many_times_entail_wit_4_2.
Proof.
  unfold how_many_times_entail_wit_4_2.
  intros.
  pre_process.
  assert (j = m) by lia.
  subst j.
  subst.
  repeat rewrite app_Znth1 in * by lia.
  assert (Hmiss : match_at_zb i l sub = false).
  {
    apply match_progress_false_at_end; try lia.
    assumption.
  }
  rewrite count_matches_upto_step_miss by (try lia; exact Hmiss).
  entailer!.
Qed.

Lemma proof_of_how_many_times_return_wit_1 : how_many_times_return_wit_1.
Proof.
  unfold how_many_times_return_wit_1.
  intros.
  c18_prep.
  assert (i = Zlength l - Zlength sub + 1) by lia.
  subst i.
  entailer!.
  apply problem_18_spec_z_count_matches_full; assumption || lia.
Qed. 

Lemma proof_of_how_many_times_return_wit_2 : how_many_times_return_wit_2.
Proof.
  unfold how_many_times_return_wit_2.
  intros.
  c18_prep.
  entailer!.
  apply problem_18_spec_z_zero_too_long.
  lia.
Qed.

Lemma proof_of_how_many_times_return_wit_3 : how_many_times_return_wit_3.
Proof.
  unfold how_many_times_return_wit_3.
  intros.
  c18_prep.
  entailer!.
  apply problem_18_spec_z_zero_empty_substring.
  lia.
Qed.

Lemma proof_of_how_many_times_return_wit_4 : how_many_times_return_wit_4.
Proof.
  unfold how_many_times_return_wit_4.
  intros.
  c18_prep.
  entailer!.
  apply problem_18_spec_z_zero_empty_input.
  lia.
Qed.
