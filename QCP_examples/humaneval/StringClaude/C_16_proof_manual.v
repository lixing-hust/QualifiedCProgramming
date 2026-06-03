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
From SimpleC.EE Require Import C_16_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_16.
Local Open Scope sac.

Ltac c16_prep :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia;
  entailer!.

Lemma proof_of_count_distinct_characters_entail_wit_1 : count_distinct_characters_entail_wit_1.
Proof.
  unfold count_distinct_characters_entail_wit_1.
  intros.
  c16_prep.
Qed. 

Lemma proof_of_count_distinct_characters_entail_wit_2_1 : count_distinct_characters_entail_wit_2_1.
Proof.
  unfold count_distinct_characters_entail_wit_2_1.
  intros.
  c16_prep.
  try (apply lower_seen_state_init; rewrite lower_z_upper by lia; reflexivity).
  try (rewrite lower_z_upper by lia; reflexivity).
Qed. 

Lemma proof_of_count_distinct_characters_entail_wit_2_2 : count_distinct_characters_entail_wit_2_2.
Proof.
  unfold count_distinct_characters_entail_wit_2_2.
  intros.
  c16_prep.
  try (apply lower_seen_state_init; rewrite lower_z_low by lia; reflexivity).
  try (rewrite lower_z_low by lia; reflexivity).
Qed. 

Lemma proof_of_count_distinct_characters_entail_wit_2_3 : count_distinct_characters_entail_wit_2_3.
Proof.
  unfold count_distinct_characters_entail_wit_2_3.
  intros.
  c16_prep.
  try (apply lower_seen_state_init; rewrite lower_z_high by lia; reflexivity).
  try (rewrite lower_z_high by lia; reflexivity).
Qed. 

Lemma proof_of_count_distinct_characters_entail_wit_3_1 : count_distinct_characters_entail_wit_3_1.
Proof.
  unfold count_distinct_characters_entail_wit_3_1.
  intros.
  c16_prep.
  eapply lower_seen_state_step_hit; try lia; try eassumption.
  try rewrite lower_z_upper by lia. lia.
Qed. 

Lemma proof_of_count_distinct_characters_entail_wit_3_2 : count_distinct_characters_entail_wit_3_2.
Proof.
  unfold count_distinct_characters_entail_wit_3_2.
  intros.
  c16_prep.
  eapply lower_seen_state_step_hit; try lia; try eassumption.
  try rewrite lower_z_low by lia. lia.
Qed. 

Lemma proof_of_count_distinct_characters_entail_wit_3_3 : count_distinct_characters_entail_wit_3_3.
Proof.
  unfold count_distinct_characters_entail_wit_3_3.
  intros.
  c16_prep.
  eapply lower_seen_state_step_hit; try lia; try eassumption.
  try rewrite lower_z_high by lia. lia.
Qed. 

Lemma proof_of_count_distinct_characters_entail_wit_3_4 : count_distinct_characters_entail_wit_3_4.
Proof.
  unfold count_distinct_characters_entail_wit_3_4.
  intros.
  c16_prep.
  eapply lower_seen_state_step_miss; try lia; try eassumption.
  try rewrite lower_z_high by lia. lia.
Qed. 

Lemma proof_of_count_distinct_characters_entail_wit_3_5 : count_distinct_characters_entail_wit_3_5.
Proof.
  unfold count_distinct_characters_entail_wit_3_5.
  intros.
  c16_prep.
  eapply lower_seen_state_step_miss; try lia; try eassumption.
  try rewrite lower_z_low by lia. lia.
Qed. 

Lemma proof_of_count_distinct_characters_entail_wit_3_6 : count_distinct_characters_entail_wit_3_6.
Proof.
  unfold count_distinct_characters_entail_wit_3_6.
  intros.
  c16_prep.
  eapply lower_seen_state_step_miss; try lia; try eassumption.
  try rewrite lower_z_upper by lia. lia.
Qed. 

Lemma proof_of_count_distinct_characters_entail_wit_4_1 : count_distinct_characters_entail_wit_4_1.
Proof.
  unfold count_distinct_characters_entail_wit_4_1.
  intros.
  pre_process.
  subst.
  assert (j = i) by lia.
  subst j.
  assert (Hstep :
    count_distinct_lower_upto i l + 1 =
    count_distinct_lower_upto (i + 1) l).
  {
    rewrite distinct_lower_prefix_step_new.
    - reflexivity.
    - lia.
    - destruct H9 as [_ [_ [_ Hzero]]].
      exact (Hzero eq_refl).
  }
  entailer!.
Qed. 

Lemma proof_of_count_distinct_characters_entail_wit_4_2 : count_distinct_characters_entail_wit_4_2.
Proof.
  unfold count_distinct_characters_entail_wit_4_2.
  intros.
  pre_process.
  subst.
  assert (j = i) by lia.
  subst j.
  assert (Hstep :
    count_distinct_lower_upto i l =
    count_distinct_lower_upto (i + 1) l).
  {
    symmetry.
    apply distinct_lower_prefix_step_seen; [lia | idtac].
    destruct H9 as [[Hseen0 | Hseen1] [_ [Hone _]]].
    - contradiction.
    - apply Hone. exact Hseen1.
  }
  entailer!.
Qed. 

Lemma proof_of_count_distinct_characters_return_wit_1 : count_distinct_characters_return_wit_1.
Proof.
  unfold count_distinct_characters_return_wit_1.
  intros.
  pre_process.
  subst.
  assert (i = Zlength l) by lia.
  subst i.
  entailer!.
  apply problem_16_spec_z_count.
  assumption.
Qed. 
