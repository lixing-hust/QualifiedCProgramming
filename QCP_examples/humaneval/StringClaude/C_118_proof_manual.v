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
From SimpleC.EE Require Import C_118_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_118.
Local Open Scope sac.

Ltac c118_base :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia;
  entailer!;
  try (unfold is_vowel_z, is_consonant_z, is_alpha_z in *; lia).

Ltac c118_left_branch :=
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1];
  entailer!;
  unfold is_vowel_z, is_consonant_z, is_alpha_z in *; lia.

Ltac c118_right_branch :=
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2];
  entailer!;
  unfold is_vowel_z, is_consonant_z, is_alpha_z in *; lia.

Lemma proof_of_is_vowel_code_return_wit_1 : is_vowel_code_return_wit_1.
Proof. unfold is_vowel_code_return_wit_1; intros; c118_base; c118_left_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_2 : is_vowel_code_return_wit_2.
Proof. unfold is_vowel_code_return_wit_2; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_3 : is_vowel_code_return_wit_3.
Proof. unfold is_vowel_code_return_wit_3; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_4 : is_vowel_code_return_wit_4.
Proof. unfold is_vowel_code_return_wit_4; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_5 : is_vowel_code_return_wit_5.
Proof. unfold is_vowel_code_return_wit_5; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_6 : is_vowel_code_return_wit_6.
Proof. unfold is_vowel_code_return_wit_6; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_7 : is_vowel_code_return_wit_7.
Proof. unfold is_vowel_code_return_wit_7; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_8 : is_vowel_code_return_wit_8.
Proof. unfold is_vowel_code_return_wit_8; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_9 : is_vowel_code_return_wit_9.
Proof. unfold is_vowel_code_return_wit_9; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_10 : is_vowel_code_return_wit_10.
Proof. unfold is_vowel_code_return_wit_10; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_11 : is_vowel_code_return_wit_11.
Proof. unfold is_vowel_code_return_wit_11; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_get_closest_vowel_entail_wit_1 : get_closest_vowel_entail_wit_1.
Proof.
  unfold get_closest_vowel_entail_wit_1.
  intros.
  pre_process; subst; entailer!.
  apply no_candidate_after_start.
Qed.

Lemma proof_of_get_closest_vowel_entail_wit_2 : get_closest_vowel_entail_wit_2.
Proof.
  unfold get_closest_vowel_entail_wit_2.
  intros.
  c118_base.
  unfold closest_vowel_candidate_z, is_consonant_z.
  split.
  - lia.
  - split.
    + split.
      * apply H15. lia.
      * exact H1.
    + split.
      * exact H7.
      * split.
        -- apply H15. lia.
        -- exact H4.
Qed.

Lemma proof_of_get_closest_vowel_entail_wit_3_1 : get_closest_vowel_entail_wit_3_1.
Proof.
  unfold get_closest_vowel_entail_wit_3_1.
  intros.
  c118_base.
  intro Hcand.
  unfold closest_vowel_candidate_z, is_consonant_z in Hcand.
  tauto.
Qed.

Lemma proof_of_get_closest_vowel_entail_wit_3_2 : get_closest_vowel_entail_wit_3_2.
Proof.
  unfold get_closest_vowel_entail_wit_3_2.
  intros.
  c118_base.
  intro Hcand.
  unfold closest_vowel_candidate_z, is_consonant_z in Hcand.
  tauto.
Qed.

Lemma proof_of_get_closest_vowel_entail_wit_3_3 : get_closest_vowel_entail_wit_3_3.
Proof.
  unfold get_closest_vowel_entail_wit_3_3.
  intros.
  c118_base.
  intro Hcand.
  unfold closest_vowel_candidate_z in Hcand.
  tauto.
Qed.

Lemma proof_of_get_closest_vowel_entail_wit_4 : get_closest_vowel_entail_wit_4.
Proof.
  unfold get_closest_vowel_entail_wit_4.
  intros.
  c118_base.
  apply no_candidate_after_step; assumption.
Qed.

Lemma proof_of_get_closest_vowel_return_wit_1 : get_closest_vowel_return_wit_1.
Proof.
  unfold get_closest_vowel_return_wit_1.
  intros.
  pre_process; subst.
  Exists 0 nil.
  rewrite (CharArray.undef_seg_empty retval 1).
  entailer!.
  apply problem_118_spec_z_not_found; assumption.
Qed.

Lemma proof_of_get_closest_vowel_return_wit_2 : get_closest_vowel_return_wit_2.
Proof.
  unfold get_closest_vowel_return_wit_2.
  intros.
  pre_process; subst.
  repeat rewrite app_Znth1 in * by lia.
  replace (signed_last_nbits (Znth i l 0) 8) with (Znth i l 0).
  2:{
    symmetry.
    apply signed_last_nbits_eq.
    - lia.
    - match goal with
      | Halpha : alpha_range_z l |- _ =>
          assert (Halpha_i : is_alpha_z (Znth i l 0)) by (apply Halpha; lia)
      end.
      unfold is_alpha_z in Halpha_i.
      lia.
  }
  Exists 1 ((Znth i l 0) :: nil).
  rewrite (CharArray.undef_seg_empty retval 2).
  entailer!.
  apply problem_118_spec_z_found; assumption.
Qed.

Lemma proof_of_get_closest_vowel_return_wit_3 : get_closest_vowel_return_wit_3.
Proof.
  unfold get_closest_vowel_return_wit_3.
  intros.
  pre_process; subst.
  Exists 0 nil.
  rewrite (CharArray.undef_seg_empty retval 1).
  entailer!.
  apply problem_118_spec_z_not_found.
  - assumption.
  - assumption.
  - unfold no_candidate_after_z, closest_vowel_candidate_z.
    intros j Hj Hcand.
    lia.
Qed.
