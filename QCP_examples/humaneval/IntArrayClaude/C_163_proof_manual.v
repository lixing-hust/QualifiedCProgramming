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
From SimpleC.EE Require Import C_163_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_163.
Local Open Scope sac.

Lemma proof_of_generate_integers_safety_wit_15 : generate_integers_safety_wit_15.
Proof.
  pre_process.
  entailer!.
  - unfold generate_bounds in *.
    destruct H6 as [Ha _].
    subst a.
    pose proof (Z.le_min_l a0 b0).
    lia.
  - unfold generate_bounds in *.
    destruct H6 as [_ Hb].
    subst b.
    assert (Z.max a0 b0 < INT_MAX) by (apply Z.max_lub_lt; lia).
    lia.
Qed.

Lemma proof_of_generate_integers_entail_wit_1_1 : generate_integers_entail_wit_1_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  - apply generate_prefix_init; lia.
  - unfold generate_bounds.
    subst a_pre b_pre.
    rewrite Z.min_l by lia.
    rewrite Z.max_r by lia.
    split; reflexivity.
Qed.

Lemma proof_of_generate_integers_entail_wit_1_2 : generate_integers_entail_wit_1_2.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  - apply generate_prefix_init; lia.
  - unfold generate_bounds.
    subst a_pre b_pre.
    rewrite Z.min_r by lia.
    rewrite Z.max_l by lia.
    split; reflexivity.
Qed.

Lemma proof_of_generate_integers_entail_wit_2 : generate_integers_entail_wit_2.
Proof.
  pre_process.
  Exists output_l_2.
  subst capacity.
  entailer!.
  all: try match goal with
  | H : generate_bounds _ _ _ _ |- _ =>
      unfold generate_bounds in H; destruct H as [Ha Hb]; subst;
      pose proof (Z.le_min_l a0 b0); pose proof (Z.le_min_r a0 b0); lia
  end.
Qed.

Lemma proof_of_generate_integers_entail_wit_3 : generate_integers_entail_wit_3.
Proof.
  pre_process.
  Exists (output_l_2 ++ (i :: nil)).
  subst capacity.
  sep_apply (IntArray.seg_single data output_size i).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size (output_size + 1)); [ | lia].
  entailer!.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - apply generate_prefix_take; try lia.
    + match goal with
      | H : generate_bounds a0 b0 a b |- _ =>
          unfold generate_bounds in H; destruct H as [Ha _]
      end.
      subst a.
      pose proof (Z.le_min_l a0 b0).
      pose proof (Z.le_min_r a0 b0).
      lia.
    + match goal with H : generate_prefix a i b output_l_2 |- _ => exact H end.
    + apply mod2_zero_even_true.
      rewrite <- Z.rem_mod_nonneg by (
        try lia;
        unfold generate_bounds in H6; destruct H6 as [Ha _]; subst a;
        pose proof (Z.le_min_l a0 b0);
        pose proof (Z.le_min_r a0 b0);
        lia).
      exact H11.
Qed.

Lemma proof_of_generate_integers_entail_wit_4_2 : generate_integers_entail_wit_4_2.
Proof.
  pre_process.
  Exists output_l_2.
  subst capacity.
  entailer!.
  apply generate_prefix_skip.
  - unfold generate_bounds in H8.
    destruct H8 as [Ha _].
    subst a.
    pose proof (Z.le_min_l a0 b0).
    pose proof (Z.le_min_r a0 b0).
    lia.
  - exact H14.
  - lia.
  - intros [Hlt _]. lia.
Qed.

Lemma proof_of_generate_integers_entail_wit_4_3 : generate_integers_entail_wit_4_3.
Proof.
  pre_process.
  Exists output_l_2.
  subst capacity.
  entailer!.
  apply generate_prefix_skip.
  - unfold generate_bounds in H9.
    destruct H9 as [Ha _].
    subst a.
    pose proof (Z.le_min_l a0 b0).
    pose proof (Z.le_min_r a0 b0).
    lia.
  - exact H15.
  - lia.
  - intros [_ Heven].
    apply (mod2_nonzero_even_false i).
    + intro Hmod.
      apply H.
      rewrite Z.rem_mod_nonneg by (
        try lia;
        unfold generate_bounds in H9; destruct H9 as [Ha _]; subst a;
        pose proof (Z.le_min_l a0 b0);
        pose proof (Z.le_min_r a0 b0);
        lia).
      exact Hmod.
    + exact Heven.
Qed.

Lemma proof_of_generate_integers_entail_wit_6 : generate_integers_entail_wit_6.
Proof.
  pre_process.
  Exists output_l_2.
  subst capacity.
  entailer!.
  - assert (i = b + 1) by lia.
    subst i.
    exact H13.
  - pose proof (generate_prefix_length_le_4 a i b output_l_2 H13).
    lia.
Qed.

Lemma proof_of_generate_integers_return_wit_1 : generate_integers_return_wit_1.
Proof.
  pre_process.
  Exists output_l_2 10 output_size_2 data_2.
  entailer!.
  apply generate_prefix_full_spec with (lo := a) (hi := b); assumption.
Qed.
