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
From SimpleC.EE Require Import C_17_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_17.
Local Open Scope sac.

Ltac prepare_music_prefix_step :=
  let Hprefix_out := fresh "Hprefix_out" in
  let Hprefix_state := fresh "Hprefix_state" in
  match goal with
  | |- context [music_prefix_output_z (?i + 1) ?l] =>
      pose proof (music_prefix_step_app l i ltac:(lia)) as [Hprefix_out Hprefix_state]
  end;
  rewrite Hprefix_out, Hprefix_state;
  repeat match goal with
  | H : ?output_l = music_prefix_output_z ?i ?l |- context[music_prefix_output_z ?i ?l] =>
      replace (music_prefix_output_z i l) with output_l by congruence
  end;
  repeat match goal with
  | H : ?state = music_prefix_state_z ?i ?l |- context[music_prefix_state_z ?i ?l] =>
      replace (music_prefix_state_z i l) with state by congruence
  end;
  repeat match goal with
  | H : Znth ?i (app ?l (cons 0 nil)) 0 = ?v |- _ => rewrite H
  end;
  repeat match goal with
  | H : ?s = ?v |- context[?s] =>
      let T := type of s in
      unify T Z;
      is_var s;
      rewrite H
  end.

Lemma proof_of_parse_music_entail_wit_1 : parse_music_entail_wit_1.
Proof.
  pre_process; try subst orig.
  Exists (@nil Z) 0.
  sep_apply (IntArray.undef_full_split_to_undef_seg retval_2 0 (retval_3 + 1)).
  2: { lia. }
  subst retval_3.
  rewrite (IntArray.undef_seg_empty retval_2 0).
  rewrite (IntArray.seg_empty retval_2 0 0).
  entailer!.
  all: try congruence; unfold music_prefix_output_z, music_prefix_state_z;
    try (rewrite (sublist_nil l 0 0) by lia); simpl; reflexivity.
Qed.

Lemma proof_of_parse_music_entail_wit_2_1 : parse_music_entail_wit_2_1.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output_z (i + 1) l = output_l_2 /\
    music_prefix_state_z (i + 1) l = 0).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state_z i l) with state by congruence.
    apply music_step_space_skip; congruence.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_music_entail_wit_2_2 : parse_music_entail_wit_2_2.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output_z (i + 1) l = app output_l_2 (1 :: nil) /\
    music_prefix_state_z (i + 1) l = 0).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state_z i l) with state by congruence.
    subst state.
    apply music_step_space_4.
  }
  sep_apply (IntArray.seg_single data output_size_2 1).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size_2 (output_size_2 + 1)
               output_l_2 (1 :: nil)); [ | lia].
  destruct Hnext as [Hout Hstate].
  Exists (app output_l_2 (1 :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_parse_music_entail_wit_2_3 : parse_music_entail_wit_2_3.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output_z (i + 1) l = app output_l_2 (2 :: nil) /\
    music_prefix_state_z (i + 1) l = 0).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state_z i l) with state by congruence.
    subst state.
    apply music_step_space_2.
  }
  sep_apply (IntArray.seg_single data output_size_2 2).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size_2 (output_size_2 + 1)
               output_l_2 (2 :: nil)); [ | lia].
  destruct Hnext as [Hout Hstate].
  Exists (app output_l_2 (2 :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_parse_music_entail_wit_2_4 : parse_music_entail_wit_2_4.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output_z (i + 1) l = app output_l_2 (4 :: nil) /\
    music_prefix_state_z (i + 1) l = 0).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state_z i l) with state by congruence.
    subst state.
    apply music_step_space_1.
  }
  sep_apply (IntArray.seg_single data output_size_2 4).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size_2 (output_size_2 + 1)
               output_l_2 (4 :: nil)); [ | lia].
  destruct Hnext as [Hout Hstate].
  Exists (app output_l_2 (4 :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_parse_music_entail_wit_2_5 : parse_music_entail_wit_2_5.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output_z (i + 1) l = output_l_2 /\
    music_prefix_state_z (i + 1) l = 1).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state_z i l) with state by congruence.
    subst state.
    apply music_step_nonspace_0_o.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_music_entail_wit_2_6 : parse_music_entail_wit_2_6.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output_z (i + 1) l = output_l_2 /\
    music_prefix_state_z (i + 1) l = 3).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state_z i l) with state by congruence.
    subst state.
    apply music_step_nonspace_0_dot.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_music_entail_wit_2_7 : parse_music_entail_wit_2_7.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output_z (i + 1) l = output_l_2 /\
    music_prefix_state_z (i + 1) l = 2).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state_z i l) with state by congruence.
    subst state.
    apply music_step_nonspace_1_bar.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_music_entail_wit_2_8 : parse_music_entail_wit_2_8.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output_z (i + 1) l = output_l_2 /\
    music_prefix_state_z (i + 1) l = 4).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state_z i l) with state by congruence.
    subst state.
    apply music_step_nonspace_3_bar.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_music_entail_wit_2_9 : parse_music_entail_wit_2_9.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output_z (i + 1) l = output_l_2 /\
    music_prefix_state_z (i + 1) l = 5).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state_z i l) with state by congruence.
    subst state.
    apply music_step_nonspace_3_bad; congruence.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_music_entail_wit_2_10 : parse_music_entail_wit_2_10.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output_z (i + 1) l = output_l_2 /\
    music_prefix_state_z (i + 1) l = 5).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state_z i l) with state by congruence.
    subst state.
    apply music_step_nonspace_1_bad; congruence.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_music_entail_wit_2_11 : parse_music_entail_wit_2_11.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output_z (i + 1) l = output_l_2 /\
    music_prefix_state_z (i + 1) l = 5).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state_z i l) with state by congruence.
    subst state.
    apply music_step_nonspace_0_bad; congruence.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_music_entail_wit_2_12 : parse_music_entail_wit_2_12.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output_z (i + 1) l = output_l_2 /\
    music_prefix_state_z (i + 1) l = 5).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state_z i l) with state by congruence.
    apply music_step_nonspace_other_bad; congruence.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_music_entail_wit_3 : parse_music_entail_wit_3.
Proof.
  pre_process; try subst orig.
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_music_entail_wit_4_1 : parse_music_entail_wit_4_1.
Proof.
  pre_process; try subst orig.
  assert (i = len) as -> by lia.
  assert (Hfinal:
    music_final_output_z (music_prefix_output_z len l) (music_prefix_state_z len l) =
    app output_l_2 (4 :: nil)).
  {
    match goal with H : output_l_2 = music_prefix_output_z len l |- _ => rewrite <- H end.
    match goal with H : state = music_prefix_state_z len l |- _ => rewrite <- H end.
    match goal with H : state = 1 |- _ => rewrite H end.
    unfold music_final_output_z.
    rewrite Z.eqb_refl.
    reflexivity.
  }
  sep_apply (IntArray.seg_single data output_size_2 4).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size_2 (output_size_2 + 1)
               output_l_2 (4 :: nil)); [ | lia].
  Exists (app output_l_2 (4 :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_parse_music_entail_wit_4_2 : parse_music_entail_wit_4_2.
Proof.
  pre_process; try subst orig.
  assert (i = len) as -> by lia.
  assert (Hfinal:
    music_final_output_z (music_prefix_output_z len l) (music_prefix_state_z len l) =
    app output_l_2 (2 :: nil)).
  {
    match goal with H : output_l_2 = music_prefix_output_z len l |- _ => rewrite <- H end.
    match goal with H : state = music_prefix_state_z len l |- _ => rewrite <- H end.
    match goal with H : state = 2 |- _ => rewrite H end.
    unfold music_final_output_z.
    rewrite (proj2 (Z.eqb_neq 2 1) ltac:(lia)).
    rewrite Z.eqb_refl.
    reflexivity.
  }
  sep_apply (IntArray.seg_single data output_size_2 2).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size_2 (output_size_2 + 1)
               output_l_2 (2 :: nil)); [ | lia].
  Exists (app output_l_2 (2 :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_parse_music_entail_wit_4_3 : parse_music_entail_wit_4_3.
Proof.
  pre_process; try subst orig.
  assert (i = len) as -> by lia.
  assert (Hfinal:
    music_final_output_z (music_prefix_output_z len l) (music_prefix_state_z len l) =
    app output_l_2 (1 :: nil)).
  {
    match goal with H : output_l_2 = music_prefix_output_z len l |- _ => rewrite <- H end.
    match goal with H : state = music_prefix_state_z len l |- _ => rewrite <- H end.
    match goal with H : state = 4 |- _ => rewrite H end.
    unfold music_final_output_z.
    rewrite (proj2 (Z.eqb_neq 4 1) ltac:(lia)).
    rewrite (proj2 (Z.eqb_neq 4 2) ltac:(lia)).
    rewrite Z.eqb_refl.
    reflexivity.
  }
  sep_apply (IntArray.seg_single data output_size_2 1).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size_2 (output_size_2 + 1)
               output_l_2 (1 :: nil)); [ | lia].
  Exists (app output_l_2 (1 :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_parse_music_entail_wit_4_4 : parse_music_entail_wit_4_4.
Proof.
  pre_process; try subst orig.
  assert (i = len) as -> by lia.
  assert (Hfinal:
    music_final_output_z (music_prefix_output_z len l) (music_prefix_state_z len l) =
    output_l_2).
  {
    match goal with H : output_l_2 = music_prefix_output_z len l |- _ => rewrite <- H end.
    match goal with H : state = music_prefix_state_z len l |- _ => rewrite <- H end.
    unfold music_final_output_z.
    repeat match goal with
    | H : state <> ?v |- context [Z.eqb state ?v] =>
        rewrite (proj2 (Z.eqb_neq state v) H)
    end.
    reflexivity.
  }
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_music_return_wit_1 : parse_music_return_wit_1.
Proof.
  pre_process; try subst orig.
  Exists data_2 output_l_2 output_size_2.
  entailer!.
  try match goal with
  | H : output_l_2 =
        music_final_output_z (music_prefix_output_z len l)
          (music_prefix_state_z len l) |- _ =>
      rewrite H
  | H : music_final_output_z (music_prefix_output_z len l)
          (music_prefix_state_z len l) = output_l_2 |- _ =>
      rewrite <- H
  end.
  try rewrite music_prefix_full_final by lia.
  apply string_of_list_z_map_nat_music_output.
  assumption.
Qed.
