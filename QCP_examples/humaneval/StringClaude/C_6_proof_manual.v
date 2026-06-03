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
From SimpleC.EE Require Import C_6_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_6.
Local Open Scope sac.

Ltac prepare_paren_prefix_step :=
  let Hout := fresh "Hout" in
  let Hin := fresh "Hin" in
  let Hlevel := fresh "Hlevel" in
  let Hmax := fresh "Hmax" in
  match goal with
  | |- context [paren_prefix_output_z (?i + 1) ?l] =>
      pose proof (paren_prefix_step_app l i ltac:(lia)) as [Hout [Hin [Hlevel Hmax]]]
  end;
  rewrite Hout, Hin, Hlevel, Hmax;
  repeat match goal with
  | H : ?output_l = paren_prefix_output_z ?i ?l |- context[paren_prefix_output_z ?i ?l] =>
      replace (paren_prefix_output_z i l) with output_l by congruence
  | H : ?in_group = paren_prefix_in_group_z ?i ?l |- context[paren_prefix_in_group_z ?i ?l] =>
      replace (paren_prefix_in_group_z i l) with in_group by congruence
  | H : ?level = paren_prefix_level_z ?i ?l |- context[paren_prefix_level_z ?i ?l] =>
      replace (paren_prefix_level_z i l) with level by congruence
  | H : ?max_level = paren_prefix_max_z ?i ?l |- context[paren_prefix_max_z ?i ?l] =>
      replace (paren_prefix_max_z i l) with max_level by congruence
  end;
  repeat match goal with
  | H : Znth ?i (app ?l (cons 0 nil)) 0 = ?v |- _ => rewrite H
  end;
  cbn;
  repeat match goal with
  | |- context[Z.eqb ?x ?x] => rewrite Z.eqb_refl
  end.

Lemma proof_of_parse_nested_parens_entail_wit_1 : parse_nested_parens_entail_wit_1.
Proof.
  pre_process; try subst orig; subst retval_3.
  Exists (@nil Z) 0.
  sep_apply (IntArray.undef_full_split_to_undef_seg retval_2 0 len).
  2: { lia. }
  rewrite (IntArray.undef_seg_empty retval_2 0).
  rewrite (IntArray.seg_empty retval_2 0 0).
  entailer!.
  all: unfold paren_prefix_output_z, paren_prefix_in_group_z,
    paren_prefix_level_z, paren_prefix_max_z, paren_prefix_state_z;
    try (rewrite (sublist_nil l 0 0) by lia); simpl; reflexivity.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_2_1 : parse_nested_parens_entail_wit_2_1.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    paren_prefix_output_z (i + 1) l = app output_l_2 (max_level :: nil) /\
    paren_prefix_in_group_z (i + 1) l = 0 /\
    paren_prefix_level_z (i + 1) l = 0 /\
    paren_prefix_max_z (i + 1) l = 0).
  {
    prepare_paren_prefix_step.
    rewrite Z.eqb_refl.
    replace (Z.eqb in_group 0) with false by (symmetry; apply Z.eqb_neq; lia).
    repeat split; reflexivity.
  }
  sep_apply (IntArray.seg_single data output_size_2 max_level).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size_2 (output_size_2 + 1)
               output_l_2 (max_level :: nil)); [ | lia].
  destruct Hnext as [Hout [Hin [Hlevel Hmax]]].
  Exists (app output_l_2 (max_level :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_2_2 : parse_nested_parens_entail_wit_2_2.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    paren_prefix_output_z (i + 1) l = output_l_2 /\
    paren_prefix_in_group_z (i + 1) l = in_group /\
    paren_prefix_level_z (i + 1) l = level /\
    paren_prefix_max_z (i + 1) l = max_level).
  {
    prepare_paren_prefix_step.
    subst in_group.
    rewrite Z.eqb_refl.
    repeat split; reflexivity.
  }
  destruct Hnext as [Hout [Hin [Hlevel Hmax]]].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_2_3 : parse_nested_parens_entail_wit_2_3.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    paren_prefix_output_z (i + 1) l = output_l_2 /\
    paren_prefix_in_group_z (i + 1) l = 1 /\
    paren_prefix_level_z (i + 1) l = level + 1 /\
    paren_prefix_max_z (i + 1) l = level + 1).
  {
    prepare_paren_prefix_step.
    replace (Z.eqb 40 32) with false by reflexivity.
    replace (Z.eqb 40 40) with true by reflexivity.
    unfold paren_zmax.
    destruct (Z.leb_spec max_level (level + 1)); try lia.
    repeat split; reflexivity.
  }
  destruct Hnext as [Hout [Hin [Hlevel Hmax]]].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_2_4 : parse_nested_parens_entail_wit_2_4.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    paren_prefix_output_z (i + 1) l = output_l_2 /\
    paren_prefix_in_group_z (i + 1) l = 1 /\
    paren_prefix_level_z (i + 1) l = level + 1 /\
    paren_prefix_max_z (i + 1) l = max_level).
  {
    prepare_paren_prefix_step.
    replace (Z.eqb 40 32) with false by reflexivity.
    replace (Z.eqb 40 40) with true by reflexivity.
    unfold paren_zmax.
    destruct (Z.leb_spec max_level (level + 1)); try lia.
    repeat split; reflexivity.
  }
  destruct Hnext as [Hout [Hin [Hlevel Hmax]]].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_2_5 : parse_nested_parens_entail_wit_2_5.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    paren_prefix_output_z (i + 1) l = output_l_2 /\
    paren_prefix_in_group_z (i + 1) l = 1 /\
    paren_prefix_level_z (i + 1) l = level - 1 /\
    paren_prefix_max_z (i + 1) l = max_level).
  {
    prepare_paren_prefix_step.
    rewrite H, H0.
    replace (Z.ltb 0 level) with true by (symmetry; apply Z.ltb_lt; lia).
    repeat split; reflexivity.
  }
  destruct Hnext as [Hout [Hin [Hlevel Hmax]]].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_2_6 : parse_nested_parens_entail_wit_2_6.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    paren_prefix_output_z (i + 1) l = output_l_2 /\
    paren_prefix_in_group_z (i + 1) l = 1 /\
    paren_prefix_level_z (i + 1) l = 0 /\
    paren_prefix_max_z (i + 1) l = max_level).
  {
    prepare_paren_prefix_step.
    rewrite H, H0.
    replace (Z.ltb 0 level) with false by (symmetry; apply Z.ltb_ge; lia).
    repeat split; reflexivity.
  }
  destruct Hnext as [Hout [Hin [Hlevel Hmax]]].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_3 : parse_nested_parens_entail_wit_3.
Proof.
  pre_process; try subst orig.
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_4_1 : parse_nested_parens_entail_wit_4_1.
Proof.
  pre_process; try subst orig.
  assert (i = len) by lia; subst i.
  assert (in_group = 1) by lia.
  assert (Hout:
    paren_final_output_z (paren_prefix_output_z len l)
      (paren_prefix_in_group_z len l) (paren_prefix_max_z len l) =
    app output_l_2 (max_level :: nil)).
  {
    subst in_group.
    unfold paren_final_output_z.
    replace (paren_prefix_in_group_z len l) with 1 by congruence.
    rewrite Z.eqb_neq by lia.
    replace (paren_prefix_output_z len l) with output_l_2 by congruence.
    replace (paren_prefix_max_z len l) with max_level by congruence.
    reflexivity.
  }
  sep_apply (IntArray.seg_single data output_size_2 max_level).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size_2 (output_size_2 + 1)
               output_l_2 (max_level :: nil)); [ | lia].
  Exists (app output_l_2 (max_level :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Hout; try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_4_2 : parse_nested_parens_entail_wit_4_2.
Proof.
  pre_process; try subst orig.
  assert (i = len) by lia; subst i.
  assert (Hout:
    paren_final_output_z (paren_prefix_output_z len l)
      (paren_prefix_in_group_z len l) (paren_prefix_max_z len l) =
    output_l_2).
  {
    subst in_group.
    unfold paren_final_output_z.
    rewrite Z.eqb_refl.
    congruence.
  }
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_parse_nested_parens_return_wit_1 : parse_nested_parens_return_wit_1.
Proof.
  pre_process; try subst orig.
  Exists data_2 output_l_2 output_size_2.
  entailer!.
  subst output_l_2.
  rewrite paren_prefix_full_final by lia.
  apply problem_6_spec_z_intro; try assumption.
  reflexivity.
Qed.
