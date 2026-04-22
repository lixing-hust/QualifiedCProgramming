Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260417_150448_copy_array Require Import copy_array_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_copy_array_entail_wit_1 : copy_array_entail_wit_1.
Proof.
  pre_process.
  rewrite Zlength_correct in *.
  prop_apply IntArray.full_length.
  rewrite app_nil_l.
  entailer!.
  subst n_pre.
  replace (Z.of_nat (Datatypes.length ls)) with (Z.of_nat (Datatypes.length ld)) by lia.
  unfold sublist.
  simpl.
  rewrite firstn_all2 by lia.
  entailer!.
  all: rewrite Zlength_correct; lia.
Qed.

Lemma proof_of_copy_array_return_wit_1 : copy_array_return_wit_1.
Proof.
  pre_process.
  rewrite Zlength_correct in *.
  replace i with n_pre in * by lia.
  assert (app (sublist 0 n_pre ls) (sublist n_pre n_pre ld) = ls).
  {
    rewrite (sublist_self ls n_pre).
    2: {
      rewrite Zlength_correct.
      lia.
    }
    rewrite (sublist_nil ld n_pre n_pre) by lia.
    rewrite app_nil_r.
    reflexivity.
  }
  replace (app (sublist 0 n_pre ls) (sublist n_pre n_pre ld)) with ls by (symmetry; exact H7).
  entailer!.
Qed.

Lemma proof_of_copy_array_which_implies_wit_1 : copy_array_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply (IntArray.full_split_to_missing_i src_pre i); try lia.
  sep_apply (IntArray.full_split_to_missing_i dst_pre i); try lia.
  replace (Znth i (app (sublist 0 i ls) (sublist i n_pre ld)) 0) with (Znth i ld 0) by
    (
      rewrite app_Znth2;
      [
        assert (Hsub : Zlength (sublist 0 i ls) = i) by (rewrite Zlength_sublist0; lia);
        rewrite Hsub;
        replace (i - i) with 0 by lia;
        rewrite Znth_sublist; try lia;
        replace (0 + i) with i by lia;
        apply Znth_indep;
        lia
      |
        rewrite Zlength_sublist0;
        lia
      ]
    ).
  entailer!.
Qed.

Lemma proof_of_copy_array_which_implies_wit_2 : copy_array_which_implies_wit_2.
Proof.
  pre_process.
  rewrite Zlength_correct in *.
  sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  assert (Hreplace:
    replace_Znth i (Znth i ls 0) (app (sublist 0 i ls) (sublist i n_pre ld)) =
    app (sublist 0 (i + 1) ls) (sublist (i + 1) n_pre ld)).
  {
    assert (Hpref : Zlength (sublist 0 i ls) = i).
    {
      apply Zlength_sublist0.
      split.
      - lia.
      - rewrite Zlength_correct.
        lia.
    }
    rewrite replace_Znth_app_r.
    2: {
      rewrite Hpref.
      lia.
    }
    rewrite replace_Znth_nothing.
    2: {
      rewrite Hpref.
      lia.
    }
    replace (i - Zlength (sublist 0 i ls)) with 0 by lia.
    rewrite (sublist_split i n_pre (i + 1) ld) by lia.
    rewrite (sublist_single i ld 0) by lia.
    assert (Hls_split : sublist 0 (i + 1) ls = app (sublist 0 i ls) (Znth i ls 0 :: nil)).
    {
      rewrite (sublist_split 0 (i + 1) i ls) by lia.
      rewrite (sublist_single i ls 0) by lia.
      simpl.
      reflexivity.
    }
    rewrite Hls_split.
    rewrite <- app_assoc.
    unfold replace_Znth.
    simpl.
    reflexivity.
  }
  rewrite Hreplace.
  rewrite replace_Znth_Znth.
  entailer!.
Qed.
