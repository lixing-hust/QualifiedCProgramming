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
From SimpleC.EE.CAV.verify_20260417_211327_set_zero Require Import set_zero_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_set_zero_entail_wit_1 : set_zero_entail_wit_1.
Proof.
  pre_process.
  rewrite Zlength_correct.
  unfold zeros.
  simpl repeat.
  rewrite app_nil_l.
  prop_apply IntArray.full_length.
  entailer!.
  subst n_pre.
  unfold sublist.
  simpl.
  rewrite firstn_all2.
  entailer!.
  lia.
Qed.

Lemma proof_of_set_zero_return_wit_1 : set_zero_return_wit_1.
Proof.
  pre_process.
  rewrite Zlength_correct in *.
  replace i with n_pre in * by lia.
  assert (zeros n_pre ++ sublist n_pre n_pre l = zeros n_pre).
  {
    unfold sublist.
    rewrite skipn_firstn.
    replace (Z.to_nat n_pre - Z.to_nat n_pre)%nat with 0%nat by lia.
    simpl firstn.
    rewrite app_nil_r.
    auto.
  }
  rewrite H4.
  entailer!.
Qed.

Lemma proof_of_set_zero_which_implies_wit_1 : set_zero_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply (IntArray.full_split_to_missing_i a_pre i); try lia.
  replace (Znth i (zeros i ++ sublist i n_pre l) 0) with (Znth i l 0).
  entailer!.
  rewrite app_Znth2.
  2: {
    rewrite Zlength_correct.
    unfold zeros.
    rewrite repeat_length.
    lia.
  }
  rewrite Zlength_correct.
  unfold zeros.
  rewrite repeat_length.
  replace (i - Z.of_nat (Z.to_nat i)) with 0 by lia.
  rewrite Znth_sublist; try lia.
  replace (0 + i) with i by lia.
  apply Znth_indep.
  lia.
Qed.

Lemma proof_of_set_zero_which_implies_wit_2 : set_zero_which_implies_wit_2.
Proof.
  pre_process.
  sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  rewrite Zlength_correct in *.
  assert (Hreplace: replace_Znth i 0 (zeros i ++ sublist i n_pre l) = zeros (i + 1) ++ sublist (i + 1) n_pre l).
  {
    assert (Zlength (zeros i) = i) by (rewrite Zlength_correct; unfold zeros; rewrite repeat_length; lia).
    rewrite replace_Znth_app_r; try lia.
    rewrite replace_Znth_nothing; try lia.
    replace (i - Zlength (zeros i)) with 0 by lia.
    replace (zeros (i + 1)) with (zeros i ++ (0 :: nil)).
    2: {
      unfold zeros.
      replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia.
      rewrite repeat_app.
      simpl.
      reflexivity.
    }
    rewrite sublist_split with (mid := (i + 1)); try lia.
    rewrite sublist_single with (a := 0); try lia.
    simpl.
    unfold replace_Znth.
    simpl.
    rewrite <- app_assoc.
    simpl.
    reflexivity.
  }
  rewrite Hreplace.
  entailer!.
Qed.
