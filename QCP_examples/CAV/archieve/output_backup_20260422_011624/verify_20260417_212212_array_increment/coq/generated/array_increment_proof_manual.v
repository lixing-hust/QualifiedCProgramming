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
From SimpleC.EE.CAV.verify_20260417_212212_array_increment Require Import array_increment_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_increment_safety_wit_2 : array_increment_safety_wit_2.
Proof.
  pre_process.
  match goal with
  | Hbound: forall _ : Z, _ -> _ |- _ => pose proof (Hbound i) as Hi
  end.
  assert (0 <= i < n_pre) by lia.
  specialize (Hi H10).
  compute in *.
  lia.
Qed.

Lemma proof_of_array_increment_entail_wit_1 : array_increment_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z), l.
  rewrite app_nil_l.
  prop_apply IntArray.full_length.
  rewrite Zlength_correct in *.
  entailer!.
  all: try lia.
  intros k Hk.
  replace (0 + k) with k by lia.
  apply Znth_indep.
  lia.
Qed.

Lemma proof_of_array_increment_entail_wit_2 : array_increment_entail_wit_2.
Proof.
  pre_process.
  Exists l1', (sublist (i_2 + 1) n_pre l).
  rewrite Zlength_correct in *.
  entailer!.
  - apply Zlength_sublist0; lia.
  - intros k Hk.
    rewrite Znth_sublist; try lia.
    replace (i_2 + 1 + (k - (i_2 + 1))) with k by lia.
    apply Znth_indep.
    lia.
Qed.

Lemma proof_of_array_increment_entail_wit_3 : array_increment_entail_wit_3.
Proof.
  pre_process.
  Exists (app l1 l2).
  rewrite Zlength_correct in *.
  entailer!.
  - rewrite Zlength_app. lia.
  - intros k Hk.
    rewrite app_Znth1.
    2: lia.
    apply H2.
    lia.
Qed.

Lemma proof_of_array_increment_return_wit_1 : array_increment_return_wit_1.
Proof.
  pre_process.
  Exists l0_2.
  entailer!.
Qed.

Lemma proof_of_array_increment_which_implies_wit_1 : array_increment_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply (IntArray.full_split_to_missing_i a_pre i); try lia.
  replace (Znth i (app l1 l2) 0) with (Znth i l 0).
  entailer!.
  rewrite app_Znth2.
  2: {
    rewrite Zlength_correct in *.
    lia.
  }
  rewrite Zlength_correct in *.
  replace (i - Z.of_nat (Datatypes.length l1)) with 0 by lia.
  rewrite H0 by lia.
  apply Znth_indep.
  lia.
Qed.

Lemma proof_of_array_increment_which_implies_wit_2 : array_increment_which_implies_wit_2.
Proof.
  pre_process.
  sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  Exists (app l1 ((Znth i l 0 + 1) :: nil)).
  rewrite Zlength_correct in *.
  assert (Hreplace :
    replace_Znth i (Znth i l 0 + 1) (app l1 l2) =
    app (app l1 ((Znth i l 0 + 1) :: nil)) (sublist (i + 1) n_pre l)).
  {
    rewrite replace_Znth_app_r.
    2: lia.
    rewrite replace_Znth_nothing.
    2: lia.
    replace (i - Zlength l1) with 0 by lia.
    assert (Hl2 : l2 = sublist i n_pre l).
    {
      apply Zlength_eq.
      - rewrite H1.
        apply Zlength_sublist0; lia.
      - intros k Hk.
        rewrite Znth_sublist; try lia.
        rewrite H2 by lia.
        replace (i + (k - i)) with k by lia.
        reflexivity.
    }
    rewrite Hl2.
    rewrite (sublist_split i n_pre (i + 1) l) by lia.
    rewrite (sublist_single i l 0) by lia.
    unfold replace_Znth.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
  }
  rewrite Hreplace.
  entailer!.
  - rewrite Zlength_app, Zlength_correct. simpl. lia.
  - intros k Hk.
    rewrite app_Znth1; try (rewrite Zlength_app, Zlength_correct; simpl; lia).
    destruct (Z_lt_ge_dec k i).
    + rewrite app_Znth1; try lia.
      apply H.
      lia.
    + assert (k = i) by lia.
      subst k.
      rewrite app_Znth2.
      2: lia.
      rewrite Zlength_correct.
      replace (i - Z.of_nat (Datatypes.length l1)) with 0 by lia.
      simpl.
      rewrite Z.add_comm.
      reflexivity.
Qed.
