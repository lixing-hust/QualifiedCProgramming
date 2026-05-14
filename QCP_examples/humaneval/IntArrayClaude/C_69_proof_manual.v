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
From SimpleC.EE Require Import C_69_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_69.
Local Open Scope sac.

Lemma proof_of_search_safety_wit_14 : search_safety_wit_14.
Proof.
  pre_process.
  match goal with
  | H : search_inner_state_69 ?input ?i ?j ?vals ?cnts ?has ?max |- _ =>
      pose proof (search_inner_cnt_at_j_bound_69 input i j vals cnts has max H ltac:(lia))
  end.
  replace (j - 0) with j by lia.
  entailer!.
Qed.

Lemma proof_of_search_entail_wit_1 : search_entail_wit_1.
Proof.
  pre_process.
  sep_apply (IntArray.undef_full_to_undef_seg retval).
  sep_apply (IntArray.undef_full_to_undef_seg retval_2).
  Exists (@nil Z) (@nil Z).
  rewrite !IntArray.seg_empty.
  entailer!.
  apply search_outer_state_69_init.
Qed.

Lemma proof_of_search_entail_wit_2 : search_entail_wit_2.
Proof.
  pre_process.
  Exists cnts_l_2 vals_l_2.
  entailer!.
  - eapply search_inner_state_69_init; eauto.
    lia.
  - apply H6.
    lia.
  - apply H6.
    lia.
Qed.

Lemma proof_of_search_entail_wit_3_1 : search_entail_wit_3_1.
Proof.
  pre_process.
  Left.
  Exists cnts_l_2 vals_l_2.
  entailer!.
  unfold search_inner_to_outer_69.
  match goal with Hhas : has = 0 |- _ => rewrite Hhas end.
  simpl.
  match goal with
  | Hs : search_inner_state_69 input_l i j vals_l_2 cnts_l_2 has max,
    Hhas : has = 0 |- _ =>
      rewrite Hhas in Hs;
      replace j with (Zlength vals_l_2) in Hs by lia;
      exact Hs
  end.
Qed.

Lemma proof_of_search_entail_wit_3_2 : search_entail_wit_3_2.
Proof.
  pre_process.
  Right.
  Exists (replace_Znth j (Znth (j - 0) cnts_l_2 0 + 1) cnts_l_2) vals_l.
  replace (j - 0) with j in * by lia.
  entailer!.
  - unfold search_inner_to_outer_69.
    simpl.
    replace (Znth j vals_l 0) with (hit_max_69 vals_l cnts_l_2 j max).
    + eapply search_hit_to_outer_69 with (has := has); eauto; try lia.
    + unfold hit_max_69.
      rewrite Znth_replace_Znth_eq_69 in H0 by lia.
      assert ((Znth j cnts_l_2 0 + 1 >=? Znth j vals_l 0) = true) as Hge.
      { apply Z.geb_le. lia. }
      assert ((Znth j vals_l 0 >? max) = true) as Hgt.
      { apply Z.gtb_lt. lia. }
      rewrite Hge, Hgt.
      reflexivity.
  - rewrite replace_Znth_length_69; lia.
Qed.

Lemma proof_of_search_entail_wit_3_3 : search_entail_wit_3_3.
Proof.
  pre_process.
  Right.
  Exists (replace_Znth j (Znth (j - 0) cnts_l_2 0 + 1) cnts_l_2) vals_l_2.
  replace (j - 0) with j in * by lia.
  entailer!.
  - unfold search_inner_to_outer_69.
    simpl.
    replace max with (hit_max_69 vals_l_2 cnts_l_2 j max).
    + eapply search_hit_to_outer_69 with (has := has); eauto; try lia.
    + unfold hit_max_69.
      rewrite Znth_replace_Znth_eq_69 in H by lia.
      destruct (andb (Znth j cnts_l_2 0 + 1 >=? Znth j vals_l_2 0)
                (Znth j vals_l_2 0 >? max)) eqn:Hmax; auto.
      apply andb_true_iff in Hmax as [Hge _].
      apply Z.geb_le in Hge.
      lia.
  - rewrite replace_Znth_length_69; lia.
Qed.

Lemma proof_of_search_entail_wit_3_4 : search_entail_wit_3_4.
Proof.
  pre_process.
  Right.
  Exists (replace_Znth j (Znth (j - 0) cnts_l_2 0 + 1) cnts_l_2) vals_l_2.
  replace (j - 0) with j in * by lia.
  entailer!.
  - unfold search_inner_to_outer_69.
    simpl.
    replace max with (hit_max_69 vals_l_2 cnts_l_2 j max).
    + eapply search_hit_to_outer_69 with (has := has); eauto; try lia.
    + unfold hit_max_69.
      destruct (andb (Znth j cnts_l_2 0 + 1 >=? Znth j vals_l_2 0)
                (Znth j vals_l_2 0 >? max)) eqn:Hmax; auto.
      apply andb_true_iff in Hmax as [_ Hgt].
      apply Z.gtb_lt in Hgt.
      lia.
  - rewrite replace_Znth_length_69; lia.
Qed.

Lemma proof_of_search_entail_wit_4 : search_entail_wit_4.
Proof.
  pre_process.
  Exists cnts_l_2 vals_l_2.
  replace (j - 0) with j in * by lia.
  subst has.
  entailer!.
  eapply search_inner_state_miss_step_69; eauto; try lia.
Qed.

Lemma proof_of_search_entail_wit_6 : search_entail_wit_6.
Proof.
  pre_process.
  Exists cnts_l_2 (vals_l_2 ++ current :: nil).
  sep_apply (IntArray.seg_single vals freq_size current).
  sep_apply (IntArray.seg_merge_to_seg vals 0 freq_size (freq_size + 1)); [ | lia].
  sep_apply (IntArray.undef_seg_merge_to_undef_seg cnts freq_size (freq_size + 1) lst_size_pre ltac:(split; lia)).
  entailer!.
  - unfold search_after_val_write_69.
    exists vals_l_2, cnts_l_2.
    split; [exact H6 | idtac].
    split; [lia | idtac].
    split; [reflexivity | idtac].
    split; [reflexivity | idtac].
    subst has; exact H20.
  - rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil.
    lia.
Qed.

Lemma proof_of_search_entail_wit_7_1 : search_entail_wit_7_1.
Proof.
  pre_process.
  Exists (cnts_l_2 ++ 1 :: nil) vals_l_2.
  sep_apply (IntArray.seg_single cnts freq_size 1).
  sep_apply (IntArray.seg_merge_to_seg cnts 0 freq_size (freq_size + 1)); [ | lia].
  entailer!.
  - eapply search_after_val_write_add_count_69.
    + eauto.
    + lia.
    + eauto.
    + left; repeat split; auto.
  - rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil.
    lia.
Qed.

Lemma proof_of_search_entail_wit_7_2 : search_entail_wit_7_2.
Proof.
  pre_process.
  Exists (cnts_l_2 ++ 1 :: nil) vals_l_2.
  sep_apply (IntArray.seg_single cnts freq_size 1).
  sep_apply (IntArray.seg_merge_to_seg cnts 0 freq_size (freq_size + 1)); [ | lia].
  entailer!.
  - eapply search_after_val_write_add_count_69.
    + eauto.
    + lia.
    + eauto.
    + right; left; repeat split; auto.
  - rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil.
    lia.
Qed.

Lemma proof_of_search_entail_wit_7_3 : search_entail_wit_7_3.
Proof.
  pre_process.
  Exists (cnts_l_2 ++ 1 :: nil) vals_l_2.
  sep_apply (IntArray.seg_single cnts freq_size 1).
  sep_apply (IntArray.seg_merge_to_seg cnts 0 freq_size (freq_size + 1)); [ | lia].
  entailer!.
  - eapply search_after_val_write_add_count_69.
    + eauto.
    + lia.
    + eauto.
    + right; right; repeat split; auto.
  - rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil.
    lia.
Qed.

Lemma proof_of_search_entail_wit_8_1 : search_entail_wit_8_1.
Proof.
  pre_process.
  Exists cnts_l_2 vals_l_2.
  entailer!.
  match goal with
  | H : search_outer_add_new_69 _ _ _ _ _ _ _ _ |- _ =>
      unfold search_outer_add_new_69 in H; tauto
  end.
Qed.

Lemma proof_of_search_entail_wit_8_2 : search_entail_wit_8_2.
Proof.
  pre_process.
  Exists cnts_l_2 vals_l_2.
  subst has.
  entailer!.
Qed.

Lemma proof_of_search_return_wit_1 : search_return_wit_1.
Proof.
  pre_process.
  entailer!.
  unfold problem_69_spec.
  match goal with
  | H : search_outer_state_69 input_l i vals_l cnts_l max |- _ =>
      unfold search_outer_state_69 in H;
      destruct H as (_ & _ & _ & Hmax)
  end.
  unfold search_prefix_69, prefix_69 in Hmax.
  replace i with (Zlength input_l) in Hmax by lia.
  rewrite sublist_self in Hmax by reflexivity.
  exact Hmax.
Qed.
