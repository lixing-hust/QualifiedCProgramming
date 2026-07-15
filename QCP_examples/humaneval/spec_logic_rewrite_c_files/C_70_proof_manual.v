Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_70_goal.
From SimpleC.EE Require Import C_70_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_70.
Local Open Scope sac.

Ltac solve_70_pures :=
  repeat match goal with
  | |- (_ && _) _ => split
  end;
  try assumption; try reflexivity; try lia;
  repeat match goal with
  | |- coq_prop _ _ => unfold coq_prop; simpl; try assumption; try reflexivity; try lia
  end.

Ltac normalize_70 :=
  subst;
  repeat match goal with
  | Hge : ?i >= ?n, Hle : ?i <= ?n |- _ =>
      let Heq := fresh "Heq" in assert (Heq : i = n) by lia; subst i
  | H1 : ?n = Zlength ?prefix_l,
    H2 : ?n = Zlength ?full_l,
    Hsub : sublist 0 ?n ?full_l = ?prefix_l |- _ =>
      let Heq := fresh "Heq" in
      pose proof (sublist_full_eq_70 full_l prefix_l n H2 H1 Hsub) as Heq;
      subst full_l
  end;
  repeat match goal with
  | |- context[sublist 0 0 ?l] => change (sublist 0 0 l) with (@nil Z)
  | H : context[sublist 0 0 ?l] |- _ => change (sublist 0 0 l) with (@nil Z) in H
  | |- context[sublist 0 (Zlength ?l) ?l] => rewrite (sublist_self l (Zlength l) eq_refl)
  | H : context[sublist 0 (Zlength ?l) ?l] |- _ => rewrite (sublist_self l (Zlength l) eq_refl) in H
  | Hlen : ?n = Zlength ?l |- context[sublist 0 ?n ?l] => rewrite (sublist_self l n Hlen)
  | Hlen : ?n = Zlength ?l, H : context[sublist 0 ?n ?l] |- _ => rewrite (sublist_self l n Hlen) in H
  | |- context[sublist 0 (?i + 1) ?l] => rewrite (sublist_snoc_Znth_70 l i) by lia
  | H : context[sublist 0 (?i + 1) ?l] |- _ => rewrite (sublist_snoc_Znth_70 l i) in H by lia
  | |- context[strange_pairs_prefix_70 ?l 0] => rewrite (strange_pairs_prefix_zero_70 l)
  | H : context[strange_pairs_prefix_70 ?l 0] |- _ => rewrite (strange_pairs_prefix_zero_70 l) in H
  | |- context[Zlength (strange_output_70 ?l)] => rewrite (Zlength_strange_output_70 l)
  | H : context[Zlength (strange_output_70 ?l)] |- _ => rewrite (Zlength_strange_output_70 l) in H
  end.

Ltac solve_70_spatial_setup :=
  repeat match goal with
  | |- context[IntArray.seg ?p 0 0 (@nil Z)] =>
      rewrite (IntArray.seg_empty p 0 0)
  | |- context[IntArray.undef_full ?p ?n ** _ |-- IntArray.undef_seg ?p 0 ?n] =>
      sep_apply_l_atomic (IntArray.undef_full_to_undef_seg p n)
  | |- context[IntArray.undef_full ?p ?n ** _ |-- _ ** IntArray.undef_seg ?p 0 ?n] =>
      sep_apply_l_atomic (IntArray.undef_full_to_undef_seg p n)
  end.

Ltac solve_70_bare_undef :=
  match goal with
  | |- ?P |-- ?Q =>
      lazymatch P with
      | IntArray.undef_full ?p ?n =>
          lazymatch Q with
          | IntArray.undef_seg ?p 0 ?n =>
              sep_apply_l_atomic (IntArray.undef_full_to_undef_seg p n)
          end
      end
  end.

Ltac solve_70_vc :=
  try (left; intros); try (right; intros);
  pre_process; normalize_70; solve_70_spatial_setup; try cancel; try solve_70_bare_undef; entailer!;
  try match goal with
  | Hn : ?n = Zlength ?l, Hright : ?right = ?n - 1 - ?left, Hlt : ?left < ?right,
    Hk : ?k = 2 * ?left + 1 |- ?k + 1 = Zlength (strange_pairs_prefix_70 ?l (?left + 1)) =>
      eapply strange_pairs_prefix_step_len_70; eauto
  | Hn : ?n = Zlength ?l, Hright : ?right = ?n - 1 - ?left, Hlt : ?left < ?right
    |- _ ++ _ ++ _ = strange_pairs_prefix_70 ?l (?left + 1) =>
      symmetry; eapply strange_pairs_prefix_step_70; eauto
  | Hn : ?n = Zlength ?l, Hright : ?right = ?n - 1 - ?left, Hge : ?left >= ?right,
    Hneq : ?left <> ?right, Hk : ?k = 2 * ?left,
    Hle : ?k <= ?n, Hlen : ?k = Zlength (strange_pairs_prefix_70 ?l ?left) |- ?k = ?n =>
      destruct (strange_output_no_middle_70 l n left right k Hn Hright Hge Hneq Hk Hle Hlen) as [? [? ?]]; assumption
  | Hn : ?n = Zlength ?l, Hright : ?right = ?n - 1 - ?left, Hge : ?left >= ?right,
    Heq : ?left = ?right, Hk : ?k = 2 * ?left,
    Hlen : ?k = Zlength (strange_pairs_prefix_70 ?l ?left) |- ?k + 1 = ?n =>
      destruct (strange_output_middle_70 l n left right k Hn Hright Hge Heq Hk Hlen) as [? [? ?]]; assumption
  | Hn : ?n = Zlength ?l, Hright : ?right = ?n - 1 - ?left, Hge : ?left >= ?right,
    Hneq : ?left <> ?right, Hk : ?k = 2 * ?left,
    Hle : ?k <= ?n, Hlen : ?k = Zlength (strange_pairs_prefix_70 ?l ?left) |- strange_output_prefix_70 ?l ?n = strange_output_70 ?l =>
      destruct (strange_output_no_middle_70 l n left right k Hn Hright Hge Hneq Hk Hle Hlen) as [? [? ?]]; assumption
  | Hn : ?n = Zlength ?l, Hright : ?right = ?n - 1 - ?left, Hge : ?left >= ?right,
    Heq : ?left = ?right, Hk : ?k = 2 * ?left,
    Hlen : ?k = Zlength (strange_pairs_prefix_70 ?l ?left) |- strange_output_prefix_70 ?l ?n = strange_output_70 ?l =>
      destruct (strange_output_middle_70 l n left right k Hn Hright Hge Heq Hk Hlen) as [? [? ?]]; assumption
  | Hn : ?n = Zlength ?l, Hright : ?right = ?n - 1 - ?left, Hge : ?left >= ?right,
    Hneq : ?left <> ?right, Hk : ?k = 2 * ?left,
    Hle : ?k <= ?n, Hlen : ?k = Zlength (strange_pairs_prefix_70 ?l ?left) |- strange_pairs_prefix_70 ?l ?left = strange_output_70 ?l =>
      destruct (strange_output_no_middle_70 l n left right k Hn Hright Hge Hneq Hk Hle Hlen) as [? [? ?]]; assumption
  | Hn : ?n = Zlength ?l, Hright : ?right = ?n - 1 - ?left, Hge : ?left >= ?right,
    Heq : ?left = ?right, Hk : ?k = 2 * ?left,
    Hlen : ?k = Zlength (strange_pairs_prefix_70 ?l ?left) |- strange_pairs_prefix_70 ?l ?left ++ [Znth ?left ?l 0] = strange_output_70 ?l =>
      destruct (strange_output_middle_70 l n left right k Hn Hright Hge Heq Hk Hlen) as [? [? ?]]; assumption
  | Hpre : problem_70_pre_z ?input, Hsort : sorted_int_list_by 1 ?sorted_l,
    Hperm : Permutation ?input ?sorted_l |- problem_70_spec_z ?input (strange_output_70 ?sorted_l) =>
      eapply sorted_strange_output_spec_70; eauto
  end; normalize_70; try cancel; solve_70_pures.

Lemma proof_of_strange_sort_list_entail_wit_1 : strange_sort_list_entail_wit_1.
Proof.
  left; intros.
  pre_process; normalize_70.
  rewrite (IntArray.seg_empty retval_3 0 0).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_3 (Zlength input_l)).
  entailer!.
Qed.

Lemma proof_of_strange_sort_list_entail_wit_2 : strange_sort_list_entail_wit_2.
Proof. solve_70_vc. Qed.

Lemma proof_of_strange_sort_list_entail_wit_3 : strange_sort_list_entail_wit_3.
Proof. solve_70_vc. Qed.

Lemma proof_of_strange_sort_list_entail_wit_4 : strange_sort_list_entail_wit_4.
Proof.
  left; intros.
  pre_process; normalize_70.
  Exists sorted_l_2.
  normalize_70; entailer!.
Qed.

Lemma proof_of_strange_sort_list_entail_wit_5 : strange_sort_list_entail_wit_5.
Proof.
  left; intros.
  pre_process; normalize_70.
  Exists sorted_l_2.
  rewrite (IntArray.seg_empty data 0 0).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg data (Zlength input_l)).
  entailer!.
Qed.

Lemma proof_of_strange_sort_list_entail_wit_6 : strange_sort_list_entail_wit_6.
Proof.
  left; intros.
  pre_process; normalize_70.
  Exists sorted_l_2.
  entailer!.
Qed.

Lemma proof_of_strange_sort_list_entail_wit_7 : strange_sort_list_entail_wit_7.
Proof.
  left; intros.
  pre_process; normalize_70.
  Exists sorted_l_2.
  entailer!.
  - replace (strange_pairs_prefix_70 sorted_l_2 (left + 1)) with
      ((strange_pairs_prefix_70 sorted_l_2 left ++
          cons (Znth left sorted_l_2 0) nil) ++
         cons (Znth (Zlength input_l - 1 - left) sorted_l_2 0) nil).
    + entailer!.
    + symmetry.
      rewrite <- app_assoc.
      eapply strange_pairs_prefix_step_70 with
        (n := Zlength input_l) (right := Zlength input_l - 1 - left);
        eauto; lia.
  - eapply strange_pairs_prefix_step_len_70 with
      (n := Zlength input_l) (right := Zlength input_l - 1 - left);
      eauto; lia.
Qed.

Lemma proof_of_strange_sort_list_entail_wit_9_1 : strange_sort_list_entail_wit_9_1.
Proof.
  left; intros.
  destruct (strange_output_no_middle_70 sorted_l_2 lst_size_pre left right k
    PreH8 PreH14 PreH15 PreH1 PreH16 PreH18 PreH17) as [Hk [Hprefix Hout]].
  pre_process; normalize_70.
  rewrite Hout.
  rewrite Hk.
  rewrite (IntArray.undef_seg_empty data (Zlength input_l)).
  sep_apply (IntArray.seg_to_full data 0 (Zlength input_l) (strange_output_70 sorted_l_2)).
  replace (data + 0 * sizeof(INT)) with data by lia.
  replace (Zlength input_l - 0) with (Zlength input_l) by lia.
  sep_apply (IntArray.full_to_full_shape sorted (Zlength input_l) sorted_l_2).
  Exists sorted_l_2.
  entailer!; try cancel.
  eapply sorted_strange_output_spec_70; eauto.
Qed.

Lemma proof_of_strange_sort_list_entail_wit_9_2 : strange_sort_list_entail_wit_9_2.
Proof.
  left; intros.
  destruct (strange_output_middle_70 sorted_l_2 lst_size_pre left right k
    PreH8 PreH14 PreH15 PreH1 PreH16 PreH17) as [Hk [Hprefix Hout]].
  pre_process; normalize_70.
  rewrite Hout.
  rewrite Hk.
  sep_apply (IntArray.seg_to_full data 0 (Zlength input_l) (strange_output_70 sorted_l_2)).
  replace (data + 0 * sizeof(INT)) with data by lia.
  replace (Zlength input_l - 0) with (Zlength input_l) by lia.
  sep_apply (IntArray.full_to_full_shape sorted (Zlength input_l) sorted_l_2).
  Exists sorted_l_2.
  entailer!; try cancel.
  eapply sorted_strange_output_spec_70; eauto.
Qed.

Lemma proof_of_strange_sort_list_return_wit_1 : strange_sort_list_return_wit_1.
Proof.
  left; intros.
  pre_process; normalize_70.
  Exists (strange_output_70 sorted_l).
  Exists (Zlength input_l).
  Exists data_2.
  rewrite Zlength_strange_output_70.
  entailer!.
Qed.
