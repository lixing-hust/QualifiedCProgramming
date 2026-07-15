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
From SimpleC.EE Require Import C_69_goal.
From SimpleC.EE Require Import C_69_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_69.
Local Open Scope sac.

Ltac solve_69_pures :=
  repeat match goal with
  | |- (_ && _) _ => split
  end;
  try assumption;
  try reflexivity;
  try lia;
  repeat match goal with
  | |- coq_prop _ _ => unfold coq_prop; simpl; try assumption; try reflexivity; try lia
  end.

Ltac normalize_69 :=
  subst;
  repeat match goal with
  | Hge : ?j >= ?n, Hle : ?j <= ?n, Hn : ?n = Zlength ?l |- context[count_prefix_69 ?x ?j ?l] =>
      replace j with n by lia;
      rewrite (count_prefix_full_69 x l n Hn)
  | Hge : ?j >= ?n, Hle : ?j <= ?n, Hn : ?n = Zlength ?l,
    H : context[count_prefix_69 ?x ?j ?l] |- _ =>
      replace j with n in H by lia;
      rewrite (count_prefix_full_69 x l n Hn) in H
  | Hn : ?n = Zlength ?l |- context[count_prefix_69 ?x ?n ?l] =>
      rewrite (count_prefix_full_69 x l n Hn)
  | Hn : ?n = Zlength ?l, H : context[count_prefix_69 ?x ?n ?l] |- _ =>
      rewrite (count_prefix_full_69 x l n Hn) in H
  | |- context[count_prefix_69 ?x 0 ?l] =>
      unfold count_prefix_69, count_z_69, count, sublist; cbn
  | H : context[count_prefix_69 ?x 0 ?l] |- _ =>
      unfold count_prefix_69, count_z_69, count, sublist in H; cbn in H
  | Hn : ?n = Zlength ?l, Heq : Znth ?j ?l 0 = ?x |- context[count_prefix_69 ?x (?j + 1) ?l] =>
      rewrite (count_prefix_step_hit_69 x j l ltac:(lia) ltac:(exact Heq))
  | Hn : ?n = Zlength ?l, Heq : Znth ?j ?l 0 = ?x, H : context[count_prefix_69 ?x (?j + 1) ?l] |- _ =>
      rewrite (count_prefix_step_hit_69 x j l ltac:(lia) ltac:(exact Heq)) in H
  | Hn : ?n = Zlength ?l, Hneq : Znth ?j ?l 0 <> ?x |- context[count_prefix_69 ?x (?j + 1) ?l] =>
      rewrite (count_prefix_step_miss_69 x j l ltac:(lia) ltac:(exact Hneq))
  | Hn : ?n = Zlength ?l, Hneq : Znth ?j ?l 0 <> ?x, H : context[count_prefix_69 ?x (?j + 1) ?l] |- _ =>
      rewrite (count_prefix_step_miss_69 x j l ltac:(lia) ltac:(exact Hneq)) in H
  | |- context[find_max_prefix_69 ?l (?i + 1)] =>
      rewrite (find_max_prefix_step_69 l i) by lia
  | H : context[find_max_prefix_69 ?l (?i + 1)] |- _ =>
      rewrite (find_max_prefix_step_69 l i) in H by lia
  | Hlt : ?freq < ?x |- context[update_best_69 ?best ?x ?freq] =>
      rewrite (update_best_miss_69 best x freq Hlt)
  | Hge : ?freq >= ?x, Hle : ?x <= ?best |- context[update_best_69 ?best ?x ?freq] =>
      rewrite (update_best_hit_le_69 best x freq Hge Hle)
  | Hge : ?freq >= ?x, Hgt : ?x > ?best |- context[update_best_69 ?best ?x ?freq] =>
      rewrite (update_best_hit_gt_69 best x freq Hge Hgt)
  | Hlt : ?freq < ?x, H : context[update_best_69 ?best ?x ?freq] |- _ =>
      rewrite (update_best_miss_69 best x freq Hlt) in H
  | Hge : ?freq >= ?x, Hle : ?x <= ?best, H : context[update_best_69 ?best ?x ?freq] |- _ =>
      rewrite (update_best_hit_le_69 best x freq Hge Hle) in H
  | Hge : ?freq >= ?x, Hgt : ?x > ?best, H : context[update_best_69 ?best ?x ?freq] |- _ =>
      rewrite (update_best_hit_gt_69 best x freq Hge Hgt) in H
  end.

Ltac solve_69_vc :=
  try (right; intros);
  pre_process; normalize_69; entailer!;
  try match goal with
  | Hrange : list_positive_int_range_69 ?l,
    Hi : 0 <= ?i,
    Hlt : ?i < Zlength ?l |- context[Znth ?i ?l 0] =>
      pose proof (list_positive_int_range_Znth_69 l i Hrange ltac:(lia))
  end;
  try match goal with
  | Hpre : problem_69_pre_z ?l,
    Hmax : ?m = find_max_prefix_69 ?l (Zlength ?l) |- problem_69_spec_z ?l ?m =>
      eapply find_max_prefix_full_spec_69; [exact Hpre | exact Hmax]
  | Hpre : problem_69_pre_z ?l,
    Hmax : ?m = find_max_prefix_69 ?l ?i,
    Hge : ?i >= ?n,
    Hle : ?i <= ?n,
    Hn : ?n = Zlength ?l |- problem_69_spec_z ?l ?m =>
      eapply find_max_prefix_full_spec_69; [exact Hpre | rewrite <- Hn; replace i with n in Hmax by lia; exact Hmax]
  end;
  normalize_69; solve_69_pures.

Lemma proof_of_search_entail_wit_1_split_goal_1 : search_entail_wit_1_split_goal_1.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_1 : search_entail_wit_1.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_2_split_goal_1 : search_entail_wit_2_split_goal_1.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_2_split_goal_2 : search_entail_wit_2_split_goal_2.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_2_split_goal_3 : search_entail_wit_2_split_goal_3.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_2_split_goal_4 : search_entail_wit_2_split_goal_4.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_2 : search_entail_wit_2.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_3_1_split_goal_1 : search_entail_wit_3_1_split_goal_1.
Proof.
  pre_process; entailer!.
  rewrite count_prefix_step_hit_69 by lia || assumption.
  lia.
Qed.

Lemma proof_of_search_entail_wit_3_1 : search_entail_wit_3_1.
Proof.
  left. intros. entailer!.
  rewrite count_prefix_step_hit_69 by lia || assumption.
  lia.
Qed.

Lemma proof_of_search_entail_wit_3_2_split_goal_1 : search_entail_wit_3_2_split_goal_1.
Proof.
  pre_process; entailer!.
  rewrite count_prefix_step_miss_69 by lia || assumption.
  lia.
Qed.

Lemma proof_of_search_entail_wit_3_2 : search_entail_wit_3_2.
Proof.
  left. intros. entailer!.
  rewrite count_prefix_step_miss_69 by lia || assumption.
  lia.
Qed.

Lemma proof_of_search_entail_wit_4_split_goal_1 : search_entail_wit_4_split_goal_1.
Proof.
  pre_process; entailer!.
  assert (j = lst_size_pre) by lia.
  subst j.
  rewrite (count_prefix_full_69 x input_l lst_size_pre PreH4) in PreH16.
  exact PreH16.
Qed.

Lemma proof_of_search_entail_wit_4 : search_entail_wit_4.
Proof.
  left. intros. entailer!.
  assert (j = lst_size_pre) by lia.
  subst j.
  rewrite (count_prefix_full_69 x input_l lst_size_pre PreH4) in PreH16.
  all: try lia; try assumption.
Qed.

Lemma proof_of_search_entail_wit_5_1_split_goal_1 : search_entail_wit_5_1_split_goal_1.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_5_1_split_goal_2 : search_entail_wit_5_1_split_goal_2.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_5_1 : search_entail_wit_5_1.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_5_2_split_goal_1 : search_entail_wit_5_2_split_goal_1.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_5_2_split_goal_2 : search_entail_wit_5_2_split_goal_2.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_5_2 : search_entail_wit_5_2.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_5_3_split_goal_1 : search_entail_wit_5_3_split_goal_1.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_5_3_split_goal_2 : search_entail_wit_5_3_split_goal_2.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_entail_wit_5_3 : search_entail_wit_5_3.
Proof. solve_69_vc. Qed.

Lemma proof_of_search_return_wit_1_split_goal_1 : search_return_wit_1_split_goal_1.
Proof.
  pre_process; entailer!.
  assert (i = lst_size_pre) by lia.
  subst i.
  eapply find_max_prefix_full_spec_69.
  - exact PreH5.
  - rewrite <- PreH4. exact PreH11.
Qed.

Lemma proof_of_search_return_wit_1 : search_return_wit_1.
Proof.
  left. intros. entailer!.
  assert (i = lst_size_pre) by lia.
  subst i.
  eapply find_max_prefix_full_spec_69.
  - exact PreH5.
  - rewrite <- PreH4. exact PreH11.
Qed.
