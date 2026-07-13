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
From SimpleC.EE Require Import C_121_goal.
From SimpleC.EE Require Import C_121_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_121.
Local Open Scope sac.

Ltac normalize_121 :=
  subst;
  repeat match goal with
  | H : context[?i * 2] |- _ =>
      replace (i * 2) with (2 * i) in H by lia
  | |- context[?i * 2] =>
      replace (i * 2) with (2 * i) by lia
  end;
  repeat match goal with
  | Hrem : Z.rem (Znth (2 * ?i) ?l 0) 2 = 1
    |- context[sum_prefix_121 (?i + 1) ?l] =>
      rewrite (sum_prefix_121_step_take l i ltac:(lia) Hrem)
  | Hrem : Z.rem (Znth (2 * ?i) ?l 0) 2 = 1,
    H : context[sum_prefix_121 (?i + 1) ?l] |- _ =>
      rewrite (sum_prefix_121_step_take l i ltac:(lia) Hrem) in H
  | Hrem : Z.rem (Znth (2 * ?i) ?l 0) 2 <> 1
    |- context[sum_prefix_121 (?i + 1) ?l] =>
      rewrite (sum_prefix_121_step_skip l i ltac:(lia) Hrem)
  | Hrem : Z.rem (Znth (2 * ?i) ?l 0) 2 <> 1,
    H : context[sum_prefix_121 (?i + 1) ?l] |- _ =>
      rewrite (sum_prefix_121_step_skip l i ltac:(lia) Hrem) in H
  | |- context[sum_prefix_121 0 ?l] =>
      rewrite (sum_prefix_121_0 l)
  | H : context[sum_prefix_121 0 ?l] |- _ =>
      rewrite (sum_prefix_121_0 l) in H
  end.

Ltac pose_121_range :=
  try match goal with
  | Hrange : sum_121_int_range ?l,
    Hi : 0 <= ?i,
    Hlt : 2 * ?i < Zlength ?l |- _ =>
      let H := fresh "Hrange_step" in
      pose proof (sum_prefix_121_range l i Hrange Hi Hlt) as H;
      destruct H as (? & ? & ?)
  end.

Ltac solve_121_pures :=
  normalize_121;
  pose_121_range;
  normalize_121;
  repeat match goal with
  | |- (_ && _) _ => split
  end;
  try assumption;
  try reflexivity;
  try unfold INT_MIN_121 in *;
  try lia;
  repeat match goal with
  | |- coq_prop _ _ => unfold coq_prop; simpl; solve_121_pures
  end.

Ltac solve_121_vc :=
  try (right; intros);
  pre_process; normalize_121; entailer!;
  solve_121_pures.

Lemma proof_of_solutions_safety_wit_10_split_goal_1 : solutions_safety_wit_10_split_goal_1.
Proof. solve_121_vc. Qed.

Lemma proof_of_solutions_safety_wit_10_split_goal_2 : solutions_safety_wit_10_split_goal_2.
Proof. solve_121_vc. Qed.

Lemma proof_of_solutions_safety_wit_10 : solutions_safety_wit_10.
Proof. solve_121_vc. Qed.

Lemma proof_of_solutions_entail_wit_1_split_goal_1 : solutions_entail_wit_1_split_goal_1.
Proof. solve_121_vc. Qed.

Lemma proof_of_solutions_entail_wit_1 : solutions_entail_wit_1.
Proof. solve_121_vc. Qed.

Lemma proof_of_solutions_entail_wit_2_1_split_goal_1 : solutions_entail_wit_2_1_split_goal_1.
Proof. solve_121_vc. Qed.

Lemma proof_of_solutions_entail_wit_2_1 : solutions_entail_wit_2_1.
Proof. solve_121_vc. Qed.

Lemma proof_of_solutions_entail_wit_2_2_split_goal_1 : solutions_entail_wit_2_2_split_goal_1.
Proof. solve_121_vc. Qed.

Lemma proof_of_solutions_entail_wit_2_2_split_goal_2 : solutions_entail_wit_2_2_split_goal_2.
Proof. solve_121_vc. Qed.
 
Lemma proof_of_solutions_entail_wit_2_2_split_goal_3 : solutions_entail_wit_2_2_split_goal_3.
Proof. solve_121_vc. Qed.

Lemma proof_of_solutions_entail_wit_2_2 : solutions_entail_wit_2_2.
Proof. solve_121_vc. Qed.

Lemma proof_of_solutions_return_wit_1_split_goal_1 : solutions_return_wit_1_split_goal_1.
Proof.
  pre_process; normalize_121; entailer!.
  match goal with
  | Hrange : sum_121_int_range ?l,
    Hi : 0 <= ?i,
    Hge : 2 * ?i >= Zlength ?l,
    Hle : 2 * ?i <= Zlength ?l + 1
    |- problem_121_spec_z ?l (sum_prefix_121 ?i ?l) =>
      eapply problem_121_spec_z_of_prefix_exit;
      [apply sum_121_int_range_nonneg; exact Hrange
      | exact Hi
      | exact Hge
      | exact Hle
      | reflexivity]
  end.
Qed.

Lemma proof_of_solutions_return_wit_1 : solutions_return_wit_1.
Proof.
  right; intros.
  pre_process; normalize_121; entailer!.
  match goal with
  | Hrange : sum_121_int_range ?l,
    Hi : 0 <= ?i,
    Hge : 2 * ?i >= Zlength ?l,
    Hle : 2 * ?i <= Zlength ?l + 1
    |- problem_121_spec_z ?l (sum_prefix_121 ?i ?l) =>
      eapply problem_121_spec_z_of_prefix_exit;
      [apply sum_121_int_range_nonneg; exact Hrange
      | exact Hi
      | exact Hge
      | exact Hle
      | reflexivity]
  end.
Qed.
