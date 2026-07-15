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
From SimpleC.EE Require Import C_73_goal.
From SimpleC.EE Require Import C_73_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_73.
Local Open Scope sac.

Ltac normalize_73 :=
  subst;
  repeat match goal with
  | H : ?n = Zlength ?l |- context[Znth ((?n - 1) - ?i) ?l 0] =>
      rewrite H
  | H : ?n = Zlength ?l, Hx : context[Znth ((?n - 1) - ?i) ?l 0] |- _ =>
      rewrite H in Hx
  | |- context[count_half_mismatches_upto (0) ?l] =>
      rewrite count_half_mismatches_upto_0
  | H : context[count_half_mismatches_upto (0) ?l] |- _ =>
      rewrite count_half_mismatches_upto_0 in H
  | Hneq : Znth ?i ?l 0 <> Znth (Zlength ?l - 1 - ?i) ?l 0 |- context[count_half_mismatches_upto (?i + 1) ?l] =>
      rewrite (count_half_mismatches_upto_step_neq l i ltac:(lia) Hneq)
  | Hneq : Znth ?i ?l 0 <> Znth (Zlength ?l - 1 - ?i) ?l 0,
    H : context[count_half_mismatches_upto (?i + 1) ?l] |- _ =>
      rewrite (count_half_mismatches_upto_step_neq l i ltac:(lia) Hneq) in H
  | Heq : Znth ?i ?l 0 = Znth (Zlength ?l - 1 - ?i) ?l 0 |- context[count_half_mismatches_upto (?i + 1) ?l] =>
      rewrite (count_half_mismatches_upto_step_eq l i ltac:(lia) Heq)
  | Heq : Znth ?i ?l 0 = Znth (Zlength ?l - 1 - ?i) ?l 0,
    H : context[count_half_mismatches_upto (?i + 1) ?l] |- _ =>
      rewrite (count_half_mismatches_upto_step_eq l i ltac:(lia) Heq) in H
  end.

Ltac solve_73_pures :=
  normalize_73;
  try match goal with
  | Hrange : smallest_change_int_range ?l,
    Hi : 0 <= ?i,
    Hloop : ?i < Zlength ?l - 1 - ?i |- _ =>
      pose proof (smallest_change_int_range_current l i Hrange Hi ltac:(unfold half_73; rewrite <- (loop_exit_half_73 l (i + 1)); lia))
  end;
  try match goal with
  | Hrange : smallest_change_int_range ?l,
    Hi : 0 <= ?i,
    Hle : 2 * ?i <= Zlength ?l |- _ =>
      pose proof (smallest_change_int_range_current l i Hrange Hi
                    (loop_index_le_half_73 l i Hi Hle))
  end;
  try match goal with
  | Hexit : ?i >= Zlength ?l - 1 - ?i,
    Hout : ?out = count_half_mismatches_upto ?i ?l |- problem_73_spec_z ?l ?out =>
      eapply problem_73_spec_z_of_exit; [lia | lia | exact Hexit | exact Hout]
  end;
  repeat match goal with
  | |- (_ && _) _ => split
  end;
  try assumption;
  try reflexivity;
  try unfold INT_MIN_73 in *;
  try lia;
  repeat match goal with
  | |- coq_prop _ _ => unfold coq_prop; simpl; solve_73_pures
  end.

Ltac solve_73_vc :=
  try (right; intros);
  pre_process; normalize_73; entailer!;
  solve_73_pures.

Lemma proof_of_smallest_change_safety_wit_9_split_goal_1 : smallest_change_safety_wit_9_split_goal_1.
Proof. solve_73_vc. Qed.

Lemma proof_of_smallest_change_safety_wit_9_split_goal_2 : smallest_change_safety_wit_9_split_goal_2.
Proof. solve_73_vc. Qed.

Lemma proof_of_smallest_change_safety_wit_9 : smallest_change_safety_wit_9.
Proof. solve_73_vc. Qed.

Lemma proof_of_smallest_change_entail_wit_1_split_goal_1 : smallest_change_entail_wit_1_split_goal_1.
Proof. solve_73_vc. Qed.

Lemma proof_of_smallest_change_entail_wit_1 : smallest_change_entail_wit_1.
Proof. solve_73_vc. Qed.

Lemma proof_of_smallest_change_entail_wit_2_1_split_goal_1 : smallest_change_entail_wit_2_1_split_goal_1.
Proof. solve_73_vc. Qed.

Lemma proof_of_smallest_change_entail_wit_2_1 : smallest_change_entail_wit_2_1.
Proof. solve_73_vc. Qed.

Lemma proof_of_smallest_change_entail_wit_2_2_split_goal_1 : smallest_change_entail_wit_2_2_split_goal_1.
Proof. solve_73_vc. Qed.

Lemma proof_of_smallest_change_entail_wit_2_2 : smallest_change_entail_wit_2_2.
Proof. solve_73_vc. Qed.

Lemma proof_of_smallest_change_return_wit_1_split_goal_1 : smallest_change_return_wit_1_split_goal_1.
Proof.
  pre_process; normalize_73; entailer!.
  match goal with
  | Hexit : ?idx >= Zlength ?l - 1 - ?idx |- problem_73_spec_z ?l (count_half_mismatches_upto ?idx ?l) =>
      eapply (problem_73_spec_z_of_exit l idx (count_half_mismatches_upto idx l));
      [lia | lia | exact Hexit | reflexivity]
  end.
Qed.

Lemma proof_of_smallest_change_return_wit_1 : smallest_change_return_wit_1.
Proof.
  right; intros.
  entailer!.
  rewrite PreH9.
  eapply (problem_73_spec_z_of_exit input_l i (count_half_mismatches_upto i input_l));
    [lia | lia | rewrite <- PreH4; exact PreH1 | reflexivity].
Qed.
