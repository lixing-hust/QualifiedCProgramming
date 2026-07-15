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
From SimpleC.EE Require Import C_85_goal.
From SimpleC.EE Require Import C_85_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_85.
Local Open Scope sac.

Ltac normalize_85 :=
  subst;
  repeat match goal with
  | H : context[2147483647 ÷ 2] |- _ =>
      change (2147483647 ÷ 2) with 1073741823 in H
  | |- context[2147483647 ÷ 2] =>
      change (2147483647 ÷ 2) with 1073741823
  end;
  repeat match goal with
  | H : context[(?i * 2) + 1] |- _ =>
      replace (i * 2 + 1) with (2 * i + 1) in H by lia
  | |- context[(?i * 2) + 1] =>
      replace (i * 2 + 1) with (2 * i + 1) by lia
  end;
  repeat match goal with
  | Hrem : Z.rem (Znth (2 * ?i + 1) ?l 0) 2 = 0
    |- context[add_prefix_sum_85 (?i + 1) ?l] =>
      rewrite (add_prefix_sum_85_step_even l i ltac:(lia) Hrem)
  | Hrem : Z.rem (Znth (2 * ?i + 1) ?l 0) 2 = 0,
    H : context[add_prefix_sum_85 (?i + 1) ?l] |- _ =>
      rewrite (add_prefix_sum_85_step_even l i ltac:(lia) Hrem) in H
  | Hrem : Z.rem (Znth (2 * ?i + 1) ?l 0) 2 <> 0
    |- context[add_prefix_sum_85 (?i + 1) ?l] =>
      rewrite (add_prefix_sum_85_step_odd l i ltac:(lia) Hrem)
  | Hrem : Z.rem (Znth (2 * ?i + 1) ?l 0) 2 <> 0,
    H : context[add_prefix_sum_85 (?i + 1) ?l] |- _ =>
      rewrite (add_prefix_sum_85_step_odd l i ltac:(lia) Hrem) in H
  | |- context[add_prefix_sum_85 0 ?l] =>
      rewrite (add_prefix_sum_85_0 l)
  | H : context[add_prefix_sum_85 0 ?l] |- _ =>
      rewrite (add_prefix_sum_85_0 l) in H
  end.

Ltac solve_85_pures :=
  normalize_85;
  try match goal with
  | Hrange : add_sum_int_range_85 ?l,
    Hi : 0 <= ?i,
    Hlt : 2 * ?i + 1 < Zlength ?l |- _ =>
      let H := fresh "Hrange_step" in
      pose proof (add_prefix_sum_85_nonneg_range l i Hrange Hi Hlt) as H;
      destruct H as (? & ? & ?)
  | Hrange : add_sum_int_range_85 ?l,
    Hi : 0 <= ?i,
    Hle : 2 * ?i <= Zlength ?l,
    Hexit : 2 * ?i + 1 >= Zlength ?l |- _ =>
      let H := fresh "Hrange_exit" in
      pose proof (add_prefix_sum_85_exit_range l i Hrange Hi Hle Hexit) as H
  end;
  normalize_85;
  repeat match goal with
  | |- (_ && _) _ => split
  end;
  try assumption;
  try reflexivity;
  try unfold INT_MIN_85 in *;
  try lia;
  repeat match goal with
  | |- coq_prop _ _ => unfold coq_prop; simpl; solve_85_pures
  end.

Ltac solve_85_vc :=
  try (right; intros);
  pre_process; normalize_85; entailer!;
  try solve_85_pures.

Lemma proof_of_add_safety_wit_3 : add_safety_wit_3.
Proof.
  right; intros.
  pre_process; normalize_85; entailer!; lia.
Qed.

Lemma proof_of_add_safety_wit_14 : add_safety_wit_14.
Proof. solve_85_vc. Qed.

Lemma proof_of_add_entail_wit_1 : add_entail_wit_1.
Proof. solve_85_vc. Qed.

Lemma proof_of_add_entail_wit_2_1 : add_entail_wit_2_1.
Proof. solve_85_vc. Qed.

Lemma proof_of_add_entail_wit_2_2 : add_entail_wit_2_2.
Proof. solve_85_vc. Qed.

Lemma proof_of_add_return_wit_1 : add_return_wit_1.
Proof.
  right; intros.
  entailer!.
  rewrite PreH9.
  replace (i * 2 + 1) with (2 * i + 1) in PreH1 by lia.
  eapply problem_85_spec_z_of_exit.
  - exact PreH7.
  - rewrite <- PreH4. exact PreH8.
  - rewrite <- PreH4. exact PreH1.
  - reflexivity.
Qed.
