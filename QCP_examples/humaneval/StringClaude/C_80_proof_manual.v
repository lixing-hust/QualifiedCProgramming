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
From SimpleC.EE Require Import C_80_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_80.
Local Open Scope sac.

Lemma proof_of_is_happy_entail_wit_1 : is_happy_entail_wit_1.
Proof.
  unfold is_happy_entail_wit_1.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  subst retval.
  entailer!.
  - apply happy_adjacent_z_2.
    match goal with
    | H : Znth 0 l 0 <> Znth 1 l 0 |- _ =>
        intro Heq; apply H; symmetry; exact Heq
    end.
  - apply happy_prefix_z_2.
Qed.

Lemma proof_of_is_happy_entail_wit_2 : is_happy_entail_wit_2.
Proof.
  unfold is_happy_entail_wit_2.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  entailer!.
  - apply happy_adjacent_z_step.
    match goal with
    | H : Znth i l 0 <> Znth (i - 1) l 0 |- _ => exact H
    end.
  - apply happy_prefix_z_step.
    + assumption.
    + assumption.
    + match goal with
      | H : Znth i l 0 <> Znth (i - 1) l 0 |- _ => exact H
      end.
    + match goal with
      | H : Znth i l 0 <> Znth (i - 2) l 0 |- _ => exact H
      end.
Qed.

Lemma proof_of_is_happy_return_wit_1 : is_happy_return_wit_1.
Proof.
  unfold is_happy_return_wit_1.
  intros.
  pre_process.
  entailer!.
  apply problem_80_spec_z_true with (i := i); auto; lia.
Qed.

Lemma proof_of_is_happy_return_wit_2 : is_happy_return_wit_2.
Proof.
  unfold is_happy_return_wit_2.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  entailer!.
  apply problem_80_spec_z_false_prev2 with (i := i); auto; lia.
Qed.

Lemma proof_of_is_happy_return_wit_3 : is_happy_return_wit_3.
Proof.
  unfold is_happy_return_wit_3.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  entailer!.
  apply problem_80_spec_z_false_prev1 with (i := i); auto; lia.
Qed.

Lemma proof_of_is_happy_return_wit_4 : is_happy_return_wit_4.
Proof.
  unfold is_happy_return_wit_4.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  subst retval.
  entailer!.
  apply problem_80_spec_z_false_first_pair; try lia.
Qed.

Lemma proof_of_is_happy_return_wit_5 : is_happy_return_wit_5.
Proof.
  unfold is_happy_return_wit_5.
  intros.
  pre_process.
  subst retval.
  entailer!.
  apply problem_80_spec_z_short.
  lia.
Qed.
