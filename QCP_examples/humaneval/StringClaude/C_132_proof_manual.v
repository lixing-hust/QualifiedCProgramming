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
From SimpleC.EE Require Import C_132_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_132.
Local Open Scope sac.

Lemma proof_of_is_nested_entail_wit_1 : is_nested_entail_wit_1.
Proof.
  unfold is_nested_entail_wit_1; intros.
  pre_process; subst retval; entailer!.
Qed.

Ltac solve_subseq_step :=
  pre_process; entailer!;
  match goal with
  | |- context[subseq_state_prefix_z (?i + 1) ?l] =>
      rewrite (subseq_state_prefix_step l i) by lia
  end;
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | H : ?state = subseq_state_prefix_z ?i ?l |- _ => rewrite <- H
  end;
  unfold subseq_step_z;
  repeat match goal with
  | |- context[Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); subst; try lia
  end;
  lia.

Ltac solve_return_prefix :=
  pre_process; entailer!;
  match goal with
  | Hge : ?i >= ?len, Hle : ?i <= ?len |- _ =>
      assert (i = len) by lia; subst i
  end.

Lemma proof_of_is_nested_entail_wit_2_1 : is_nested_entail_wit_2_1.
Proof.
  unfold is_nested_entail_wit_2_1; intros; solve_subseq_step.
Qed.

Lemma proof_of_is_nested_entail_wit_2_2 : is_nested_entail_wit_2_2.
Proof.
  unfold is_nested_entail_wit_2_2; intros; solve_subseq_step.
Qed.

Lemma proof_of_is_nested_entail_wit_2_3 : is_nested_entail_wit_2_3.
Proof.
  unfold is_nested_entail_wit_2_3; intros; solve_subseq_step.
Qed.

Lemma proof_of_is_nested_entail_wit_2_4 : is_nested_entail_wit_2_4.
Proof.
  unfold is_nested_entail_wit_2_4; intros; solve_subseq_step.
Qed.

Lemma proof_of_is_nested_entail_wit_2_5 : is_nested_entail_wit_2_5.
Proof.
  unfold is_nested_entail_wit_2_5; intros; solve_subseq_step.
Qed.

Lemma proof_of_is_nested_entail_wit_2_6 : is_nested_entail_wit_2_6.
Proof.
  unfold is_nested_entail_wit_2_6; intros; solve_subseq_step.
Qed.

Lemma proof_of_is_nested_entail_wit_2_7 : is_nested_entail_wit_2_7.
Proof.
  unfold is_nested_entail_wit_2_7; intros; solve_subseq_step.
Qed.

Lemma proof_of_is_nested_entail_wit_2_8 : is_nested_entail_wit_2_8.
Proof.
  unfold is_nested_entail_wit_2_8; intros; solve_subseq_step.
Qed.

Lemma proof_of_is_nested_entail_wit_2_9 : is_nested_entail_wit_2_9.
Proof.
  unfold is_nested_entail_wit_2_9; intros.
  pre_process; entailer!.
  assert (state = 4) by lia; subst state.
  rewrite (subseq_state_prefix_step l i) by lia.
  repeat rewrite app_Znth1 in * by lia.
  match goal with
  | H : 4 = subseq_state_prefix_z i l |- _ => rewrite <- H
  | H : subseq_state_prefix_z i l = 4 |- _ => rewrite H
  end.
  unfold subseq_step_z; reflexivity.
Qed.

Lemma proof_of_is_nested_return_wit_1 : is_nested_return_wit_1.
Proof.
  unfold is_nested_return_wit_1; intros.
  solve_return_prefix.
  apply problem_132_spec_z_false; auto.
  intro Hbad.
  replace (Zlength l) with len in Hbad by lia.
  match goal with
  | Hstate : state = subseq_state_prefix_z len l,
    Hneq : state <> 4 |- _ =>
      rewrite <- Hstate in Hbad; contradiction
  end.
Qed.

Lemma proof_of_is_nested_return_wit_2 : is_nested_return_wit_2.
Proof.
  unfold is_nested_return_wit_2; intros.
  solve_return_prefix.
  apply problem_132_spec_z_true; auto.
  replace (Zlength l) with len by lia.
  match goal with
  | Hstate : state = subseq_state_prefix_z len l,
    Hstate4 : state = 4 |- _ =>
      rewrite <- Hstate; exact Hstate4
  end.
Qed.
