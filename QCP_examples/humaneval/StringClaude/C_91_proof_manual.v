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
From SimpleC.EE Require Import C_91_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_91.
Local Open Scope sac.

Ltac bored_pre :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Ltac simplify_zeqb :=
  repeat match goal with
  | H : ?x = ?y |- context[Z.eqb ?x ?y] =>
      replace (Z.eqb x y) with true by (symmetry; apply Z.eqb_eq; lia)
  | H : ?x = ?y |- context[Z.eqb ?y ?x] =>
      replace (Z.eqb y x) with true by (symmetry; apply Z.eqb_eq; lia)
  | H : ?x <> ?y |- context[Z.eqb ?x ?y] =>
      replace (Z.eqb x y) with false by (symmetry; apply Z.eqb_neq; lia)
  | H : ?x <> ?y |- context[Z.eqb ?y ?x] =>
      replace (Z.eqb y x) with false by (symmetry; apply Z.eqb_neq; lia)
  | |- context[Z.eqb ?x ?x] =>
      replace (Z.eqb x x) with true by (symmetry; apply Z.eqb_eq; lia)
  end;
  simpl.

Ltac unfold_bored_step :=
  repeat rewrite bored_sum_prefix_step by lia;
  repeat rewrite bored_isstart_prefix_step by lia;
  repeat rewrite bored_isi_prefix_step by lia;
  unfold bored_add_z, bored_next_isstart_z, bored_next_isi_z,
         z_is_space, z_is_i, z_is_delim, zbool in *;
  simplify_zeqb.

Ltac solve_bored_step :=
  bored_pre;
  unfold_bored_step;
  entailer!;
  try lia.

Lemma proof_of_is_bored_entail_wit_1 : is_bored_entail_wit_1.
Proof.
  unfold is_bored_entail_wit_1.
  intros.
  bored_pre.
  unfold bored_sum_prefix_z, bored_isstart_prefix_z, bored_isi_prefix_z.
  simpl.
  entailer!.
Qed.

Lemma proof_of_is_bored_entail_wit_2_1 : is_bored_entail_wit_2_1.
Proof. unfold is_bored_entail_wit_2_1; intros; solve_bored_step. Qed.

Lemma proof_of_is_bored_entail_wit_2_2 : is_bored_entail_wit_2_2.
Proof. unfold is_bored_entail_wit_2_2; intros; solve_bored_step. Qed.

Lemma proof_of_is_bored_entail_wit_2_3 : is_bored_entail_wit_2_3.
Proof. unfold is_bored_entail_wit_2_3; intros; solve_bored_step. Qed.

Lemma proof_of_is_bored_entail_wit_2_4 : is_bored_entail_wit_2_4.
Proof. unfold is_bored_entail_wit_2_4; intros; solve_bored_step. Qed.

Lemma proof_of_is_bored_entail_wit_2_5 : is_bored_entail_wit_2_5.
Proof. unfold is_bored_entail_wit_2_5; intros; solve_bored_step. Qed.

Lemma proof_of_is_bored_entail_wit_2_6 : is_bored_entail_wit_2_6.
Proof. unfold is_bored_entail_wit_2_6; intros; solve_bored_step. Qed.

Lemma proof_of_is_bored_entail_wit_2_7 : is_bored_entail_wit_2_7.
Proof. unfold is_bored_entail_wit_2_7; intros; solve_bored_step. Qed.

Lemma proof_of_is_bored_entail_wit_2_8 : is_bored_entail_wit_2_8.
Proof. unfold is_bored_entail_wit_2_8; intros; solve_bored_step. Qed.

Lemma proof_of_is_bored_return_wit_1 : is_bored_return_wit_1.
Proof.
  unfold is_bored_return_wit_1.
  intros.
  bored_pre.
  assert (i = Zlength l) by lia.
  subst i.
  entailer!.
  eapply problem_91_spec_z_intro; eauto.
Qed.
