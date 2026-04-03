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
From SimpleC.EE Require Import C_97_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_97.
Local Open Scope sac.

Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof.
  unfold abs_return_wit_1.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof.
  unfold abs_return_wit_2.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_multiply_safety_wit_1 : multiply_safety_wit_1.
Proof.
  unfold multiply_safety_wit_1.
  intros.
  Intros.
  entailer!.
  pose proof (Z.abs_nonneg a_pre) as Hna.
  pose proof (Z.abs_nonneg b_pre) as Hnb.
  assert (Ha: 0 <= retval mod 10 < 10) by (apply Z.mod_pos_bound; lia).
  assert (Hb: 0 <= retval_2 mod 10 < 10) by (apply Z.mod_pos_bound; lia).
  apply Z.mul_nonneg_nonneg; lia.
Qed.

Lemma proof_of_multiply_return_wit_1 : multiply_return_wit_1.
Proof.
  unfold multiply_return_wit_1.
  intros.
  Intros.
  entailer!.
  unfold problem_97_spec.
  subst.
  reflexivity.
Qed.

