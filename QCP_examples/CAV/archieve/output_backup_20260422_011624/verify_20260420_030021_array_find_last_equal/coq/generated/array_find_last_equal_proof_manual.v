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
From SimpleC.EE.CAV.verify_20260420_030021_array_find_last_equal Require Import array_find_last_equal_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_find_last_equal_entail_wit_1 : array_find_last_equal_entail_wit_1.
Proof.
  unfold array_find_last_equal_entail_wit_1.
  intros.
  entailer!.
Qed.

Lemma proof_of_array_find_last_equal_entail_wit_3 : array_find_last_equal_entail_wit_3.
Proof.
  unfold array_find_last_equal_entail_wit_3.
  intros.
  entailer!.
  all: assert (i = n_pre) by lia; subst i.
  - intros j Hj.
    apply H6.
    exact Hj.
  - intro Hans.
    intros j Hj.
    apply H4.
    + exact Hans.
    + exact Hj.
Qed.

Lemma proof_of_array_find_last_equal_return_wit_1 : array_find_last_equal_return_wit_1.
Proof.
  unfold array_find_last_equal_return_wit_1.
  pre_process.
  destruct (Z.eq_dec ans (-1)) as [Hans | Hans].
  - subst ans.
    right.
    entailer!.
    unfold andp, coq_prop; simpl.
    repeat split; auto.
  - assert (0 <= ans) by lia.
    left.
    entailer!.
    unfold andp, coq_prop; simpl.
    repeat split; auto.
Qed.
