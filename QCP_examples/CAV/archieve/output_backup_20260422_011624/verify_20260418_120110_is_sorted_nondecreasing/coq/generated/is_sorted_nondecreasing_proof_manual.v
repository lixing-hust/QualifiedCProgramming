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
From SimpleC.EE.CAV.verify_20260418_120110_is_sorted_nondecreasing Require Import is_sorted_nondecreasing_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_is_sorted_nondecreasing_entail_wit_1 : is_sorted_nondecreasing_entail_wit_1.
Proof.
  unfold is_sorted_nondecreasing_entail_wit_1.
  intros.
  entailer!.
Qed.

Lemma proof_of_is_sorted_nondecreasing_entail_wit_4 : is_sorted_nondecreasing_entail_wit_4.
Proof.
  unfold is_sorted_nondecreasing_entail_wit_4.
  intros.
  entailer!.
  intros j Hj.
  apply H.
  lia.
Qed.

Lemma proof_of_is_sorted_nondecreasing_return_wit_2 : is_sorted_nondecreasing_return_wit_2.
Proof.
  unfold is_sorted_nondecreasing_return_wit_2.
  intros.
  Intros.
  right.
  entailer!.
Qed.
