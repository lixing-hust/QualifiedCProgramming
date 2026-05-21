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
From SimpleC.EE Require Import C_54_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_54.
Local Open Scope sac.

Ltac same_chars_pre :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Lemma proof_of_same_chars_entail_wit_1 : same_chars_entail_wit_1.
Proof.
  unfold same_chars_entail_wit_1.
  intros.
  same_chars_pre.
  entailer!.
  apply same_chars_prefix_zero.
Qed. 

Lemma proof_of_same_chars_entail_wit_2 : same_chars_entail_wit_2.
Proof.
  unfold same_chars_entail_wit_2.
  intros.
  same_chars_pre.
  entailer!.
  apply same_chars_prefix_step; try lia.
  assumption.
  assumption.
Qed. 

Lemma proof_of_same_chars_entail_wit_3 : same_chars_entail_wit_3.
Proof.
  unfold same_chars_entail_wit_3.
  intros.
  same_chars_pre.
  assert (i = Zlength l0) by lia.
  subst i.
  entailer!.
  - apply same_chars_prefix_zero.
  - pose proof (Zlength_nonneg l1); lia.
Qed. 

Lemma proof_of_same_chars_entail_wit_4 : same_chars_entail_wit_4.
Proof.
  unfold same_chars_entail_wit_4.
  intros.
  same_chars_pre.
  entailer!.
  apply same_chars_prefix_step; try lia.
  assumption.
  assumption.
Qed. 

Lemma proof_of_same_chars_return_wit_1 : same_chars_return_wit_1.
Proof.
  unfold same_chars_return_wit_1.
  intros.
  same_chars_pre.
  assert (i = Zlength l1) by lia.
  subst i.
  entailer!.
  apply problem_54_spec_z_true; assumption.
Qed. 

Lemma proof_of_same_chars_return_wit_2 : same_chars_return_wit_2.
Proof.
  unfold same_chars_return_wit_2.
  intros.
  same_chars_pre.
  entailer!.
  apply problem_54_spec_z_false_right with (i := i); try lia; try assumption.
Qed. 

Lemma proof_of_same_chars_return_wit_3 : same_chars_return_wit_3.
Proof.
  unfold same_chars_return_wit_3.
  intros.
  same_chars_pre.
  entailer!.
  apply problem_54_spec_z_false_left with (i := i); try lia; try assumption.
Qed. 
