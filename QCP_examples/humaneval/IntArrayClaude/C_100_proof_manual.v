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
From SimpleC.EE Require Import C_100_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_100.
Local Open Scope sac.

Lemma proof_of_make_a_pile_safety_wit_3 : make_a_pile_safety_wit_3.
Proof.
  pre_process.
  match goal with
  | H: pile_int_range n0 |- _ => pose proof (H i ltac:(lia))
  end.
  entailer!.
Qed. 

Lemma proof_of_make_a_pile_safety_wit_4 : make_a_pile_safety_wit_4.
Proof.
  pre_process.
  match goal with
  | H: pile_int_range n0 |- _ => pose proof (H i ltac:(lia))
  end.
  entailer!.
Qed. 

Lemma proof_of_make_a_pile_entail_wit_1 : make_a_pile_entail_wit_1.
Proof.
  pre_process.
  subst.
  rewrite sublist_nil by lia.
  simpl.
  sep_apply IntArray.undef_full_to_undef_seg.
  entailer!.
  rewrite IntArray.seg_empty.
  entailer!.
  apply make_pile_Zlength.
  lia.
Qed. 

Lemma proof_of_make_a_pile_entail_wit_2 : make_a_pile_entail_wit_2.
Proof.
  pre_process.
  rewrite make_pile_sublist_snoc by lia.
  sep_apply (IntArray.seg_single data i (n0 + 2 * i)).
  sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)); [ | lia].
  entailer!.
Qed. 

Lemma proof_of_make_a_pile_return_wit_1 : make_a_pile_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = n0) by lia.
  subst i.
  Exists (make_pile n0) n0 data_2.
  rewrite sublist_self by lia.
  sep_apply (IntArray.seg_to_full data_2 0 n0).
  replace (data_2 + 0 * sizeof (INT)) with data_2 by lia.
  replace (n0 - 0) with n0 by lia.
  rewrite (IntArray.undef_seg_empty data_2 n0).
  entailer!.
  apply problem_100_spec_z_make_pile.
  lia.
Qed. 
