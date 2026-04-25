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
From SimpleC.EE Require Import C_106_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_106.
Local Open Scope sac.

Lemma proof_of_f_safety_wit_4 : f_safety_wit_4.
Proof.
  pre_process.
  subst s.
  match goal with
  | H: f_seq_int_range n0 |- _ => pose proof (H (i + 1) ltac:(lia)) as Hrange
  end.
  rewrite <- triangular_z_step by lia.
  entailer!.
Qed. 

Lemma proof_of_f_safety_wit_7 : f_safety_wit_7.
Proof.
  pre_process.
  subst p.
  match goal with
  | H: f_seq_int_range n0 |- _ => pose proof (H (i + 1) ltac:(lia)) as Hrange
  end.
  rewrite <- factorial_z_step by lia.
  entailer!.
Qed. 

Lemma proof_of_f_entail_wit_1 : f_entail_wit_1.
Proof.
  pre_process.
  subst.
  rewrite f_seq_Zlength by lia.
  rewrite triangular_z_0.
  rewrite factorial_z_0.
  rewrite sublist_nil by lia.
  simpl.
  sep_apply IntArray.undef_full_to_undef_seg.
  entailer!.
  rewrite IntArray.seg_empty.
  entailer!.
Qed. 

Lemma proof_of_f_entail_wit_2_1 : f_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hsnext : s + (i + 1) = triangular_z (i + 1)).
  { subst s. symmetry. apply triangular_z_step. lia. }
  assert (Hpnext : p * (i + 1) = factorial_z (i + 1)).
  { subst p. symmetry. apply factorial_z_step. lia. }
  rewrite f_seq_sublist_snoc by lia.
  replace (p * (i + 1)) with (f_elem (i + 1)).
  2:{
    rewrite Hpnext.
    apply f_elem_even_rem.
    assumption.
  }
  sep_apply (IntArray.seg_single data i (f_elem (i + 1))).
  sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)); [ | lia].
  andp_cancel; auto; try lia.
  apply f_elem_even_rem.
  assumption.
Qed. 

Lemma proof_of_f_entail_wit_2_2 : f_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hsnext : s + (i + 1) = triangular_z (i + 1)).
  { subst s. symmetry. apply triangular_z_step. lia. }
  assert (Hpnext : p * (i + 1) = factorial_z (i + 1)).
  { subst p. symmetry. apply factorial_z_step. lia. }
  rewrite f_seq_sublist_snoc by lia.
  replace (s + (i + 1)) with (f_elem (i + 1)).
  2:{
    rewrite Hsnext.
    apply f_elem_odd_rem.
    assumption.
  }
  sep_apply (IntArray.seg_single data i (f_elem (i + 1))).
  sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)); [ | lia].
  andp_cancel; auto; try lia.
  apply f_elem_odd_rem.
  assumption.
Qed. 

Lemma proof_of_f_return_wit_1 : f_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = n0) by lia.
  subst i.
  Exists (f_seq n0) n0 data_2.
  rewrite sublist_self by lia.
  sep_apply (IntArray.seg_to_full data_2 0 n0).
  replace (data_2 + 0 * sizeof (INT)) with data_2 by lia.
  replace (n0 - 0) with n0 by lia.
  rewrite (IntArray.undef_seg_empty data_2 n0).
  entailer!.
  apply problem_106_spec_z_f_seq.
  lia.
Qed. 
