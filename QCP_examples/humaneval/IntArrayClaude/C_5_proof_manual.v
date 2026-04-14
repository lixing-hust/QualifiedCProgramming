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
From SimpleC.EE Require Import C_5_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_5.
Local Open Scope sac.

Lemma proof_of_intersperse_entail_wit_1 : intersperse_entail_wit_1.
Proof.
  pre_process.
  subst.
  prop_apply (IntArray.full_length numbers0). Intros.
  rewrite intersperse_list_sublist_one by lia.
  sep_apply (IntArray.seg_single out0 0 (Znth 0 input_l 0)).
  entailer!.
Qed.

Lemma proof_of_intersperse_entail_wit_2 : intersperse_entail_wit_2.
Proof.
  pre_process.
  prop_apply (IntArray.full_length numbers0). Intros.
  rewrite intersperse_list_sublist_snoc by lia.
  sep_apply (IntArray.seg_single out0 k delimeter0).
  sep_apply (IntArray.seg_single out0 (k + 1) (Znth i input_l 0)).
  sep_apply (IntArray.seg_merge_to_seg out0 0 k (k + 1)); [ | lia].
  sep_apply (IntArray.seg_merge_to_seg out0 0 (k + 1) ((k + 1) + 1)); [ | lia].
  rewrite <- app_assoc.
  entailer!.
Qed.

Lemma proof_of_intersperse_return_wit_1 : intersperse_return_wit_1.
Proof.
  pre_process.
  subst.
  prop_apply (IntArray.full_length numbers0). Intros.
  Exists (@nil Z).
  rewrite IntArray.undef_full_empty.
  rewrite (IntArray.full_empty out0 0).
  entailer!.
  unfold problem_5_spec; split; intros; auto; lia.
Qed.

Lemma proof_of_intersperse_return_wit_2 : intersperse_return_wit_2.
Proof.
  pre_process.
  assert (Hi : i = numbers_size0) by lia.
  subst i.
  assert (Hk : k = out_size0) by lia.
  prop_apply (IntArray.full_length numbers0).
  entailer!.
  assert (Hsl : sublist 0 numbers_size0 input_l = input_l).
  {
    apply sublist_self.
    rewrite Zlength_correct.
    match goal with
    | Hlen : Z.of_nat (Datatypes.length input_l) = numbers_size0 |- _ =>
        symmetry; exact Hlen
    end.
  }
  rewrite Hsl.
  rewrite <- Hk.
  Exists (intersperse_list input_l delimeter0).
  sep_apply (IntArray.seg_to_full out0 0 k).
  replace (out0 + 0 * sizeof (INT)) with out0 by lia.
  replace (k - 0) with k by lia.
  rewrite Hk.
  rewrite (IntArray.undef_seg_empty out0 out_size0).
  entailer!.
  apply problem_5_spec_intersperse_list.
Qed.
