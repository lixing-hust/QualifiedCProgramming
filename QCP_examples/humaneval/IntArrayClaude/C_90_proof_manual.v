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
From SimpleC.EE Require Import C_90_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_90.
Local Open Scope sac.

Lemma proof_of_next_smallest_entail_wit_1 : next_smallest_entail_wit_1.
Proof.
  pre_process.
  sep_apply (IntArray.full_to_seg lst_pre lst_size_pre input_l).
  rewrite (IntArray.undef_seg_empty lst_pre lst_size_pre).
  entailer!.
Qed.

Lemma proof_of_next_smallest_entail_wit_2 : next_smallest_entail_wit_2.
Proof.
  pre_process.
  assert (sorted_full_l = sorted_l_2).
  {
    rewrite <- H1.
    replace lst_size_pre with (Zlength sorted_full_l) by lia.
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  subst sorted_full_l.
  assert (next_smallest_sorted_bridge input_l sorted_l_2 lst_size_pre).
  {
    apply next_smallest_sorted_bridge_of_sorted; assumption.
  }
  Exists sorted_l_2.
  entailer!.
  apply no_distinct_prefix_1.
Qed.

Lemma proof_of_next_smallest_entail_wit_3 : next_smallest_entail_wit_3.
Proof.
  pre_process.
  Exists sorted_l_2.
  assert (no_distinct_prefix (i + 1) sorted_l_2).
  {
    apply no_distinct_prefix_step; try assumption; lia.
  }
  entailer!.
Qed.

Lemma proof_of_next_smallest_return_wit_1 : next_smallest_return_wit_1.
Proof.
  pre_process.
  assert (problem_90_spec_z input_l (-1)).
  {
    match goal with
    | Hbridge : next_smallest_sorted_bridge input_l sorted_l lst_size_pre |- _ =>
        destruct Hbridge as [_ Hnone];
        apply Hnone;
        replace i with lst_size_pre in * by lia;
        assumption
    end.
  }
  Exists sorted_l.
  entailer!.
Qed.

Lemma proof_of_next_smallest_return_wit_2 : next_smallest_return_wit_2.
Proof.
  pre_process.
  assert (problem_90_spec_z input_l (Znth i sorted_l 0)).
  {
    match goal with
    | Hbridge : next_smallest_sorted_bridge input_l sorted_l lst_size_pre |- _ =>
        destruct Hbridge as [Hfound _];
        apply Hfound; try assumption; lia
    end.
  }
  Exists sorted_l.
  entailer!.
Qed.

Lemma proof_of_next_smallest_return_wit_3 : next_smallest_return_wit_3.
Proof.
  pre_process.
  assert (problem_90_spec_z input_l (-1)).
  {
    apply problem_90_spec_z_short.
    lia.
  }
  Exists input_l.
  entailer!.
Qed.
