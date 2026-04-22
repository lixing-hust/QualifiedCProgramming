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
From SimpleC.EE Require Import C_43_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_43.
Local Open Scope sac.

Lemma proof_of_pairs_sum_to_zero_safety_wit_4 : pairs_sum_to_zero_safety_wit_4.
Proof.
  pre_process.
  assert (Hij : 0 <= i < j) by lia.
  assert (Hjn : j < l_size_pre) by lia.
  match goal with
  | H: pair_sum_int_range input_l l_size_pre |- _ =>
      pose proof (H i j Hij Hjn) as Hsum
  end.
  andp_cancel; lia.
Qed.

Lemma proof_of_pairs_sum_to_zero_entail_wit_1 : pairs_sum_to_zero_entail_wit_1.
Proof.
  pre_process.
  andp_cancel; auto; try lia; try apply scanned_i_init.
Qed.

Lemma proof_of_pairs_sum_to_zero_entail_wit_2 : pairs_sum_to_zero_entail_wit_2.
Proof.
  pre_process.
  andp_cancel; auto; try lia.
  apply scanned_j_init.
  assumption.
Qed.

Lemma proof_of_pairs_sum_to_zero_entail_wit_3 : pairs_sum_to_zero_entail_wit_3.
Proof.
  pre_process.
  assert (Hnext : scanned_i input_l l_size_pre (i + 1)).
  { apply scanned_i_step with (j := j); auto; lia. }
  andp_cancel; auto; try lia.
  sep_apply store_int_undef_store_int.
  andp_cancel; auto; try lia.
Qed.

Lemma proof_of_pairs_sum_to_zero_entail_wit_4 : pairs_sum_to_zero_entail_wit_4.
Proof.
  pre_process.
  assert (Hnext : scanned_j input_l l_size_pre i (j + 1)).
  { apply scanned_j_step.
    - assumption.
    - unfold pair_sum_zero.
      lia. }
  andp_cancel; auto; try lia.
Qed.

Lemma proof_of_pairs_sum_to_zero_return_wit_1 : pairs_sum_to_zero_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_Zlength l_pre). Intros.
  Left.
  andp_cancel; auto; try lia.
  apply problem_43_spec_false_of_scanned_i with (n := l_size_pre) (limit := i);
    auto; lia.
Qed.

Lemma proof_of_pairs_sum_to_zero_return_wit_2 : pairs_sum_to_zero_return_wit_2.
Proof.
  pre_process.
  prop_apply (IntArray.full_Zlength l_pre). Intros.
  Right.
  andp_cancel; auto; try lia.
  apply problem_43_spec_true_of_pair with (n := l_size_pre) (i := i) (j := j);
    auto; try lia.
Qed.
