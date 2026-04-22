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
From SimpleC.EE Require Import C_52_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_52.
Local Open Scope sac.

Lemma proof_of_below_threshold_entail_wit_2 : below_threshold_entail_wit_2.
Proof.
  pre_process.
  andp_cancel; auto; try lia.
  intros k Hk.
  assert (k < i \/ k = i) as [Hlt | ->] by lia.
  - match goal with
    | H: forall k, 0 <= k < i -> Znth k input_l 0 < t_pre |- _ =>
        apply H; lia
    end.
  - assumption.
Qed.

Lemma proof_of_below_threshold_return_wit_1 : below_threshold_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_Zlength l_pre). Intros.
  Right.
  andp_cancel; auto; try lia.
  apply problem_52_spec_true_of_all_below with (n := l_size_pre); auto.
  intros k Hk.
  match goal with
  | H: forall k, 0 <= k < i -> Znth k input_l 0 < t_pre |- _ =>
      apply H; lia
  end.
Qed.

Lemma proof_of_below_threshold_return_wit_2 : below_threshold_return_wit_2.
Proof.
  pre_process.
  prop_apply (IntArray.full_Zlength l_pre). Intros.
  Left.
  andp_cancel; auto; try lia.
  apply problem_52_spec_false_of_counter with (n := l_size_pre) (i := i);
    auto; lia.
Qed.
