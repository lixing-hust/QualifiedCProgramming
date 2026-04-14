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
From SimpleC.EE Require Import C_3_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_3.
Local Open Scope sac.

Lemma proof_of_below_zero_safety_wit_3 : below_zero_safety_wit_3.
Proof.
  pre_process.
  subst num.
  rewrite sum_sublist_snoc by lia.
  entailer!.
  all: match goal with
  | H: prefix_sums_int_range _ _ |- _ =>
      unfold prefix_sums_int_range in H;
      specialize (H (i + 1)); lia
  end.
Qed.

Lemma proof_of_below_zero_entail_wit_1 : below_zero_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_below_zero_entail_wit_2 : below_zero_entail_wit_2.
Proof.
  pre_process.
  subst num.
  assert (Hstep: sum (sublist 0 i l) + Znth i l 0 =
                 sum (sublist 0 (i + 1) l)).
  { apply sum_sublist_snoc. lia. }
  entailer!.
  intros k Hk.
  destruct (Z_lt_ge_dec k i).
  - match goal with
    | H: forall k, 0 <= k < i -> 0 <= sum (sublist 0 (k + 1) l) |- _ =>
        apply H; lia
    end.
  - assert (k = i) by lia.
    subst k.
    rewrite <- Hstep. lia.
Qed.

Lemma proof_of_below_zero_return_wit_1 : below_zero_return_wit_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  apply problem_3_spec_true_of_negative_prefix with (k := i).
  - lia.
  - subst num.
    rewrite <- sum_sublist_snoc by lia.
    lia.
Qed.

Lemma proof_of_below_zero_return_wit_2 : below_zero_return_wit_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  entailer!.
  apply problem_3_spec_false_of_all_prefix_nonneg.
  intros k Hk.
  match goal with
  | H: forall k, 0 <= k < i -> 0 <= sum (sublist 0 (k + 1) l) |- _ =>
      apply H; lia
  end.
Qed.
