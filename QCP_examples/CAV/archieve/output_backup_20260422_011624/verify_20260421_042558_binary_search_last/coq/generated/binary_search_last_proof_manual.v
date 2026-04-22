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
From SimpleC.EE.CAV.verify_20260421_042558_binary_search_last Require Import binary_search_last_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma binary_search_last_quot2_bounds:
  forall x, 0 <= x -> 0 <= x ÷ 2 <= x.
Proof.
  intros x Hx.
  destruct (Z.eq_dec x 0) as [Hx0 | Hx0].
  - subst. change (0 ÷ 2) with 0. lia.
  - split.
    + apply Z.quot_pos; lia.
    + assert (x ÷ 2 < x) by (apply Z.quot_lt; lia).
      lia.
Qed.

Lemma binary_search_last_quot2_lt:
  forall x, 0 < x -> x ÷ 2 < x.
Proof.
  intros x Hx.
  apply Z.quot_lt; lia.
Qed.

Lemma proof_of_binary_search_last_safety_wit_2 : binary_search_last_safety_wit_2.
Proof.
  pre_process.
  prop_apply (store_int_range (&("left")) left).
  Intros.
  prop_apply (store_int_range (&("right")) right).
  Intros.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  assert (Hq: 0 <= (right - left) ÷ 2 <= right - left)
    by (apply binary_search_last_quot2_bounds; lia).
  entailer!.
Qed. 

Lemma proof_of_binary_search_last_entail_wit_1 : binary_search_last_entail_wit_1.
Proof. pre_process. Qed. 

Lemma proof_of_binary_search_last_entail_wit_2 : binary_search_last_entail_wit_2.
Proof.
  pre_process.
  assert (Hq: 0 <= (right - left) ÷ 2 <= right - left)
    by (apply binary_search_last_quot2_bounds; lia).
  assert (Hqlt: (right - left) ÷ 2 < right - left)
    by (apply binary_search_last_quot2_lt; lia).
  entailer!.
Qed. 

Lemma proof_of_binary_search_last_entail_wit_3 : binary_search_last_entail_wit_3.
Proof. pre_process. Qed. 

Lemma proof_of_binary_search_last_entail_wit_4_1 : binary_search_last_entail_wit_4_1.
Proof.
  pre_process.
  assert (Hupper_new:
    forall j, mid <= j < n_pre -> Znth j l 0 > target_pre).
  {
    intros j Hj.
    destruct (Z.eq_dec j mid) as [Heq | Hneq].
    - subst. lia.
    - assert (mid < j) by lia.
      assert (Hmono: Znth mid l 0 <= Znth j l 0).
      {
        match goal with
        | Hsorted: forall i k, _ -> Znth i l 0 <= Znth k l 0 |- _ =>
            apply (Hsorted mid j); lia
        end.
      }
      lia.
  }
  assert (Hpoint_new:
    (left = mid /\ left < n_pre) -> Znth left l 0 > target_pre).
  { intros [Heq Hlt]. subst. lia. }
  sep_apply store_int_undef_store_int.
  entailer!.
Qed. 

Lemma proof_of_binary_search_last_entail_wit_4_2 : binary_search_last_entail_wit_4_2.
Proof.
  pre_process.
  assert (Hlower_new:
    forall j, 0 <= j < mid + 1 -> Znth j l 0 <= target_pre).
  {
    intros j Hj.
    destruct (Z_lt_dec j left) as [Hjleft | Hnotleft].
    - match goal with
      | Hlower: forall q, 0 <= q /\ q < left -> Znth q l 0 <= target_pre |- _ =>
          apply Hlower; lia
      end.
    - assert (j <= mid) by lia.
      assert (Hmono: Znth j l 0 <= Znth mid l 0).
      {
        match goal with
        | Hsorted: forall i k, _ -> Znth i l 0 <= Znth k l 0 |- _ =>
            apply (Hsorted j mid); lia
        end.
      }
      lia.
  }
  assert (Hpoint_new:
    (mid + 1 = right /\ mid + 1 < n_pre) ->
      Znth (mid + 1) l 0 > target_pre).
  {
    intros [Heq Hlt].
    match goal with
    | Hupper: forall q, right <= q /\ q < n_pre -> Znth q l 0 > target_pre |- _ =>
        apply Hupper; lia
    end.
  }
  sep_apply store_int_undef_store_int.
  entailer!.
Qed. 

Lemma proof_of_binary_search_last_return_wit_2 : binary_search_last_return_wit_2.
Proof.
  pre_process.
  assert (Hlr: left = right) by lia.
  assert (Hlast_lt: Znth (left - 1) l 0 < target_pre).
  {
    assert (Hlast_le: Znth (left - 1) l 0 <= target_pre).
    {
      match goal with
      | Hlower: forall q, 0 <= q /\ q < left -> Znth q l 0 <= target_pre |- _ =>
          apply Hlower; lia
      end.
    }
    lia.
  }
  assert (Hnone:
    forall i, 0 <= i /\ i < n_pre -> Znth i l 0 <> target_pre).
  {
    intros i Hi.
    destruct (Z_lt_dec i left) as [Hilt | Hnotlt].
    - assert (Hmono: Znth i l 0 <= Znth (left - 1) l 0).
      {
        match goal with
        | Hsorted: forall p q, _ -> Znth p l 0 <= Znth q l 0 |- _ =>
            apply (Hsorted i (left - 1)); lia
        end.
      }
      lia.
    - match goal with
      | Hupper: forall q, right <= q /\ q < n_pre -> Znth q l 0 > target_pre |- _ =>
          specialize (Hupper i)
      end.
      lia.
  }
  right.
  entailer!.
  split.
  - hnf. lia.
  - split.
    + hnf. exact Hnone.
    + exact H15.
Qed. 
