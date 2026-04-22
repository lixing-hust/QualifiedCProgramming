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
From SimpleC.EE.CAV.verify_20260420_231624_binary_search Require Import binary_search_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma binary_search_quot2_bounds:
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

Lemma binary_search_sorted_adjacent_mono:
  forall (l: list Z) n i j,
    Zlength l = n ->
    (forall k, 0 <= k /\ k + 1 < n -> Znth k l 0 <= Znth (k + 1) l 0) ->
    0 <= i ->
    i <= j ->
    j < n ->
    Znth i l 0 <= Znth j l 0.
Proof.
  intros l n i j Hlen Hsorted Hi Hij Hj.
  assert (Hmono_nat:
    forall k p,
      0 <= p ->
      p + Z.of_nat k < n ->
      Znth p l 0 <= Znth (p + Z.of_nat k) l 0).
  {
    induction k; intros p Hp Hpk.
    - replace (p + Z.of_nat 0) with p by lia.
      lia.
    - replace (p + Z.of_nat (S k)) with ((p + Z.of_nat k) + 1) by lia.
      assert (Hleft: Znth p l 0 <= Znth (p + Z.of_nat k) l 0).
      { apply IHk; lia. }
      assert (Hstep: Znth (p + Z.of_nat k) l 0 <=
                     Znth ((p + Z.of_nat k) + 1) l 0).
      { apply Hsorted; lia. }
      lia.
  }
  replace j with (i + Z.of_nat (Z.to_nat (j - i))).
  - apply Hmono_nat; lia.
  - rewrite Z2Nat.id by lia.
    lia.
Qed.

Lemma proof_of_binary_search_safety_wit_4 : binary_search_safety_wit_4.
Proof.
  pre_process.
  prop_apply (store_int_range (&("left")) left).
  Intros.
  prop_apply (store_int_range (&("right")) right).
  Intros.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  assert (Hq: 0 <= (right - left) ÷ 2 <= right - left)
    by (apply binary_search_quot2_bounds; lia).
  entailer!.
Qed. 

Lemma proof_of_binary_search_entail_wit_1 : binary_search_entail_wit_1.
Proof. pre_process. Qed. 

Lemma proof_of_binary_search_entail_wit_2 : binary_search_entail_wit_2.
Proof.
  pre_process.
  assert (Hq: 0 <= (right - left) ÷ 2 <= right - left)
    by (apply binary_search_quot2_bounds; lia).
  entailer!.
Qed. 

Lemma proof_of_binary_search_entail_wit_3 : binary_search_entail_wit_3.
Proof. pre_process. Qed. 

Lemma proof_of_binary_search_entail_wit_4 : binary_search_entail_wit_4.
Proof. pre_process. Qed. 

Lemma proof_of_binary_search_entail_wit_5_1 : binary_search_entail_wit_5_1.
Proof.
  pre_process.
  assert (Hupper_new:
    forall j, mid - 1 < j < n_pre -> target_pre < Znth j l 0).
  {
    intros j Hj.
    destruct (Z.eq_dec j mid) as [Heq | Hneqj].
    - subst. lia.
    - assert (mid < j) by lia.
      assert (Hmono: Znth mid l 0 <= Znth j l 0).
      {
        match goal with
        | Hlen: Zlength l = n_pre,
          Hsorted: forall k, 0 <= k /\ k + 1 < n_pre ->
                             Znth k l 0 <= Znth (k + 1) l 0 |- _ =>
            apply (binary_search_sorted_adjacent_mono l n_pre mid j);
            try exact Hlen; try exact Hsorted; lia
        end.
      }
      lia.
  }
  sep_apply store_int_undef_store_int.
  entailer!.
Qed. 

Lemma proof_of_binary_search_entail_wit_5_2 : binary_search_entail_wit_5_2.
Proof.
  pre_process.
  assert (Hlower_new:
    forall j, 0 <= j < mid + 1 -> Znth j l 0 < target_pre).
  {
    intros j Hj.
    destruct (Z_lt_dec j left) as [Hjleft | Hnotleft].
    - match goal with
      | Hlower: forall q, 0 <= q /\ q < left -> Znth q l 0 < target_pre |- _ =>
          apply Hlower; lia
      end.
    - assert (j <= mid) by lia.
      assert (Hmono: Znth j l 0 <= Znth mid l 0).
      {
        match goal with
        | Hlen: Zlength l = n_pre,
          Hsorted: forall k, 0 <= k /\ k + 1 < n_pre ->
                             Znth k l 0 <= Znth (k + 1) l 0 |- _ =>
            apply (binary_search_sorted_adjacent_mono l n_pre j mid);
            try exact Hlen; try exact Hsorted; lia
        end.
      }
      lia.
  }
  sep_apply store_int_undef_store_int.
  entailer!.
Qed. 
