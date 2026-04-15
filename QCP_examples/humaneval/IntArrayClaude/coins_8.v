Load "../spec/8".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Import ListNotations.

Definition list_int_range (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> INT_MIN <= Znth i l 0 <= INT_MAX.

Definition prefix_sum (l : list Z) (i : Z) : Z :=
  fold_left Z.add (sublist 0 i l) 0.

Definition prefix_product (l : list Z) (i : Z) : Z :=
  fold_left Z.mul (sublist 0 i l) 1.

Definition prefix_sum_product_int_range (l : list Z) (n : Z) : Prop :=
  forall i,
    0 <= i <= n ->
    INT_MIN <= prefix_sum l i <= INT_MAX /\
    INT_MIN <= prefix_product l i <= INT_MAX.

Lemma prefix_sum_snoc : forall l i,
  0 <= i < Zlength l ->
  prefix_sum l (i + 1) = prefix_sum l i + Znth i l 0.
Proof.
  intros.
  rewrite Zlength_correct in H.
  unfold prefix_sum.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single i l 0) by lia.
  rewrite fold_left_app.
  simpl.
  lia.
Qed.

Lemma prefix_product_snoc : forall l i,
  0 <= i < Zlength l ->
  prefix_product l (i + 1) = prefix_product l i * Znth i l 0.
Proof.
  intros.
  rewrite Zlength_correct in H.
  unfold prefix_product.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single i l 0) by lia.
  rewrite fold_left_app.
  simpl.
  lia.
Qed.

Lemma problem_8_spec_of_prefix_full : forall l n,
  n = Zlength l ->
  problem_8_spec l (prefix_sum l n) (prefix_product l n).
Proof.
  intros.
  unfold problem_8_spec, prefix_sum, prefix_product.
  subst n.
  rewrite sublist_self by reflexivity.
  auto.
Qed.
