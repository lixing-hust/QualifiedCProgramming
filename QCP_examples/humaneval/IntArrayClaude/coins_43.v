Load "../spec/43".

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition pair_sum_int_range (l : list Z) (n : Z) : Prop :=
  forall i j,
    0 <= i < j ->
    j < n ->
    INT_MIN <= Znth i l 0 + Znth j l 0 <= INT_MAX.

Definition pair_sum_zero (l : list Z) (i j : Z) : Prop :=
  Znth i l 0 + Znth j l 0 = 0.

Definition scanned_i (l : list Z) (n i : Z) : Prop :=
  forall p q,
    0 <= p < q ->
    q < n ->
    p < i ->
    ~ pair_sum_zero l p q.

Definition scanned_j (l : list Z) (n i j : Z) : Prop :=
  scanned_i l n i /\
  forall q,
    i < q ->
    q < n ->
    q < j ->
    ~ pair_sum_zero l i q.

Lemma scanned_i_init : forall l n,
  scanned_i l n 0.
Proof.
  unfold scanned_i; intros; lia.
Qed.

Lemma scanned_j_init : forall l n i,
  scanned_i l n i ->
  scanned_j l n i (i + 1).
Proof.
  unfold scanned_j; intros.
  split; auto.
  intros; lia.
Qed.

Lemma scanned_j_step : forall l n i j,
  scanned_j l n i j ->
  ~ pair_sum_zero l i j ->
  scanned_j l n i (j + 1).
Proof.
  unfold scanned_j; intros l n i j [Hi Hj] Hcur.
  split; auto.
  intros q Hiq Hqn Hqnext.
  assert (q < j \/ q = j) by lia.
  destruct H as [Hlt | ->]; auto.
Qed.

Lemma scanned_i_step : forall l n i j,
  j >= n ->
  j <= n ->
  scanned_j l n i j ->
  scanned_i l n (i + 1).
Proof.
  unfold scanned_j, scanned_i; intros l n i j Hge Hle [Hi Hj].
  intros p q Hpq Hqn Hpnext.
  assert (p < i \/ p = i) by lia.
  destruct H as [Hpi | ->].
  - apply Hi; lia.
  - apply Hj; lia.
Qed.

Lemma problem_43_spec_true_of_pair : forall l n i j,
  Zlength l = n ->
  0 <= i < j ->
  j < n ->
  pair_sum_zero l i j ->
  problem_43_spec l true.
Proof.
  intros l n i j Hlen Hij Hjn Hsum.
  unfold problem_43_spec.
  split; intro H; [reflexivity |].
  exists (Z.to_nat i), (Z.to_nat j).
  repeat split.
  - intro Heq. apply Z2Nat.inj in Heq; lia.
  - apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia.
  - apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia.
  - unfold pair_sum_zero, Znth in Hsum.
    exact Hsum.
Qed.

Lemma scanned_i_no_ordered_pair : forall l n limit p q,
  scanned_i l n limit ->
  n <= limit ->
  0 <= p < q ->
  q < n ->
  pair_sum_zero l p q ->
  False.
Proof.
  intros l n limit p q Hscan Hlimit Hpq Hqn Hzero.
  specialize (Hscan p q Hpq Hqn).
  apply Hscan; [lia | exact Hzero].
Qed.

Lemma scanned_i_no_distinct_pair : forall l n limit a b,
  scanned_i l n limit ->
  n <= limit ->
  0 <= a < n ->
  0 <= b < n ->
  a <> b ->
  Znth a l 0 + Znth b l 0 = 0 ->
  False.
Proof.
  intros l n limit a b Hscan Hlimit Ha Hb Hab Hsum.
  destruct (Z_lt_ge_dec a b) as [Hablt | Hbage].
  - eapply scanned_i_no_ordered_pair with (p := a) (q := b); eauto;
      unfold pair_sum_zero; lia.
  - eapply scanned_i_no_ordered_pair with (p := b) (q := a); eauto;
      unfold pair_sum_zero; lia.
Qed.

Lemma problem_43_spec_false_of_scanned_i : forall l n limit,
  Zlength l = n ->
  n <= limit ->
  scanned_i l n limit ->
  problem_43_spec l false.
Proof.
  intros l n limit Hlen Hlimit Hscan.
  unfold problem_43_spec.
  split; intro H.
  - destruct H as [i [j [Hij [Hi [Hj Hsum]]]]].
    pose (zi := Z.of_nat i).
    pose (zj := Z.of_nat j).
    assert (Hzi : 0 <= zi < n).
    { subst zi. rewrite <- Hlen. rewrite Zlength_correct. lia. }
    assert (Hzj : 0 <= zj < n).
    { subst zj. rewrite <- Hlen. rewrite Zlength_correct. lia. }
    assert (Hzij : zi <> zj).
    { subst zi zj. intro Heq. apply Nat2Z.inj in Heq. contradiction. }
    assert (Hzsum : Znth zi l 0 + Znth zj l 0 = 0).
    { subst zi zj. unfold Znth. rewrite !Nat2Z.id. exact Hsum. }
    exfalso.
    eapply scanned_i_no_distinct_pair with
      (n := n) (limit := limit) (a := zi) (b := zj); eauto.
  - discriminate H.
Qed.
