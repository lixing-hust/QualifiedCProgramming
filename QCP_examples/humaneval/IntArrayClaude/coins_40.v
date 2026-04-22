Load "../spec/40".

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition triple_sum_int_range (l : list Z) (n : Z) : Prop :=
  forall i j k,
    0 <= i < j ->
    j < k ->
    k < n ->
    INT_MIN <= Znth i l 0 + Znth j l 0 <= INT_MAX /\
    INT_MIN <= Znth i l 0 + Znth j l 0 + Znth k l 0 <= INT_MAX.

Definition triple_sum_zero (l : list Z) (i j k : Z) : Prop :=
  Znth i l 0 + Znth j l 0 + Znth k l 0 = 0.

Definition scanned_i (l : list Z) (n i : Z) : Prop :=
  forall p q r,
    0 <= p < q ->
    q < r ->
    r < n ->
    p < i ->
    ~ triple_sum_zero l p q r.

Definition scanned_j (l : list Z) (n i j : Z) : Prop :=
  scanned_i l n i /\
  forall q r,
    i < q ->
    q < r ->
    r < n ->
    q < j ->
    ~ triple_sum_zero l i q r.

Definition scanned_k (l : list Z) (n i j k : Z) : Prop :=
  scanned_j l n i j /\
  forall r,
    j < r ->
    r < k ->
    ~ triple_sum_zero l i j r.

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

Lemma scanned_k_init : forall l n i j,
  scanned_j l n i j ->
  scanned_k l n i j (j + 1).
Proof.
  unfold scanned_k; intros.
  split; auto.
  intros; lia.
Qed.

Lemma scanned_k_step : forall l n i j k,
  scanned_k l n i j k ->
  ~ triple_sum_zero l i j k ->
  scanned_k l n i j (k + 1).
Proof.
  unfold scanned_k; intros l n i j k [Hj Hk] Hcur.
  split; auto.
  intros r Hjr Hr.
  assert (r < k \/ r = k) by lia.
  destruct H as [Hlt | ->]; auto.
Qed.

Lemma scanned_j_step : forall l n i j k,
  k >= n ->
  k <= n ->
  scanned_k l n i j k ->
  scanned_j l n i (j + 1).
Proof.
  unfold scanned_k, scanned_j; intros l n i j k Hge Hle [Hs Hj].
  destruct Hs as [Hi Hq].
  split; auto.
  intros q r Hiq Hqr Hrn Hqnext.
  assert (q < j \/ q = j) by lia.
  destruct H as [Hqj | ->].
  - apply Hq; lia.
  - apply Hj; lia.
Qed.

Lemma scanned_i_step : forall l n i j,
  j >= n ->
  j <= n ->
  scanned_j l n i j ->
  scanned_i l n (i + 1).
Proof.
  unfold scanned_j, scanned_i; intros l n i j Hge Hle [Hi Hq].
  intros p q r Hpq Hqr Hrn Hpnext.
  assert (p < i \/ p = i) by lia.
  destruct H as [Hpi | ->].
  - apply Hi; lia.
  - apply Hq; lia.
Qed.

Lemma problem_40_spec_true_of_triple : forall l n i j k,
  Zlength l = n ->
  0 <= i < j ->
  j < k ->
  k < n ->
  triple_sum_zero l i j k ->
  problem_40_spec l true.
Proof.
  intros l n i j k Hlen Hij Hjk Hkn Hsum.
  unfold problem_40_spec.
  split; intro H; [reflexivity |].
  exists (Z.to_nat i), (Z.to_nat j), (Z.to_nat k).
  repeat split.
  - intro Heq. apply Z2Nat.inj in Heq; lia.
  - intro Heq. apply Z2Nat.inj in Heq; lia.
  - intro Heq. apply Z2Nat.inj in Heq; lia.
  - apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia.
  - apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia.
  - apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia.
  - unfold triple_sum_zero, Znth in Hsum.
    exact Hsum.
Qed.

Lemma scanned_i_no_ordered_triple : forall l n limit p q r,
  scanned_i l n limit ->
  n <= limit ->
  0 <= p < q ->
  q < r ->
  r < n ->
  triple_sum_zero l p q r ->
  False.
Proof.
  intros l n limit p q r Hscan Hlimit Hpq Hqr Hrn Hzero.
  specialize (Hscan p q r Hpq Hqr Hrn).
  apply Hscan; [lia | exact Hzero].
Qed.

Lemma scanned_i_no_distinct_triple : forall l n limit a b c,
  scanned_i l n limit ->
  n <= limit ->
  0 <= a < n ->
  0 <= b < n ->
  0 <= c < n ->
  a <> b ->
  a <> c ->
  b <> c ->
  Znth a l 0 + Znth b l 0 + Znth c l 0 = 0 ->
  False.
Proof.
  intros l n limit a b c Hscan Hlimit Ha Hb Hc Hab Hac Hbc Hsum.
  destruct (Z_lt_ge_dec a b) as [Hablt | Hbage].
  - destruct (Z_lt_ge_dec b c) as [Hbclt | Hcbge].
    + eapply scanned_i_no_ordered_triple with (p := a) (q := b) (r := c); eauto;
        unfold triple_sum_zero; lia.
    + destruct (Z_lt_ge_dec a c) as [Haclt | Hcage].
      * eapply scanned_i_no_ordered_triple with (p := a) (q := c) (r := b); eauto;
          unfold triple_sum_zero; lia.
      * eapply scanned_i_no_ordered_triple with (p := c) (q := a) (r := b); eauto;
          unfold triple_sum_zero; lia.
  - destruct (Z_lt_ge_dec a c) as [Haclt | Hcage].
    + eapply scanned_i_no_ordered_triple with (p := b) (q := a) (r := c); eauto;
        unfold triple_sum_zero; lia.
    + destruct (Z_lt_ge_dec b c) as [Hbclt | Hcbge].
      * eapply scanned_i_no_ordered_triple with (p := b) (q := c) (r := a); eauto;
          unfold triple_sum_zero; lia.
      * eapply scanned_i_no_ordered_triple with (p := c) (q := b) (r := a); eauto;
          unfold triple_sum_zero; lia.
Qed.

Lemma problem_40_spec_false_of_scanned_i : forall l n limit,
  Zlength l = n ->
  n <= limit ->
  scanned_i l n limit ->
  problem_40_spec l false.
Proof.
  intros l n limit Hlen Hlimit Hscan.
  unfold problem_40_spec.
  split; intro H.
  - destruct H as [i [j [k [Hij [Hik [Hjk [Hi [Hj [Hk Hsum]]]]]]]]].
    pose (zi := Z.of_nat i).
    pose (zj := Z.of_nat j).
    pose (zk := Z.of_nat k).
    assert (Hzi : 0 <= zi < n).
    { subst zi. rewrite <- Hlen. rewrite Zlength_correct. lia. }
    assert (Hzj : 0 <= zj < n).
    { subst zj. rewrite <- Hlen. rewrite Zlength_correct. lia. }
    assert (Hzk : 0 <= zk < n).
    { subst zk. rewrite <- Hlen. rewrite Zlength_correct. lia. }
    assert (Hzij : zi <> zj).
    { subst zi zj. intro Heq. apply Nat2Z.inj in Heq. contradiction. }
    assert (Hzik : zi <> zk).
    { subst zi zk. intro Heq. apply Nat2Z.inj in Heq. contradiction. }
    assert (Hzjk : zj <> zk).
    { subst zj zk. intro Heq. apply Nat2Z.inj in Heq. contradiction. }
    assert (Hzsum : Znth zi l 0 + Znth zj l 0 + Znth zk l 0 = 0).
    { subst zi zj zk. unfold Znth. rewrite !Nat2Z.id. exact Hsum. }
    exfalso.
    eapply scanned_i_no_distinct_triple with
      (n := n) (limit := limit) (a := zi) (b := zj) (c := zk); eauto.
  - discriminate H.
Qed.
