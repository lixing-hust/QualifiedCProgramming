Load "../spec/135".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
From AUXLib Require Import List_lemma.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition can_arrange_hit (l : list Z) (i : Z) : Prop :=
  0 <= i < Zlength l /\ Znth i l 0 <= i.

Definition can_arrange_prefix (i : Z) (l : list Z) (max : Z) : Prop :=
  0 <= i <= Zlength l /\
  -1 <= max < i /\
  (max = -1 \/ can_arrange_hit l max) /\
  (forall j, 0 <= j < i -> can_arrange_hit l j -> j <= max).

Definition problem_135_pre_z (l : list Z) : Prop :=
  problem_135_pre l.

Definition problem_135_spec_z (l : list Z) (r : Z) : Prop :=
  problem_135_spec l r.

Lemma can_arrange_prefix_init : forall l,
  0 <= Zlength l ->
  can_arrange_prefix 0 l (-1).
Proof.
  intros l Hlen.
  unfold can_arrange_prefix.
  repeat split; try lia.
Qed.

Lemma can_arrange_prefix_keep : forall i l max,
  can_arrange_prefix i l max ->
  0 <= i < Zlength l ->
  ~ can_arrange_hit l i ->
  can_arrange_prefix (i + 1) l max.
Proof.
  intros i l max Hpre Hi Hnot.
  unfold can_arrange_prefix in *.
  destruct Hpre as [Hibound [Hmax [Hmaxhit Hall]]].
  repeat split; try lia; try assumption.
  intros j Hj Hhit.
  assert (j < i \/ j = i) by lia.
  destruct H as [Hlt | Heq].
  - apply Hall; [lia|assumption].
  - subst j. contradiction.
Qed.

Lemma can_arrange_prefix_update : forall i l max,
  can_arrange_prefix i l max ->
  0 <= i < Zlength l ->
  can_arrange_hit l i ->
  can_arrange_prefix (i + 1) l i.
Proof.
  intros i l max Hpre Hi Hhit.
  unfold can_arrange_prefix in *.
  destruct Hpre as [Hibound [_ [_ Hall]]].
  repeat split; try lia; try (right; assumption).
Qed.

Lemma can_arrange_hit_of_cond : forall l i,
  0 <= i < Zlength l ->
  Znth i l 0 <= i ->
  can_arrange_hit l i.
Proof.
  intros l i Hi Hle.
  unfold can_arrange_hit.
  split; lia.
Qed.

Lemma can_arrange_not_hit_of_cond : forall l i,
  0 <= i < Zlength l ->
  Znth i l 0 > i ->
  ~ can_arrange_hit l i.
Proof.
  intros l i Hi Hgt Hhit.
  unfold can_arrange_hit in Hhit.
  lia.
Qed.

Lemma can_arrange_at_hit_iff : forall l k,
  can_arrange_at l k <-> can_arrange_hit l (Z.of_nat k).
Proof.
  intros l k.
  unfold can_arrange_at, can_arrange_hit.
  rewrite Zlength_correct.
  split.
  - intros [Hlen Hnth].
    split.
    + lia.
    + destruct (nth_error l k) eqn:Hntherr; [|contradiction].
      unfold Znth.
      replace (Z.to_nat (Z.of_nat k)) with k by lia.
      rewrite (nth_error_nth l k 0%Z Hntherr).
      exact Hnth.
  - intros [Hrange Hle].
    split; [lia|].
    destruct (nth_error l k) eqn:Hntherr.
    + unfold Znth in Hle.
      replace (Z.to_nat (Z.of_nat k)) with k in Hle by lia.
      rewrite (nth_error_nth l k 0%Z Hntherr) in Hle.
      exact Hle.
    + apply nth_error_None in Hntherr.
      lia.
Qed.

Lemma can_arrange_prefix_full_spec : forall l r,
  can_arrange_prefix (Zlength l) l r ->
  problem_135_spec l r.
Proof.
  intros l r Hpre.
  unfold can_arrange_prefix in Hpre.
  destruct Hpre as [Hibound [Hr [Hrhit Hmax]]].
  destruct Hrhit as [Hrneg | Hrhit].
  - left.
    split; [assumption|].
    intros k Hat.
    apply can_arrange_at_hit_iff in Hat.
    assert (0 <= Z.of_nat k < Zlength l).
    { unfold can_arrange_hit in Hat. lia. }
    pose proof (Hmax (Z.of_nat k) ltac:(lia) Hat).
    lia.
  - right.
    assert (0 <= r) by (destruct Hrhit as [Hrng _]; lia).
    exists (Z.to_nat r).
    split.
    + rewrite Z2Nat.id by lia.
      reflexivity.
    + split.
      * apply can_arrange_at_hit_iff.
        rewrite Z2Nat.id by lia.
        assumption.
      * intros j Hat.
        apply can_arrange_at_hit_iff in Hat.
        assert (0 <= Z.of_nat j < Zlength l).
        { unfold can_arrange_hit in Hat. lia. }
        pose proof (Hmax (Z.of_nat j) ltac:(lia) Hat).
        lia.
Qed.
