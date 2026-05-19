Load "../spec/126".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition problem_126_pre_z (l : list Z) : Prop :=
  Forall (fun z => 0 <= z) l /\
  problem_126_pre (map Z.to_nat l).

Definition sorted_no_triple_prefix (i : Z) (l : list Z) : Prop :=
  (forall j, 1 <= j < i -> Znth (j - 1) l 0 <= Znth j l 0) /\
  (forall j, 2 <= j < i ->
    ~ (Znth j l 0 = Znth (j - 1) l 0 /\ Znth j l 0 = Znth (j - 2) l 0)).

Definition problem_126_spec_z (l : list Z) (b : bool) : Prop :=
  problem_126_spec (map Z.to_nat l) b.

Lemma Forall_Znth_nonneg_126 : forall l i,
  Forall (fun z => 0 <= z) l ->
  0 <= i < Zlength l ->
  0 <= Znth i l 0.
Proof.
  intros l i Hforall Hi.
  unfold Znth.
  apply (proj1 (@Forall_nth Z (fun z => 0 <= z) l) Hforall).
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma nth_map_Znth_to_nat_126 : forall l i,
  0 <= i < Zlength l ->
  nth (Z.to_nat i) (map Z.to_nat l) 0%nat = Z.to_nat (Znth i l 0).
Proof.
  intros l i Hi.
  unfold Znth.
  rewrite map_nth with (d := 0).
  reflexivity.
Qed.

Lemma nth_map_Znth_nat_126 : forall l j,
  nth j (map Z.to_nat l) 0%nat = Z.to_nat (Znth (Z.of_nat j) l 0).
Proof.
  intros l j.
  unfold Znth.
  rewrite Nat2Z.id.
  rewrite map_nth with (d := 0).
  reflexivity.
Qed.

Lemma sorted_no_triple_prefix_to_original_126 : forall l,
  problem_126_pre_z l ->
  sorted_no_triple_prefix (Zlength l) l ->
  sorted_no_triple_nat (map Z.to_nat l).
Proof.
  intros l [Hnonneg _] [Hsorted Htriple].
  unfold sorted_no_triple_nat.
  split.
  - intros j Hj.
    assert (HjZ : 1 <= Z.of_nat j < Zlength l).
    { rewrite Zlength_correct. rewrite map_length in Hj. lia. }
    rewrite !nth_map_Znth_nat_126.
    replace (Z.of_nat (j - 1)) with (Z.of_nat j - 1) by lia.
    assert (Hprev_nonneg : 0 <= Znth (Z.of_nat j - 1) l 0)
      by (apply Forall_Znth_nonneg_126; try exact Hnonneg; lia).
    assert (Hcur_nonneg : 0 <= Znth (Z.of_nat j) l 0)
      by (apply Forall_Znth_nonneg_126; try exact Hnonneg; lia).
    apply (proj1 (Z2Nat.inj_le _ _ Hprev_nonneg Hcur_nonneg)).
    apply Hsorted. lia.
  - intros j Hj Hbad.
    assert (HjZ : 2 <= Z.of_nat j < Zlength l).
    { rewrite Zlength_correct. rewrite map_length in Hj. lia. }
    apply (Htriple (Z.of_nat j)); [lia|].
    destruct Hbad as [Heq1 Heq2].
    split.
    + apply Z2Nat.inj.
      * apply Forall_Znth_nonneg_126; try exact Hnonneg; lia.
      * apply Forall_Znth_nonneg_126; try exact Hnonneg; lia.
      * rewrite !nth_map_Znth_nat_126 in Heq1.
        replace (Z.of_nat (j - 1)) with (Z.of_nat j - 1) in Heq1 by lia.
        exact Heq1.
    + apply Z2Nat.inj.
      * apply Forall_Znth_nonneg_126; try exact Hnonneg; lia.
      * apply Forall_Znth_nonneg_126; try exact Hnonneg; lia.
      * rewrite !nth_map_Znth_nat_126 in Heq2.
        replace (Z.of_nat (j - 2)) with (Z.of_nat j - 2) in Heq2 by lia.
        exact Heq2.
Qed.

Lemma problem_126_spec_true_of_original : forall l,
  problem_126_pre_z l ->
  sorted_no_triple_prefix (Zlength l) l ->
  problem_126_spec_z l true.
Proof.
  intros l Hpre Hprefix.
  unfold problem_126_spec_z, problem_126_spec.
  split; intros _.
  - reflexivity.
  - apply sorted_no_triple_prefix_to_original_126; assumption.
Qed.

Lemma problem_126_spec_false_of_not_original : forall l,
  problem_126_pre_z l ->
  ~ sorted_no_triple_nat (map Z.to_nat l) ->
  problem_126_spec_z l false.
Proof.
  intros l _ Hnot.
  unfold problem_126_spec_z, problem_126_spec.
  split; intros H.
  - contradiction.
  - discriminate.
Qed.

Lemma sorted_no_triple_prefix_1 : forall l,
  sorted_no_triple_prefix 1 l.
Proof.
  intros l.
  unfold sorted_no_triple_prefix.
  split; intros j Hj; lia.
Qed.

Lemma sorted_no_triple_prefix_step : forall l i,
  1 <= i ->
  sorted_no_triple_prefix i l ->
  Znth (i - 1) l 0 <= Znth i l 0 ->
  ~ (2 <= i /\ Znth i l 0 = Znth (i - 1) l 0 /\ Znth i l 0 = Znth (i - 2) l 0) ->
  sorted_no_triple_prefix (i + 1) l.
Proof.
  intros l i Hi [Hsorted Htriple] Hle Hnot.
  unfold sorted_no_triple_prefix.
  split.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hne].
    + exact Hle.
    + apply Hsorted. lia.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hne].
    + intro Hbad. apply Hnot. tauto.
    + apply Htriple. lia.
Qed.

Lemma problem_126_spec_false_of_desc : forall l i,
  problem_126_pre_z l ->
  1 <= i ->
  i < Zlength l ->
  Znth i l 0 < Znth (i - 1) l 0 ->
  problem_126_spec_z l false.
Proof.
  intros l i Hpre Hi Hlen Hlt.
  apply problem_126_spec_false_of_not_original; [exact Hpre|].
  destruct Hpre as [Hnonneg _].
  intro Horig.
  unfold sorted_no_triple_nat in Horig.
  destruct Horig as [Hsorted _].
  pose proof (Hsorted (Z.to_nat i)) as Hsorted_i.
  assert (Hi_nat : (1 <= Z.to_nat i < length (map Z.to_nat l))%nat).
  {
    rewrite map_length.
    rewrite Zlength_correct in Hlen.
    assert (Z.of_nat (Z.to_nat i) = i) by lia.
    lia.
  }
  specialize (Hsorted_i Hi_nat).
  replace (Z.to_nat i - 1)%nat with (Z.to_nat (i - 1)) in Hsorted_i by lia.
  rewrite nth_map_Znth_to_nat_126 in Hsorted_i by lia.
  rewrite nth_map_Znth_to_nat_126 in Hsorted_i by lia.
  assert (Z.to_nat (Znth i l 0%Z) < Z.to_nat (Znth (i - 1) l 0%Z))%nat.
  {
    apply Z2Nat.inj_lt.
    - apply Forall_Znth_nonneg_126; try exact Hnonneg; lia.
    - apply Forall_Znth_nonneg_126; try exact Hnonneg; lia.
    - exact Hlt.
  }
  lia.
Qed.

Lemma problem_126_spec_false_of_triple : forall l i,
  problem_126_pre_z l ->
  2 <= i ->
  i < Zlength l ->
  Znth i l 0 = Znth (i - 1) l 0 ->
  Znth i l 0 = Znth (i - 2) l 0 ->
  problem_126_spec_z l false.
Proof.
  intros l i Hpre Hi Hlen Heq1 Heq2.
  apply problem_126_spec_false_of_not_original; [exact Hpre|].
  intro Horig.
  unfold sorted_no_triple_nat in Horig.
  destruct Horig as [_ Htriple].
  pose proof (Htriple (Z.to_nat i)) as Hnot.
  assert (Hi_nat : (2 <= Z.to_nat i < length (map Z.to_nat l))%nat).
  {
    rewrite map_length.
    rewrite Zlength_correct in Hlen.
    assert (Z.of_nat (Z.to_nat i) = i) by lia.
    lia.
  }
  specialize (Hnot Hi_nat).
  apply Hnot.
  split.
  - replace (Z.to_nat i - 1)%nat with (Z.to_nat (i - 1)) by lia.
    rewrite nth_map_Znth_to_nat_126 by lia.
    rewrite nth_map_Znth_to_nat_126 by lia.
    rewrite Heq1.
    reflexivity.
  - replace (Z.to_nat i - 2)%nat with (Z.to_nat (i - 2)) by lia.
    rewrite nth_map_Znth_to_nat_126 by lia.
    rewrite nth_map_Znth_to_nat_126 by lia.
    rewrite Heq2.
    reflexivity.
Qed.

Lemma problem_126_spec_true_of_exit : forall l i,
  problem_126_pre_z l ->
  i >= Zlength l ->
  i <= Zlength l ->
  sorted_no_triple_prefix i l ->
  problem_126_spec_z l true.
Proof.
  intros l i Hpre Hge Hle Hprefix.
  replace i with (Zlength l) in Hprefix by lia.
  apply problem_126_spec_true_of_original; assumption.
Qed.
