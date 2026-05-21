Load "../spec/80".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Import string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition problem_80_pre_z (s : list Z) : Prop :=
  problem_80_pre (string_of_list_z s).

Definition problem_80_spec_z (s : list Z) (output : Z) : Prop :=
  problem_80_spec (string_of_list_z s) (bool_of_z output).

Definition ascii_range_z (s : list Z) : Prop :=
  string_bridge.ascii_range_z s.

Definition happy_window_end_z (k : Z) (s : list Z) : Prop :=
  Znth k s 0 <> Znth (k - 1) s 0 /\
  Znth k s 0 <> Znth (k - 2) s 0 /\
  Znth (k - 1) s 0 <> Znth (k - 2) s 0.

Definition happy_prefix_z (i : Z) (s : list Z) : Prop :=
  forall k, 2 <= k < i -> happy_window_end_z k s.

Definition happy_adjacent_z (i : Z) (s : list Z) : Prop :=
  Znth (i - 1) s 0 <> Znth (i - 2) s 0.

Lemma happy_prefix_z_2 : forall s,
  happy_prefix_z 2 s.
Proof.
  unfold happy_prefix_z.
  intros s k Hk.
  lia.
Qed.

Lemma happy_adjacent_z_2 : forall s,
  Znth 1 s 0 <> Znth 0 s 0 ->
  happy_adjacent_z 2 s.
Proof.
  unfold happy_adjacent_z.
  intros s H.
  replace (2 - 1) with 1 by lia.
  replace (2 - 2) with 0 by lia.
  exact H.
Qed.

Lemma happy_adjacent_z_step : forall i s,
  Znth i s 0 <> Znth (i - 1) s 0 ->
  happy_adjacent_z (i + 1) s.
Proof.
  unfold happy_adjacent_z.
  intros i s H.
  replace (i + 1 - 1) with i by lia.
  replace (i + 1 - 2) with (i - 1) by lia.
  exact H.
Qed.

Lemma happy_prefix_z_step : forall i s,
  happy_prefix_z i s ->
  happy_adjacent_z i s ->
  Znth i s 0 <> Znth (i - 1) s 0 ->
  Znth i s 0 <> Znth (i - 2) s 0 ->
  happy_prefix_z (i + 1) s.
Proof.
  unfold happy_prefix_z, happy_window_end_z.
  intros i s Hprefix Hadj Hprev1 Hprev2 k Hk.
  destruct (Z_lt_ge_dec k i).
  - apply Hprefix. lia.
  - assert (k = i) by lia.
    subst k.
    unfold happy_adjacent_z in Hadj.
    repeat split; assumption.
Qed.

Lemma problem_80_spec_z_short : forall s,
  Zlength s < 3 ->
  problem_80_spec_z s 0.
Proof.
  intros s Hshort.
  unfold problem_80_spec_z, bool_of_z.
  change (Z.eqb 0 1) with false.
  unfold problem_80_spec.
  rewrite string_of_list_z_length.
  rewrite Zlength_correct in Hshort.
  left.
  lia.
Qed.

Lemma string_get_eq_from_z : forall s i j,
  0 <= i < Zlength s ->
  0 <= j < Zlength s ->
  Znth i s 0 = Znth j s 0 ->
  String.get (Z.to_nat i) (string_of_list_z s) =
  String.get (Z.to_nat j) (string_of_list_z s).
Proof.
  intros s i j Hi Hj Heq.
  repeat rewrite string_get_string_of_list_z_z by lia.
  rewrite Heq.
  reflexivity.
Qed.

Lemma string_get_neq_from_z : forall s i j,
  ascii_range_z s ->
  0 <= i < Zlength s ->
  0 <= j < Zlength s ->
  Znth i s 0 <> Znth j s 0 ->
  String.get (Z.to_nat i) (string_of_list_z s) <>
  String.get (Z.to_nat j) (string_of_list_z s).
Proof.
  intros s i j Hrange Hi Hj Hneq Heq.
  repeat rewrite string_get_string_of_list_z_z in Heq by lia.
  inversion Heq as [Hascii].
  apply Hneq.
  apply (f_equal nat_of_ascii) in Hascii.
  repeat rewrite nat_of_ascii_ascii_of_z in Hascii by (apply Hrange; lia).
  apply Z2Nat.inj; try (pose proof (Hrange i Hi); lia);
    try (pose proof (Hrange j Hj); lia); exact Hascii.
Qed.

Lemma problem_80_spec_z_false_first_pair : forall s,
  3 <= Zlength s ->
  Znth 1 s 0 = Znth 0 s 0 ->
  problem_80_spec_z s 0.
Proof.
  intros s Hlen Heq.
  assert (HZlen : 3 <= Zlength s) by exact Hlen.
  unfold problem_80_spec_z, bool_of_z.
  change (Z.eqb 0 1) with false.
  unfold problem_80_spec.
  rewrite string_of_list_z_length.
  right.
  exists 0%nat.
  rewrite Zlength_correct in Hlen.
  split; [lia |].
  left.
  change (0%nat) with (Z.to_nat 0).
  replace (Z.to_nat 0 + S (Z.to_nat 0))%nat with (Z.to_nat 1)
    by reflexivity.
  pose proof (string_get_eq_from_z s 0 1 ltac:(lia) ltac:(lia)
    ltac:(symmetry; exact Heq)) as Hget.
  exact Hget.
Qed.

Lemma problem_80_spec_z_false_prev1 : forall s i,
  2 <= i ->
  i < Zlength s ->
  Znth i s 0 = Znth (i - 1) s 0 ->
  problem_80_spec_z s 0.
Proof.
  intros s i Hi Hbound Heq.
  assert (HZbound : i < Zlength s) by exact Hbound.
  unfold problem_80_spec_z, bool_of_z.
  change (Z.eqb 0 1) with false.
  unfold problem_80_spec.
  rewrite string_of_list_z_length.
  right.
  exists (Z.to_nat (i - 2)).
  rewrite Zlength_correct in Hbound.
  split.
  - change (Z.to_nat (i - 2) + 2 < Datatypes.length s)%nat.
    apply Nat2Z.inj_lt.
    rewrite Nat2Z.inj_add.
    rewrite Z2Nat.id by lia.
    lia.
  - right.
    right.
    replace (Z.to_nat (i - 2) + 1)%nat with (Z.to_nat (i - 1)) by lia.
    replace (Z.to_nat (i - 2) + 2)%nat with (Z.to_nat i) by lia.
    pose proof (string_get_eq_from_z s (i - 1) i ltac:(lia) ltac:(lia)
      ltac:(symmetry; exact Heq)) as Hget.
    exact Hget.
Qed.

Lemma problem_80_spec_z_false_prev2 : forall s i,
  2 <= i ->
  i < Zlength s ->
  Znth i s 0 = Znth (i - 2) s 0 ->
  problem_80_spec_z s 0.
Proof.
  intros s i Hi Hbound Heq.
  assert (HZbound : i < Zlength s) by exact Hbound.
  unfold problem_80_spec_z, bool_of_z.
  change (Z.eqb 0 1) with false.
  unfold problem_80_spec.
  rewrite string_of_list_z_length.
  right.
  exists (Z.to_nat (i - 2)).
  rewrite Zlength_correct in Hbound.
  split.
  - change (Z.to_nat (i - 2) + 2 < Datatypes.length s)%nat.
    apply Nat2Z.inj_lt.
    rewrite Nat2Z.inj_add.
    rewrite Z2Nat.id by lia.
    lia.
  - right.
    left.
    replace (Z.to_nat (i - 2) + 2)%nat with (Z.to_nat i) by lia.
    pose proof (string_get_eq_from_z s (i - 2) i ltac:(lia) ltac:(lia)
      ltac:(symmetry; exact Heq)) as Hget.
    exact Hget.
Qed.

Lemma problem_80_spec_z_true : forall s i,
  ascii_range_z s ->
  i >= Zlength s ->
  3 <= Zlength s ->
  happy_prefix_z i s ->
  problem_80_spec_z s 1.
Proof.
  intros s i Hrange Hexit Hlen Hprefix.
  unfold problem_80_spec_z, bool_of_z.
  change (Z.eqb 1 1) with true.
  unfold problem_80_spec.
  rewrite string_of_list_z_length.
  rewrite Zlength_correct in *.
  split; [lia |].
  intros n Hn.
  apply Nat2Z.inj_lt in Hn.
  rewrite Nat2Z.inj_add in Hn.
  set (k := Z.of_nat (n + 2)).
  assert (Hk_range : 2 <= k < Zlength s).
  {
    rewrite Zlength_correct.
    subst k.
    rewrite Nat2Z.inj_add.
    lia.
  }
  assert (Hwin : happy_window_end_z k s) by (apply Hprefix; lia).
  unfold happy_window_end_z in Hwin.
  destruct Hwin as [Hneq32 [Hneq31 Hneq21]].
  subst k.
  rewrite Nat2Z.inj_add in *.
  assert (Hneq32' :
    Znth (Z.of_nat n + 2) s 0 <> Znth (Z.of_nat n + 1) s 0).
  {
    intro H.
    apply Hneq32.
    replace (Z.of_nat n + Z.of_nat 2) with (Z.of_nat n + 2) by lia.
    replace (Z.of_nat n + 2 - 1) with (Z.of_nat n + 1) by lia.
    exact H.
  }
  assert (Hneq31' :
    Znth (Z.of_nat n + 2) s 0 <> Znth (Z.of_nat n) s 0).
  {
    intro H.
    apply Hneq31.
    replace (Z.of_nat n + Z.of_nat 2) with (Z.of_nat n + 2) by lia.
    replace (Z.of_nat n + 2 - 2) with (Z.of_nat n) by lia.
    exact H.
  }
  assert (Hneq21' :
    Znth (Z.of_nat n + 1) s 0 <> Znth (Z.of_nat n) s 0).
  {
    intro H.
    apply Hneq21.
    replace (Z.of_nat n + Z.of_nat 2 - 1) with (Z.of_nat n + 1) by lia.
    replace (Z.of_nat n + Z.of_nat 2 - 2) with (Z.of_nat n) by lia.
    exact H.
  }
  repeat split.
  - replace n with (Z.to_nat (Z.of_nat n)) by lia.
    replace (Z.to_nat (Z.of_nat n) + 1)%nat with
      (Z.to_nat (Z.of_nat n + 1)) by lia.
    apply string_get_neq_from_z; try assumption; try lia.
  - replace n with (Z.to_nat (Z.of_nat n)) by lia.
    replace (Z.to_nat (Z.of_nat n) + 2)%nat with
      (Z.to_nat (Z.of_nat n + 2)) by lia.
    apply string_get_neq_from_z; try assumption; try lia.
  - replace (n + 1)%nat with (Z.to_nat (Z.of_nat n + 1)) by lia.
    replace (n + 2)%nat with (Z.to_nat (Z.of_nat n + 2)) by lia.
    apply string_get_neq_from_z; try assumption; try lia.
Qed.
