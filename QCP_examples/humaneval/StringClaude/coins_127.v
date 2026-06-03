Load "../spec/127".

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import ListNotations.
Import naive_C_Rules.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition yesno_of_z (z : Z) : string :=
  if Z.eqb z 1 then "YES" else "NO".

Definition interval_pair_z (l : list Z) : Z * Z :=
  (Znth 0 l 0, Znth 1 l 0).

Definition inter_start_z (i1 i2 : list Z) : Z :=
  Z.max (Znth 0 i1 0) (Znth 0 i2 0).

Definition inter_end_z (i1 i2 : list Z) : Z :=
  Z.min (Znth 1 i1 0) (Znth 1 i2 0).

Definition inter_len_z (i1 i2 : list Z) : Z :=
  inter_end_z i1 i2 - inter_start_z i1 i2.

Definition problem_127_pre_z (i1 i2 : list Z) : Prop :=
  problem_127_pre (interval_pair_z i1) (interval_pair_z i2).

Definition problem_127_spec_z (i1 i2 : list Z) (output : Z) : Prop :=
  problem_127_spec (interval_pair_z i1) (interval_pair_z i2) (yesno_of_z output).

Definition interval_int_range (l : list Z) : Prop :=
  Zlength l = 2 /\
  forall i, 0 <= i < 2 -> -1000000000 <= Znth i l 0 <= 1000000000.

Definition prime_prefix_z (i n : Z) : Prop :=
  forall d, 2 <= d < i -> Z.rem n d <> 0.

Definition prime_len_z (n : Z) : Prop :=
  2 <= n /\ forall d, 2 <= d /\ d * d <= n -> Z.rem n d <> 0.

Lemma prime_to_prime_len_z : forall n,
  prime n ->
  prime_len_z n.
Proof.
  intros n Hprime.
  unfold prime_len_z.
  split.
  - pose proof (prime_ge_2 _ Hprime). lia.
  - intros d [Hd Hsquare] Hrem.
    apply Z.rem_divide in Hrem; try lia.
    pose proof (prime_divisors _ Hprime _ Hrem) as Hdivs.
    destruct Hdivs as [-> | [-> | [-> | ->]]]; nia.
Qed.

Lemma prime_len_z_to_prime : forall n,
  prime_len_z n ->
  prime n.
Proof.
  intros n [Hn Hnodiv].
  apply prime_alt.
  unfold prime'.
  split.
  - lia.
  - intros d Hd Hdivide.
  destruct Hdivide as [q Hnq].
    destruct (Z_le_gt_dec (d * d) n) as [Hsmall | Hlarge].
    + apply (Hnodiv d).
      * lia.
      * apply Z.rem_divide.
        { lia. }
        { exists q. exact Hnq. }
    + assert (Hqpos : 1 < q).
    {
      assert (0 < q) by nia.
      destruct (Z.eq_dec q 1) as [-> | Hqne]; nia.
    }
      assert (Hqsmall : q * q <= n) by nia.
      apply (Hnodiv q).
      * lia.
      * apply Z.rem_divide.
        { lia. }
        { exists d. nia. }
Qed.

Lemma prime_prefix_z_2 : forall n,
  prime_prefix_z 2 n.
Proof.
  unfold prime_prefix_z.
  intros n d H.
  lia.
Qed.

Lemma prime_prefix_z_step : forall i n,
  prime_prefix_z i n ->
  Z.rem n i <> 0 ->
  prime_prefix_z (i + 1) n.
Proof.
  unfold prime_prefix_z.
  intros i n Hpre Hmod d Hd.
  destruct (Z.eq_dec d i) as [-> | Hne].
  - exact Hmod.
  - apply Hpre. lia.
Qed.

Lemma prime_len_z_false_small : forall n,
  n < 2 ->
  ~ prime_len_z n.
Proof.
  unfold prime_len_z.
  intros n Hlt H.
  lia.
Qed.

Lemma prime_len_z_false_divisor : forall i n,
  2 <= i ->
  i * i <= n ->
  Z.rem n i = 0 ->
  ~ prime_len_z n.
Proof.
  unfold prime_len_z.
  intros i n Hi Hsquare Hmod [_ Hprime].
  specialize (Hprime i ltac:(lia)).
  contradiction.
Qed.

Lemma prime_len_z_true_from_prefix : forall i n,
  2 <= n ->
  2 <= i ->
  i * i > n ->
  prime_prefix_z i n ->
  prime_len_z n.
Proof.
  unfold prime_prefix_z, prime_len_z.
  intros i n Hn Hi Hexit Hpre.
  split.
  - assumption.
  - intros d [Hd Hsquare].
    apply Hpre.
    assert (d < i) by nia.
    lia.
Qed.

Lemma problem_127_spec_z_true : forall i1 i2,
  prime_len_z (inter_len_z i1 i2) ->
  problem_127_spec_z i1 i2 1.
Proof.
  intros i1 i2 Hprime_len.
  unfold problem_127_spec_z, problem_127_spec, interval_pair_z,
    inter_len_z, inter_start_z, inter_end_z, yesno_of_z.
  destruct Hprime_len as [Hlen Hnodiv].
  unfold inter_len_z, inter_start_z, inter_end_z in Hlen.
  replace (Z.eqb 1 1) with true by reflexivity.
  destruct (Z.leb_spec (Z.max (Znth 0 i1 0) (Znth 0 i2 0))
                       (Z.min (Znth 1 i1 0) (Znth 1 i2 0))).
  - left.
    split.
    + rewrite Z2Nat.id by lia.
      apply prime_len_z_to_prime.
      split; assumption.
    + reflexivity.
  - lia.
Qed.

Lemma problem_127_spec_z_false : forall i1 i2,
  ~ prime_len_z (inter_len_z i1 i2) ->
  problem_127_spec_z i1 i2 0.
Proof.
  intros i1 i2 Hnot.
  unfold problem_127_spec_z, problem_127_spec, interval_pair_z,
    inter_len_z, inter_start_z, inter_end_z, yesno_of_z.
  replace (Z.eqb 0 1) with false by reflexivity.
  destruct (Z.leb_spec (Z.max (Znth 0 i1 0) (Znth 0 i2 0))
                       (Z.min (Znth 1 i1 0) (Znth 1 i2 0))).
  - right.
    split.
    + intros Hprime.
      apply Hnot.
      rewrite Z2Nat.id in Hprime by lia.
      apply prime_to_prime_len_z.
      exact Hprime.
    + reflexivity.
  - reflexivity.
Qed.

Lemma inter_len_range_safe : forall i1 i2,
  interval_int_range i1 ->
  interval_int_range i2 ->
  -2000000000 <= inter_len_z i1 i2 <= 2000000000.
Proof.
  intros i1 i2 [_ Hr1] [_ Hr2].
  unfold inter_len_z, inter_start_z, inter_end_z.
  pose proof (Hr1 0 ltac:(lia)).
  pose proof (Hr1 1 ltac:(lia)).
  pose proof (Hr2 0 ltac:(lia)).
  pose proof (Hr2 1 ltac:(lia)).
  nia.
Qed.

Lemma prime_loop_next_bound_127 : forall i n,
  2 <= i ->
  i <= 46340 ->
  n <= 2000000000 ->
  i * i <= n ->
  i + 1 <= 46340.
Proof.
  intros.
  nia.
Qed.
