Load "../spec/82".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Import string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition prime_prefix_z (i n : Z) : Prop :=
  forall d, 2 <= d < i -> Z.rem n d <> 0.

Definition prime_len_z (n : Z) : Prop :=
  2 <= n /\ forall d, 2 <= d /\ d * d <= n -> Z.rem n d <> 0.

Definition problem_82_pre_z (s : list Z) : Prop :=
  problem_82_pre (string_of_list_z s).

Definition problem_82_spec_z (s : list Z) (output : Z) : Prop :=
  problem_82_spec (string_of_list_z s) (bool_of_z output).

Lemma prime_to_prime_len_z : forall n,
  prime n ->
  prime_len_z n.
Proof.
  intros n Hprime.
  unfold prime_len_z.
  split.
  - pose proof (prime_ge_2 _ Hprime). lia.
  - intros d [Hd Hsquare] Hrem.
    apply Z.rem_divide in Hrem; [| lia].
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
  split; [lia |].
  intros d Hd Hdivide.
  destruct Hdivide as [q Hnq].
  destruct (Z_le_gt_dec (d * d) n) as [Hsmall | Hlarge].
  - apply (Hnodiv d); [lia |].
    apply Z.rem_divide; [lia |].
    exists q. exact Hnq.
  - assert (Hqpos : 1 < q).
    {
      assert (0 < q) by nia.
      destruct (Z.eq_dec q 1) as [-> | Hqne]; nia.
    }
    assert (Hqsmall : q * q <= n) by nia.
    apply (Hnodiv q); [lia |].
    apply Z.rem_divide; [lia |].
    exists d. nia.
Qed.

Lemma prime_len_z_iff_prime : forall n,
  prime_len_z n <-> prime n.
Proof.
  split; [apply prime_len_z_to_prime | apply prime_to_prime_len_z].
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
  - apply Hpre.
    lia.
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
  split; [assumption |].
  intros d [Hd Hsquare].
  apply Hpre.
  assert (d < i) by nia.
  lia.
Qed.

Lemma problem_82_spec_z_true : forall s,
  prime_len_z (Zlength s) ->
  problem_82_spec_z s 1.
Proof.
  intros s H.
  unfold problem_82_spec_z.
  unfold problem_82_spec, bool_of_z.
  simpl.
  rewrite string_of_list_z_length_z.
  split; intros _.
  - apply prime_len_z_to_prime. exact H.
  - reflexivity.
Qed.

Lemma problem_82_spec_z_false : forall s,
  ~ prime_len_z (Zlength s) ->
  problem_82_spec_z s 0.
Proof.
  intros s H.
  unfold problem_82_spec_z.
  unfold problem_82_spec, bool_of_z.
  simpl.
  rewrite string_of_list_z_length_z.
  split; intros Hbad.
  - discriminate.
  - exfalso. apply H.
    apply prime_to_prime_len_z. exact Hbad.
Qed.

Lemma prime_loop_next_bound : forall i n,
  2 <= i ->
  i <= 46340 ->
  n <= 2147302921 ->
  i * i <= n ->
  i + 1 <= 46340.
Proof.
  intros.
  nia.
Qed.
