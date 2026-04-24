Load "../spec/94".

From AUXLib Require Import List_lemma ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Coq.micromega.Lia.

Import naive_C_Rules.
Open Scope Z_scope.

Definition problem_94_pre_z (lst : list Z) : Prop :=
  problem_94_pre (map Z.to_nat lst).

Definition list_nonneg_int_range (lst : list Z) : Prop :=
  forall i,
    0 <= i < Zlength lst ->
    0 <= Znth i lst 0 <= INT_MAX.

Definition largest_prime_prefix (i : Z) (lst : list Z) (largest : Z) : Prop :=
  0 <= i <= Zlength lst /\
  0 <= largest <= INT_MAX /\
  (largest = 0 \/ exists k, 0 <= k < i /\ largest = Znth k lst 0).

Definition prime_scan_state (x j prime : Z) : Prop :=
  1 < x <= INT_MAX /\
  2 <= j <= x + 1 /\
  0 <= prime <= 1.

Definition digit_sum_int_range (n : Z) : Prop :=
  0 <= n <= INT_MAX.

Fixpoint sum_digits_fuel_z (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if Z.leb n 0 then 0 else (n mod 10) + sum_digits_fuel_z (n / 10) fuel'
  end.

Definition digit_sum_state (original current sum : Z) : Prop :=
  0 <= original <= INT_MAX /\
  exists fuel : nat,
    0 <= current /\
    0 <= sum /\
    current < 10 ^ (Z.of_nat fuel) /\
    sum + sum_digits_fuel_z current fuel <= 100.

Definition problem_94_spec_z (lst : list Z) (out : Z) : Prop :=
  0 <= out <= 100 /\
  exists largest,
    largest_prime_prefix (Zlength lst) lst largest /\
    digit_sum_int_range largest.

Lemma largest_prime_prefix_init : forall lst,
  0 <= Zlength lst ->
  largest_prime_prefix 0 lst 0.
Proof.
  intros.
  unfold largest_prime_prefix.
  lia.
Qed.

Lemma largest_prime_prefix_skip : forall i lst largest,
  largest_prime_prefix i lst largest ->
  0 <= i < Zlength lst ->
  largest_prime_prefix (i + 1) lst largest.
Proof.
  intros i lst largest Hpref Hi.
  unfold largest_prime_prefix in *.
  destruct Hpref as [Hi_bounds [Hlargest Hseen]].
  repeat split; try lia.
  destruct Hseen as [-> | [k [Hk Hval]]].
  - left. reflexivity.
  - right. exists k. split; [lia | exact Hval].
Qed.

Lemma largest_prime_prefix_update : forall i lst largest x,
  largest_prime_prefix i lst largest ->
  0 <= i < Zlength lst ->
  x = Znth i lst 0 ->
  0 <= x <= INT_MAX ->
  largest_prime_prefix (i + 1) lst x.
Proof.
  intros i lst largest x _ Hi Hx Hrange.
  unfold largest_prime_prefix.
  repeat split; try lia.
  right. exists i. split; [lia | exact Hx].
Qed.

Lemma prime_scan_state_init : forall x,
  1 < x <= INT_MAX ->
  prime_scan_state x 2 1.
Proof.
  intros.
  unfold prime_scan_state.
  lia.
Qed.

Lemma prime_scan_state_step_keep : forall x j prime,
  prime_scan_state x j prime ->
  j <= x / j ->
  prime_scan_state x (j + 1) prime.
Proof.
  intros x j prime Hstate Hcond.
  unfold prime_scan_state in *.
  assert (x / j <= x).
  { apply Z.div_le_upper_bound; nia. }
  lia.
Qed.

Lemma prime_scan_state_step_zero : forall x j prime,
  prime_scan_state x j prime ->
  j <= x / j ->
  prime_scan_state x (j + 1) 0.
Proof.
  intros x j prime Hstate Hcond.
  unfold prime_scan_state in *.
  assert (x / j <= x).
  { apply Z.div_le_upper_bound; nia. }
  lia.
Qed.

Lemma sum_digits_fuel_z_nonneg : forall n fuel,
  0 <= sum_digits_fuel_z n fuel.
Proof.
  intros n fuel.
  revert n.
  induction fuel; intros n; simpl.
  - lia.
  - destruct (Z.leb n 0) eqn:Hleb.
    + lia.
    + apply Z.leb_gt in Hleb.
      pose proof (IHfuel (n / 10)) as Hrec.
      assert (0 <= n mod 10 < 10) by (apply Z.mod_pos_bound; lia).
      lia.
Qed.

Lemma sum_digits_fuel_z_upper : forall n fuel,
  sum_digits_fuel_z n fuel <= 9 * Z.of_nat fuel.
Proof.
  intros n fuel.
  revert n.
  induction fuel; intros n; simpl.
  - lia.
  - destruct (Z.leb n 0) eqn:Hleb.
    + lia.
    + apply Z.leb_gt in Hleb.
      pose proof (IHfuel (n / 10)) as Hrec.
      assert (0 <= n mod 10 < 10) by (apply Z.mod_pos_bound; lia).
      lia.
Qed.

Lemma digit_sum_state_init : forall n,
  digit_sum_int_range n ->
  digit_sum_state n n 0.
Proof.
  intros n Hrange.
  unfold digit_sum_int_range, digit_sum_state in *.
  split.
  - lia.
  - exists 11%nat.
    assert (Hpow: n < 10 ^ (Z.of_nat 11)).
    { change (10 ^ (Z.of_nat 11)) with 100000000000. lia. }
    assert (Hsum: sum_digits_fuel_z n 11 <= 100).
    {
      pose proof (sum_digits_fuel_z_upper n 11) as Hup.
      change (9 * Z.of_nat 11) with 99 in Hup.
      lia.
    }
    lia.
Qed.

Lemma digit_sum_state_step : forall original current sum,
  digit_sum_state original current sum ->
  current > 0 ->
  digit_sum_state original (current / 10) (sum + current mod 10).
Proof.
  intros original current sum Hstate Hpos.
  unfold digit_sum_state in *.
  destruct Hstate as [Horig [fuel [Hcur [Hsum [Hpow Hbound]]]]].
  assert (Hfuel_pos: fuel <> O).
  {
    intro Hfuel0.
    subst fuel.
    simpl in Hpow.
    lia.
  }
  destruct fuel.
  - contradiction.
  - assert (Hdiv_nonneg: 0 <= current / 10) by (apply Z.div_pos; lia).
    assert (Hmod_bounds: 0 <= current mod 10 < 10) by (apply Z.mod_pos_bound; lia).
    assert (Hpow_step: current / 10 < 10 ^ (Z.of_nat fuel)).
    {
      assert (Hcur_lt: current < 10 * (10 ^ (Z.of_nat fuel))).
      {
        replace (Z.of_nat (S fuel)) with (Z.of_nat fuel + 1) in Hpow by lia.
        rewrite Z.pow_add_r in Hpow by lia.
        change (10 ^ 1) with 10 in Hpow.
        lia.
      }
      apply Z.div_lt_upper_bound; nia.
    }
    assert (Hunfold:
      sum_digits_fuel_z current (S fuel) =
        current mod 10 + sum_digits_fuel_z (current / 10) fuel).
    {
      simpl.
      assert (Hleb: (current <=? 0) = false).
      { apply Z.leb_gt. lia. }
      rewrite Hleb.
      reflexivity.
    }
    split.
    + exact Horig.
    + exists fuel.
      rewrite Hunfold in Hbound.
      nia.
Qed.

Lemma problem_94_spec_z_of_digit_state : forall lst largest out,
  largest_prime_prefix (Zlength lst) lst largest ->
  digit_sum_int_range largest ->
  digit_sum_state largest 0 out ->
  problem_94_spec_z lst out.
Proof.
  intros lst largest out Hpref Hrange Hstate.
  unfold problem_94_spec_z, digit_sum_state in *.
  destruct Hstate as [_ [fuel [Hcur [Hout [Hpow Hbound]]]]].
  assert (Hnonneg: 0 <= sum_digits_fuel_z 0 fuel) by apply sum_digits_fuel_z_nonneg.
  split.
  - replace out with (out + sum_digits_fuel_z 0 fuel - sum_digits_fuel_z 0 fuel) by lia.
    lia.
  - exists largest.
    auto.
Qed.
