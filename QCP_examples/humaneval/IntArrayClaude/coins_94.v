Load "../spec/94".

From AUXLib Require Import List_lemma ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List.

Import naive_C_Rules.
Import ListNotations.
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
  ((largest = 0 /\
    forall k, 0 <= k < i -> ~ prime (Znth k lst 0)) \/
   (prime largest /\
    (exists k, 0 <= k < i /\ largest = Znth k lst 0) /\
    forall k, 0 <= k < i -> prime (Znth k lst 0) -> Znth k lst 0 <= largest)).

Definition prime_scan_state (x j prime : Z) : Prop :=
  1 < x <= INT_MAX /\
  2 <= j <= x + 1 /\
  0 <= prime <= 1 /\
  (prime <> 0 ->
   forall d, 2 <= d < j -> x mod d <> 0) /\
  (prime = 0 ->
   exists d, 2 <= d < j /\ d < x /\ x mod d = 0).

Definition digit_sum_int_range (n : Z) : Prop :=
  0 <= n <= INT_MAX.

Fixpoint sum_digits_fuel_z (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel0 =>
      if Z.leb n 0 then 0 else (n mod 10) + sum_digits_fuel_z (n / 10) fuel0
  end.

Definition digit_sum_state (original current sum : Z) : Prop :=
  0 <= original <= INT_MAX /\
  exists fuel : nat,
    0 <= current /\
    0 <= sum /\
    current < 10 ^ (Z.of_nat fuel) /\
    sum + sum_digits_fuel_z current fuel <= 100 /\
    sum + Z.of_nat (sum_digits (Z.to_nat current)) =
      Z.of_nat (sum_digits (Z.to_nat original)).

Definition problem_94_spec_z (lst : list Z) (out : Z) : Prop :=
  problem_94_spec (map Z.to_nat lst) (Z.to_nat out).

Lemma prime_gt_1_94 : forall p,
  prime p -> 1 < p.
Proof.
  intros p Hprime.
  inversion Hprime.
  assumption.
Qed.

Lemma largest_prime_prefix_init : forall lst,
  0 <= Zlength lst ->
  largest_prime_prefix 0 lst 0.
Proof.
  intros lst Hlen.
  unfold largest_prime_prefix.
  repeat split; try lia.
  left.
  split.
  - reflexivity.
  - intros k Hk. lia.
Qed.

Lemma largest_prime_prefix_skip_not_prime : forall i lst largest,
  largest_prime_prefix i lst largest ->
  0 <= i < Zlength lst ->
  ~ prime (Znth i lst 0) ->
  largest_prime_prefix (i + 1) lst largest.
Proof.
  intros i lst largest Hpref Hi Hnot.
  unfold largest_prime_prefix in *.
  destruct Hpref as [Hi_bounds [Hlargest Hseen]].
  repeat split; try lia.
  destruct Hseen as [[Hzero Hnone] | [Hprime [Hin Hmax]]].
  - left.
    split.
    + exact Hzero.
    + intros k Hk.
    destruct (Z.eq_dec k i) as [-> | Hneq].
      * exact Hnot.
      * apply Hnone. lia.
  - right.
    split.
    + exact Hprime.
    + split.
      * destruct Hin as [k [Hk Hval]].
        exists k. split; [lia | exact Hval].
      * intros k Hk Hpk.
        destruct (Z.eq_dec k i) as [-> | Hneq].
        -- contradiction.
        -- apply Hmax; try assumption; lia.
Qed.

Lemma largest_prime_prefix_skip_le : forall i lst largest,
  largest_prime_prefix i lst largest ->
  0 <= i < Zlength lst ->
  Znth i lst 0 <= largest ->
  largest_prime_prefix (i + 1) lst largest.
Proof.
  intros i lst largest Hpref Hi Hle.
  unfold largest_prime_prefix in *.
  destruct Hpref as [Hi_bounds [Hlargest Hseen]].
  repeat split; try lia.
  destruct Hseen as [[Hzero Hnone] | [Hprime [Hin Hmax]]].
  - left.
    split.
    + exact Hzero.
    + intros k Hk Hpk.
    destruct (Z.eq_dec k i) as [-> | Hneq].
      * pose proof (prime_gt_1_94 _ Hpk). lia.
      * apply (Hnone k); try assumption; lia.
  - right.
    split.
    + exact Hprime.
    + split.
      * destruct Hin as [k [Hk Hval]].
        exists k. split; [lia | exact Hval].
      * intros k Hk Hpk.
        destruct (Z.eq_dec k i) as [-> | Hneq].
        -- exact Hle.
        -- apply Hmax; try assumption; lia.
Qed.

Lemma largest_prime_prefix_update : forall i lst largest x,
  largest_prime_prefix i lst largest ->
  0 <= i < Zlength lst ->
  x = Znth i lst 0 ->
  0 <= x <= INT_MAX ->
  prime x ->
  largest < x ->
  largest_prime_prefix (i + 1) lst x.
Proof.
  intros i lst largest x Hpref Hi Hx Hrange Hprime Hgt.
  unfold largest_prime_prefix in *.
  destruct Hpref as [Hi_bounds [Hlargest Hseen]].
  repeat split; try lia.
  right.
  split.
  - exact Hprime.
  - split.
    + exists i. split; [lia | exact Hx].
    + intros k Hk Hpk.
      destruct (Z.eq_dec k i) as [-> | Hneq].
      * rewrite <- Hx. lia.
      * destruct Hseen as [[Hzero Hnone] | [Hprime_old [Hin Hmax]]].
        -- exfalso. apply (Hnone k); try assumption; lia.
        -- assert (Znth k lst 0 <= largest) by (apply Hmax; try assumption; lia).
           lia.
Qed.

Lemma prime_scan_state_init : forall x,
  1 < x <= INT_MAX ->
  prime_scan_state x 2 1.
Proof.
  intros.
  unfold prime_scan_state.
  repeat split; try lia;
    try (intros _ d Hd; lia);
    try (intros Hzero; lia).
Qed.

Lemma prime_scan_state_step_keep : forall x j prime,
  prime_scan_state x j prime ->
  j <= x / j ->
  x mod j <> 0 ->
  prime_scan_state x (j + 1) prime.
Proof.
  intros x j prime Hstate Hcond Hmod.
  unfold prime_scan_state in *.
  destruct Hstate as [Hx [Hj [Hprime [Hnonzero Hzero]]]].
  assert (x / j <= x) by (apply Z.div_le_upper_bound; nia).
  split.
  - lia.
  - split.
    + lia.
    + split.
      * lia.
      * split.
        -- intros Hnz d Hd.
           destruct (Z.eq_dec d j) as [-> | Hneq].
           ++ exact Hmod.
           ++ apply Hnonzero; try assumption; lia.
        -- intros Hz.
           destruct (Hzero Hz) as [d [Hd [Hd_lt Hdiv]]].
           exists d. split; [lia | split; [exact Hd_lt | exact Hdiv]].
Qed.

Lemma prime_scan_state_step_zero : forall x j prime,
  prime_scan_state x j prime ->
  j <= x / j ->
  x mod j = 0 ->
  prime_scan_state x (j + 1) 0.
Proof.
  intros x j prime Hstate Hcond Hmod.
  unfold prime_scan_state in *.
  destruct Hstate as [Hx [Hj [_ _]]].
  assert (x / j <= x) by (apply Z.div_le_upper_bound; nia).
  split.
  - lia.
  - split.
    + lia.
    + split.
      * lia.
      * split.
        -- intros Hnz. lia.
        -- intros _.
           exists j.
           split.
           ++ lia.
           ++ split.
              ** assert (j * j <= x).
                 {
                   assert (j * j <= j * (x / j)).
                   { apply Z.mul_le_mono_nonneg_l; lia. }
                   pose proof (Z.mul_div_le x j ltac:(lia)).
                   nia.
                 }
                 nia.
              ** exact Hmod.
Qed.

Lemma divide_trans_94 : forall a b c,
  (a | b) -> (b | c) -> (a | c).
Proof.
  intros a b c [x Hx] [y Hy].
  exists (y * x).
  rewrite Hy, Hx.
  ring.
Qed.

Lemma exists_prime_divisor_94 : forall n,
  1 < n ->
  exists p, prime p /\ (p | n) /\ 2 <= p <= n.
Proof.
  apply (well_founded_induction
           (Z.lt_wf 0)
           (fun n => 1 < n -> exists p, prime p /\ (p | n) /\ 2 <= p <= n)).
  intros n IH Hn.
  destruct (prime_dec n) as [Hprime | Hnot].
  - exists n.
    split.
    + exact Hprime.
    + split.
      * exists 1. lia.
      * lia.
  - destruct (not_prime_divide n Hn Hnot) as [d [[Hd_gt Hd_lt] Hdiv]].
    assert (Hrec : 0 <= d < n) by lia.
    destruct (IH d Hrec ltac:(lia)) as [p [Hp [Hpdiv Hrange]]].
    exists p.
    split.
    + exact Hp.
    + split.
      * eapply divide_trans_94; eauto.
      * lia.
Qed.

Lemma composite_small_prime_divisor_94 : forall n,
  1 < n ->
  ~ prime n ->
  exists p, prime p /\ (p | n) /\ 2 <= p < n /\ p <= n / p.
Proof.
  intros n Hn Hnot.
  destruct (not_prime_divide n Hn Hnot) as [d [[Hd_gt Hd_lt] Hdiv]].
  destruct Hdiv as [q Hn_eq].
  assert (Hd_pos : 0 < d) by lia.
  assert (Hq_gt1 : 1 < q).
  {
    destruct (Z_le_gt_dec q 1) as [Hq_le | Hq_gt].
    - assert (q <= 0 \/ q = 1) as Hq_case by lia.
      destruct Hq_case as [Hqle | Hqeq].
      + nia.
      + subst q. nia.
    - lia.
  }
  assert (Hq_pos : 0 < q) by lia.
  assert (Hd_case : d <= q \/ q < d) by lia.
  destruct Hd_case as [Hd_le_q | Hq_lt_d].
  - destruct (exists_prime_divisor_94 d ltac:(lia)) as [p [Hp [Hpdiv [Hp_ge Hp_le]]]].
    exists p.
    split.
    + exact Hp.
    + split.
      * eapply divide_trans_94; eauto. exists q. exact Hn_eq.
      * split.
        -- lia.
        -- assert (p <= d) by lia.
           assert (d <= n / d).
           {
             apply Z.div_le_lower_bound; nia.
           }
           assert (n / d <= n / p).
           {
             apply Z.div_le_lower_bound; try lia.
             pose proof (Z.mul_div_le n d ltac:(lia)).
             nia.
           }
           lia.
  - destruct (exists_prime_divisor_94 q ltac:(lia)) as [p [Hp [Hpdiv [Hp_ge Hp_le]]]].
    exists p.
    split.
    + exact Hp.
    + split.
      * destruct Hpdiv as [m Hq_eq].
        exists (d * m).
        rewrite Hn_eq, Hq_eq.
        ring.
      * split.
        -- lia.
        -- assert (p <= q) by lia.
           assert (q <= n / q).
           {
             rewrite Hn_eq.
             apply Z.div_le_lower_bound; nia.
           }
           assert (n / q <= n / p).
           {
             apply Z.div_le_lower_bound; try lia.
             pose proof (Z.mul_div_le n q ltac:(lia)).
             nia.
           }
           lia.
Qed.

Lemma prime_scan_state_zero_not_prime : forall x j,
  prime_scan_state x j 0 ->
  ~ prime x.
Proof.
  intros x j Hstate Hprime.
  unfold prime_scan_state in Hstate.
  destruct Hstate as [_ [_ [_ [_ Hzero]]]].
  destruct (Hzero eq_refl) as [d [Hd [Hd_lt Hmod]]].
  assert (Hdiv : (d | x)).
  { apply Z.mod_divide; lia. }
  pose proof (prime_divisors x Hprime d Hdiv) as [Heq | [Heq | [Heq | Heq]]]; lia.
Qed.

Lemma prime_scan_state_exit_prime : forall x j flag,
  prime_scan_state x j flag ->
  flag <> 0 ->
  j > x / j ->
  prime x.
Proof.
  intros x j flag Hstate Hflag Hexit.
  destruct (prime_dec x) as [Hprime | Hnot].
  - exact Hprime.
  - 
    unfold prime_scan_state in Hstate.
    destruct Hstate as [Hx [Hj [_ [Hnodiv _]]]].
    destruct (composite_small_prime_divisor_94 x ltac:(lia) Hnot)
      as [p [Hp [Hdiv [[Hp_ge Hp_lt] Hp_le_div]]]].
    assert (Hp_lt_j : p < j).
    {
      destruct (Z_lt_ge_dec p j) as [Hlt | Hge].
      - exact Hlt.
      - exfalso.
        assert (x / p <= x / j).
        {
          apply Z.div_le_lower_bound.
          - lia.
          - assert (0 <= x / p) by (apply Z.div_pos; lia).
            assert (j * (x / p) <= p * (x / p)).
            { apply Z.mul_le_mono_nonneg_r; lia. }
            pose proof (Z.mul_div_le x p ltac:(lia)).
            nia.
        }
        lia.
    }
    specialize (Hnodiv Hflag p ltac:(lia)).
    exfalso.
    apply Hnodiv.
    apply Z.mod_divide.
    + lia.
    + exact Hdiv.
Qed.

Lemma prime_scan_state_exit_prime_intmax : forall x j flag,
  prime_scan_state x j flag ->
  flag <> 0 ->
  j >= INT_MAX ->
  prime x.
Proof.
  intros x j flag Hstate Hflag Hjmax.
  eapply prime_scan_state_exit_prime; eauto.
  unfold prime_scan_state in Hstate.
  destruct Hstate as [Hx [Hj _]].
  assert (x / j <= 1).
  {
    apply Z.div_le_upper_bound; nia.
  }
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

Lemma sum_digits_fueled_ge : forall n fuel,
  (n <= fuel)%nat ->
  sum_digits_fueled n fuel = sum_digits n.
Proof.
  apply (well_founded_induction
           lt_wf
           (fun n => forall fuel, (n <= fuel)%nat ->
              sum_digits_fueled n fuel = sum_digits n)).
  intros n IH fuel Hle.
  destruct n.
  - destruct fuel; reflexivity.
  - destruct fuel.
    + lia.
    + unfold sum_digits at 1.
      simpl.
      assert (Hlt : (((S n) / 10) < S n)%nat).
      { apply Nat.div_lt; lia. }
      change ((S n mod 10 + sum_digits_fueled (S n / 10) fuel)%nat =
              (S n mod 10 + sum_digits_fueled (S n / 10) n)%nat).
      rewrite (IH ((S n) / 10)%nat Hlt fuel) by lia.
      rewrite (IH ((S n) / 10)%nat Hlt n).
      * reflexivity.
      * destruct n.
        -- simpl. lia.
        -- apply Nat.div_le_upper_bound; lia.
Qed.

Lemma sum_digits_step_nat : forall n,
  n <> O ->
  sum_digits n = (n mod 10 + sum_digits (n / 10))%nat.
Proof.
  intros n Hn.
  destruct n.
  - contradiction.
  - unfold sum_digits at 1.
    simpl.
    rewrite sum_digits_fueled_ge.
    + reflexivity.
    + destruct n.
      * simpl. lia.
      * assert (Hdiv : (S (S n) / 10 <= S n)%nat).
        { apply Nat.div_le_upper_bound; lia. }
        exact Hdiv.
Qed.

Lemma sum_digits_step_Z : forall current,
  current > 0 ->
  Z.of_nat (sum_digits (Z.to_nat current)) =
    current mod 10 + Z.of_nat (sum_digits (Z.to_nat (current / 10))).
Proof.
  intros current Hpos.
  assert (Hnat_pos : Z.to_nat current <> O) by lia.
  rewrite sum_digits_step_nat by exact Hnat_pos.
  rewrite Nat2Z.inj_add.
  rewrite Nat2Z.inj_mod by lia.
  rewrite Z2Nat.id by lia.
  rewrite Z2Nat.inj_div by lia.
  reflexivity.
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
    repeat split; try lia.
Qed.

Lemma digit_sum_state_step : forall original current sum,
  digit_sum_state original current sum ->
  current > 0 ->
  digit_sum_state original (current / 10) (sum + current mod 10).
Proof.
  intros original current sum Hstate Hpos.
  unfold digit_sum_state in *.
  destruct Hstate as [Horig [fuel [Hcur [Hsum [Hpow [Hbound Heq]]]]]].
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
      split.
      * lia.
      * split.
        -- lia.
        -- split.
           ++ exact Hpow_step.
           ++ split.
              ** rewrite Hunfold in Hbound.
                 lia.
              ** rewrite <- Heq.
                 rewrite (sum_digits_step_Z current) by lia.
                 ring.
Qed.

Lemma Znth_In_range_94 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma In_Znth_exists_94 : forall (x : Z) l,
  In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l 0 = x.
Proof.
  intros x l Hin.
  apply In_nth_error in Hin.
  destruct Hin as [n Hn].
  exists (Z.of_nat n).
  split.
  - assert ((n < length l)%nat) as Hlt.
    { apply nth_error_Some. rewrite Hn. discriminate. }
    rewrite Zlength_correct.
    lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    apply nth_error_nth with (d := 0) in Hn.
    exact Hn.
Qed.

Lemma problem_94_spec_z_of_digit_state : forall lst largest out,
  list_nonneg_int_range lst ->
  largest_prime_prefix (Zlength lst) lst largest ->
  digit_sum_int_range largest ->
  digit_sum_state largest 0 out ->
  problem_94_spec_z lst out.
Proof.
  intros lst largest out Hlst_range Hpref Hrange Hstate.
  unfold problem_94_spec_z.
  unfold digit_sum_state in Hstate.
  destruct Hstate as [Horig [fuel [Hcur [Hout [Hpow [Hbound Hsum_eq]]]]]].
  unfold largest_prime_prefix in Hpref.
  destruct Hpref as [Hbounds [Hlargest Hcase]].
  destruct Hcase as [[Hzero Hnone] | [Hprime [Hin Hmax]]].
  - right.
    split.
    + intros p Hp Hprime_p.
      apply in_map_iff in Hp.
      destruct Hp as [z [Hp Hz_in]].
      destruct (In_Znth_exists_94 z lst Hz_in) as [k [Hk Hz]].
      subst p.
      assert (Hz_nonneg : 0 <= z).
      {
        rewrite <- Hz.
        pose proof (Hlst_range k Hk).
        lia.
      }
      apply (Hnone k).
      * lia.
      * rewrite Hz.
        rewrite <- (Z2Nat.id z) by lia.
        exact Hprime_p.
    + simpl in Hsum_eq.
      rewrite Hzero in Hsum_eq.
      simpl in Hsum_eq.
      assert (out = 0) by lia.
      subst out.
      reflexivity.
  - left.
    exists (Z.to_nat largest).
    split.
    + destruct Hin as [k [Hk Hval]].
      apply in_map.
      rewrite Hval.
      apply Znth_In_range_94.
      lia.
    + split.
      * rewrite Z2Nat.id by lia.
        exact Hprime.
      * split.
        -- intros p' Hp' Hprime_p'.
           apply in_map_iff in Hp'.
           destruct Hp' as [z [Hp' Hz_in]].
           destruct (In_Znth_exists_94 z lst Hz_in) as [k [Hk Hz]].
           subst p'.
           assert (Hz_nonneg : 0 <= z).
           {
             rewrite <- Hz.
             pose proof (Hlst_range k Hk).
             lia.
           }
           assert (Hprime_z : prime z).
           {
             rewrite <- (Z2Nat.id z) by lia.
             exact Hprime_p'.
           }
           assert (Hz_le : z <= largest).
           {
             assert (Hprime_k : prime (Znth k lst 0)).
             { rewrite Hz. exact Hprime_z. }
             pose proof (Hmax k Hk Hprime_k).
             lia.
           }
           apply Z2Nat.inj_le; lia.
        -- simpl in Hsum_eq.
           apply Nat2Z.inj.
           rewrite Z2Nat.id by lia.
           lia.
Qed.
