Load "../spec/145".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.ZArith.Zquot.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition Zabs (x : Z) : Z := Z.abs x.

Definition problem_145_pre_z (input : list Z) : Prop :=
  problem_145_pre input.

Definition problem_145_spec_z (input output : list Z) : Prop :=
  problem_145_spec input output.

Definition order_by_points_safe_145 (input : list Z) : Prop :=
  forall i,
    0 <= i < Zlength input ->
    INT_MIN < Znth i input 0 < INT_MAX.

Definition signed_digit_score_result_145 (x score : Z) : Prop :=
  signed_digit_sum x score.

Definition first_digit_state_145 (x t : Z) : Prop :=
  0 <= t <= x /\
  ((x = 0 /\ t = 0) \/ (0 < x /\ 1 <= t)) /\
  exists k tail,
    0 <= k /\
    0 <= tail < 10 ^ k /\
    x = t * 10 ^ k + tail.

Definition highest_power10_state_145 (x t p sum : Z) : Prop :=
  t = Z.abs x /\
  exists msd k tail r,
    0 <= k /\
    0 <= r <= k /\
    1 <= msd < 10 /\
    0 <= tail < 10 ^ k /\
    t = msd * 10 ^ k + tail /\
    p = 10 ^ r /\
    sum = if x <? 0 then - msd else msd.

Definition signed_digit_tail_state_145 (x t sum : Z) : Prop :=
  exists final size,
    signed_digit_sum x final /\
    0 <= size /\
    0 <= t < 10 ^ size /\
    sum + digit_sum_list (Z_to_list 10 t (Z.to_nat size)) = final /\
    INT_MIN < final /\ final < INT_MAX.

Definition order_copy_prefix_145
  (i : Z) (input output : list Z) : Prop :=
  0 <= i <= Zlength input /\
  Zlength output = i /\
  output = sublist 0 i input.

Definition score_prefix_rel_145 (input scores : list Z) : Prop :=
  Zlength scores = Zlength input /\
  forall i,
    0 <= i < Zlength input ->
    signed_digit_score_result_145 (Znth i input 0) (Znth i scores 0).

Definition order_score_prefix_145
  (i : Z) (input scores : list Z) : Prop :=
  0 <= i <= Zlength input /\
  Zlength scores = i /\
  score_prefix_rel_145 (sublist 0 i input) scores.

Definition score_pairs_145 (output scores : list Z) : list (Z * Z) :=
  combine output scores.

Definition pair_values_145 (pairs : list (Z * Z)) : list Z :=
  map fst pairs.

Definition pair_scores_145 (pairs : list (Z * Z)) : list Z :=
  map snd pairs.

Definition should_swap_pair_145 (p1 p2 : Z * Z) : bool :=
  if snd p1 >? snd p2 then true else false.

Definition swap_adjacent_pair_145 (j : nat) (pairs : list (Z * Z)) : list (Z * Z) :=
  match nth_error pairs j, nth_error pairs (S j) with
  | Some p1, Some p2 =>
      if should_swap_pair_145 p1 p2
      then firstn j pairs ++ p2 :: p1 :: skipn (S (S j)) pairs
      else pairs
  | _, _ => pairs
  end.

Fixpoint bubble_pass_pairs_from_145
  (fuel j : nat) (pairs : list (Z * Z)) : list (Z * Z) :=
  match fuel with
  | O => pairs
  | S fuel' => bubble_pass_pairs_from_145 fuel' (S j) (swap_adjacent_pair_145 j pairs)
  end.

Definition bubble_pass_pairs_145 (pairs : list (Z * Z)) : list (Z * Z) :=
  bubble_pass_pairs_from_145 (length pairs - 1)%nat 0 pairs.

Fixpoint bubble_sort_pairs_fuel_145
  (fuel : nat) (pairs : list (Z * Z)) : list (Z * Z) :=
  match fuel with
  | O => pairs
  | S fuel' => bubble_sort_pairs_fuel_145 fuel' (bubble_pass_pairs_145 pairs)
  end.

Definition bubble_outer_pairs_145
  (i : Z) (input initial_scores output scores : list Z) : Prop :=
  let pairs :=
    bubble_sort_pairs_fuel_145 (Z.to_nat i)
      (score_pairs_145 input initial_scores) in
  output = pair_values_145 pairs /\
  scores = pair_scores_145 pairs.

Definition order_outer_state_145
  (i : Z) (input initial_scores output scores : list Z) : Prop :=
  0 <= i <= Zlength input /\
  Zlength output = Zlength input /\
  Zlength scores = Zlength input /\
  score_prefix_rel_145 input initial_scores /\
  bubble_outer_pairs_145 i input initial_scores output scores /\
  (i = Zlength input -> problem_145_spec_z input output).

Definition bubble_inner_pairs_145
  (i j : Z) (input initial_scores output scores : list Z) : Prop :=
  exists outer_pairs,
    outer_pairs = bubble_sort_pairs_fuel_145
      (Z.to_nat i) (score_pairs_145 input initial_scores) /\
    output = pair_values_145
      (bubble_pass_pairs_from_145 (Z.to_nat (j - 1)) 0 outer_pairs) /\
    scores = pair_scores_145
      (bubble_pass_pairs_from_145 (Z.to_nat (j - 1)) 0 outer_pairs).

Definition order_inner_state_145
  (i j : Z) (input initial_scores output scores : list Z) : Prop :=
  0 <= i < Zlength input /\
  1 <= j <= Zlength input /\
  Zlength output = Zlength input /\
  Zlength scores = Zlength input /\
  score_prefix_rel_145 input initial_scores /\
  bubble_inner_pairs_145 i j input initial_scores output scores.

Lemma Zquot_eq_Zdiv_nonneg_145 : forall a b,
  0 <= a ->
  0 < b ->
  Z.quot a b = a / b.
Proof.
  intros a b Ha Hb.
  apply Zquot_Zdiv_pos; lia.
Qed.

Lemma Zrem_eq_Zmod_nonneg_145 : forall a b,
  0 <= a ->
  0 < b ->
  Z.rem a b = a mod b.
Proof.
  intros a b Ha Hb.
  apply Z.rem_mod_nonneg; lia.
Qed.

Lemma digit_sum_list_app_145 : forall l1 l2,
  digit_sum_list (l1 ++ l2) =
  digit_sum_list l1 + digit_sum_list l2.
Proof.
  assert (Hacc : forall l acc,
    fold_left Z.add l acc = acc + fold_left Z.add l 0).
  {
    induction l as [|x xs IH]; intros acc; cbn; [lia|].
    rewrite IH, (IH x).
    lia.
  }
  intros l1 l2.
  unfold digit_sum_list.
  rewrite fold_left_app.
  rewrite Hacc.
  lia.
Qed.

Lemma digit_sum_list_single_145 : forall x,
  digit_sum_list [x] = x.
Proof. intros; cbn; lia. Qed.

Lemma digit_sum_list_Z_to_list_zero_145 : forall size,
  0 <= size ->
  digit_sum_list (Z_to_list 10 0 (Z.to_nat size)) = 0.
Proof.
  intros size _.
  assert (Hnat : forall n,
    digit_sum_list (Z_to_list 10 0 n) = 0).
  {
    unfold digit_sum_list.
    induction n; cbn.
    - lia.
    - rewrite IHn; lia.
  }
  apply Hnat.
Qed.

Lemma digit_sum_list_Z_to_list_step_145 : forall t size,
  0 < t ->
  0 < size ->
  t < 10 ^ size ->
  digit_sum_list (Z_to_list 10 t (Z.to_nat size)) =
    Z.rem t 10 +
    digit_sum_list (Z_to_list 10 (Z.quot t 10) (Z.to_nat (size - 1))).
Proof.
  intros t size Ht Hsize Hbound.
  assert (Hacc : forall l acc,
    fold_left Z.add l acc = acc + fold_left Z.add l 0).
  {
    induction l as [|x xs IH]; intros acc; cbn; [lia|].
    rewrite IH, (IH x); lia.
  }
  assert (Hz : Z.to_nat size = S (Z.to_nat (size - 1))) by lia.
  rewrite Hz.
  unfold digit_sum_list at 1.
  cbn.
  rewrite Zrem_eq_Zmod_nonneg_145 by lia.
  rewrite Zquot_eq_Zdiv_nonneg_145 by lia.
  replace (Z.to_nat (size - 1)) with (Z.to_nat size - 1)%nat by lia.
  rewrite Hacc.
  reflexivity.
Qed.

Lemma first_digit_state_145_start : forall x,
  0 <= x ->
  first_digit_state_145 x x.
Proof.
  intros x Hx.
  unfold first_digit_state_145.
  split; [lia|].
  split.
  - destruct (Z.eq_dec x 0); [left; lia|right; lia].
  - exists 0, 0.
    cbn.
    repeat split; lia.
Qed.

Lemma first_digit_state_145_step : forall x t,
  t >= 10 ->
  first_digit_state_145 x t ->
  first_digit_state_145 x (Z.quot t 10).
Proof.
  intros x t Ht Hstate.
  unfold first_digit_state_145 in *.
  destruct Hstate as [Ht_bounds [Hcanon [k [tail [Hk [Htail Hx]]]]]].
  pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)) as Hrem.
  pose proof (Z.quot_rem t 10 ltac:(lia)) as Hqr.
  assert (Hq_nonneg : 0 <= Z.quot t 10) by (apply Z.quot_pos; lia).
  assert (Hq_pos : 1 <= Z.quot t 10).
  {
    apply Z.quot_le_lower_bound; lia.
  }
  split.
  - split.
    + exact Hq_nonneg.
    + rewrite Hx.
      assert (0 < 10 ^ k) by (apply Z.pow_pos_nonneg; lia).
      nia.
  - split.
    + destruct Hcanon as [[Hx0 Ht0] | [Hxpos _]]; [lia|right; lia].
    + exists (k + 1), (Z.rem t 10 * 10 ^ k + tail).
      repeat split.
      * lia.
      * assert (0 <= 10 ^ k) by (apply Z.pow_nonneg; lia).
        nia.
      * rewrite Z.pow_add_r by lia.
        change (10 ^ 1) with 10.
        nia.
      * rewrite Z.pow_add_r by lia.
        change (10 ^ 1) with 10.
        nia.
Qed.

Lemma first_digit_state_145_small_eq : forall x t,
  first_digit_state_145 x t ->
  x < 10 ->
  t = x.
Proof.
  intros x t Hstate Hsmall.
  unfold first_digit_state_145 in Hstate.
  destruct Hstate as [[Ht_nonneg Ht_le] [Hcanon [k [tail [Hk [Htail Hx]]]]]].
  destruct Hcanon as [[Hx0 Ht0] | [Hxpos Htpos]]; [lia|].
  destruct (Z.eq_dec k 0) as [Hk0 | Hkne].
  - subst k.
    cbn in Htail, Hx.
    lia.
  - assert (Hk_pos : 1 <= k) by lia.
    assert (Hpow_ge : 10 <= 10 ^ k).
    {
      replace 10 with (10 ^ 1) by reflexivity.
      apply Z.pow_le_mono_r; lia.
    }
    assert (10 <= t * 10 ^ k) by nia.
    nia.
Qed.

Lemma decimal_digits_single_145 : forall x d,
  d = Z.abs x ->
  0 <= d < 10 ->
  decimal_digits x [d].
Proof.
  intros x d Hd Hd_bounds.
  unfold decimal_digits.
  split.
  - cbn; lia.
  - split.
    + rewrite (list_to_Z_single 10 d). lia.
    + destruct (Z.eq_dec x 0) as [Hx0|Hxne].
      * left.
        subst x.
        rewrite Z.abs_0 in Hd.
        split; [reflexivity|].
        f_equal; lia.
      * right.
        split; [assumption|].
        split; [discriminate|].
        cbn.
        intro Hlast.
        assert (Z.abs x = 0) by lia.
        destruct x; cbn in H; lia.
Qed.

Lemma signed_digit_sum_single_pos_145 : forall x d,
  0 <= x ->
  d = Z.abs x ->
  0 <= d < 10 ->
  signed_digit_sum x d.
Proof.
  intros x d Hx Hd Hd_bounds.
  unfold signed_digit_sum.
  exists [d].
  split.
  - apply decimal_digits_single_145; assumption.
  - right.
    split; [lia|].
    cbn; lia.
Qed.

Lemma signed_digit_sum_single_neg_145 : forall x d,
  x < 0 ->
  d = Z.abs x ->
  0 <= d < 10 ->
  signed_digit_sum x (- d).
Proof.
  intros x d Hx Hd Hd_bounds.
  unfold signed_digit_sum.
  exists [d].
  split.
  - apply decimal_digits_single_145; assumption.
  - left.
    split; [lia|].
    cbn; lia.
Qed.

Lemma first_digit_state_145_to_high_pos : forall x ax msd,
  ax = Z.abs x ->
  ax >= 10 ->
  first_digit_state_145 ax msd ->
  msd < 10 ->
  0 <= x ->
  highest_power10_state_145 x ax 1 msd.
Proof.
  intros x ax msd Hax Hax_ge Hstate Hmsd_lt Hx.
  unfold first_digit_state_145 in Hstate.
  destruct Hstate as [Hmsd_bounds [Hcanon [k [tail [Hk [Htail Hdecomp]]]]]].
  unfold highest_power10_state_145.
  split; [assumption|].
  exists msd, k, tail, 0.
  assert (Hmsd_pos : 1 <= msd).
  { destruct Hcanon as [[Hzero _] | [_ Hmsd_pos]]; lia. }
  cbn.
  repeat split; try lia; try assumption; try reflexivity;
    try (destruct (x <? 0) eqn:Hxlt;
      [apply Z.ltb_lt in Hxlt; lia|reflexivity]).
Qed.

Lemma first_digit_state_145_to_high_neg : forall x ax msd,
  ax = Z.abs x ->
  ax >= 10 ->
  first_digit_state_145 ax msd ->
  msd < 10 ->
  x < 0 ->
  highest_power10_state_145 x ax 1 (- msd).
Proof.
  intros x ax msd Hax Hax_ge Hstate Hmsd_lt Hx.
  unfold first_digit_state_145 in Hstate.
  destruct Hstate as [Hmsd_bounds [Hcanon [k [tail [Hk [Htail Hdecomp]]]]]].
  unfold highest_power10_state_145.
  split; [assumption|].
  exists msd, k, tail, 0.
  assert (Hmsd_pos : 1 <= msd).
  { destruct Hcanon as [[Hzero _] | [_ Hmsd_pos]]; lia. }
  cbn.
  repeat split; try lia; try assumption; try reflexivity;
    try (destruct (x <? 0) eqn:Hxlt;
      [reflexivity|apply Z.ltb_ge in Hxlt; lia]).
Qed.

Lemma highest_power10_state_145_step : forall x t p sum,
  p <= Z.quot t 10 ->
  highest_power10_state_145 x t p sum ->
  highest_power10_state_145 x t (p * 10) sum.
Proof.
  intros x t p sum Hcond Hstate.
  unfold highest_power10_state_145 in *.
  destruct Hstate as [Ht_abs Hstate].
  destruct Hstate as [msd [k [tail [r Hstate]]]].
  destruct Hstate as [Hk [Hr [Hmsd [Htail [Ht [Hp Hsum]]]]]].
  split; [exact Ht_abs|].
  exists msd, k, tail, (r + 1).
  assert (Hr_lt : r < k).
  {
    destruct (Z.eq_dec r k) as [Heq|Hneq]; [|lia].
    subst r.
    assert (Hp10 : p = 10 ^ k) by exact Hp.
    assert (Ht_lt : t < p * 10).
    {
      rewrite Hp10, Ht.
      assert (0 < 10 ^ k) by (apply Z.pow_pos_nonneg; lia).
      nia.
    }
    assert (Hq_lt : Z.quot t 10 < p).
    {
      apply Z.quot_lt_upper_bound; try lia.
    }
    lia.
  }
  repeat split; try lia.
  - rewrite Hp.
    rewrite Z.pow_add_r by lia.
    change (10 ^ 1) with 10.
    ring.
Qed.

Lemma highest_power10_state_145_exit_index : forall x t p msd k tail r,
  p > Z.quot t 10 ->
  t = Z.abs x ->
  0 <= k ->
  0 <= r <= k ->
  1 <= msd < 10 ->
  0 <= tail < 10 ^ k ->
  t = msd * 10 ^ k + tail ->
  p = 10 ^ r ->
  r = k.
Proof.
  intros x t p msd k tail r Hexit _ Hk Hr Hmsd Htail Ht Hp.
  destruct (Z.eq_dec r k) as [|Hneq]; [assumption|].
  assert (Hrlt : r < k) by lia.
  assert (Hpow_le : 10 ^ r * 10 <= t).
  {
    rewrite Ht.
    assert (10 ^ (r + 1) <= 10 ^ k).
    { apply Z.pow_le_mono_r; lia. }
    rewrite Z.pow_add_r in H by lia.
    change (10 ^ 1) with 10 in H.
    nia.
  }
  assert (Hquot_ge : p <= Z.quot t 10).
  {
    rewrite Hp.
    apply Z.quot_le_lower_bound; try lia.
  }
  lia.
Qed.

Lemma removelast_app_single_145 : forall {A : Type} (l : list A) x,
  removelast (l ++ [x]) = l.
Proof.
  induction l as [|a l IH]; intros x; cbn.
  - reflexivity.
  - destruct l as [|b l].
    + reflexivity.
    + cbn in IH |- *.
      f_equal.
      apply IH.
Qed.

Lemma last_app_single_145 : forall {A : Type} (l : list A) x d,
  last (l ++ [x]) d = x.
Proof.
  induction l as [|a l IH]; intros x d; cbn.
  - reflexivity.
  - destruct l as [|b l].
    + reflexivity.
    + apply IH.
Qed.

Lemma fold_left_Zadd_acc_145 : forall l acc,
  fold_left Z.add l acc = acc + fold_left Z.add l 0.
Proof.
  induction l as [|a l IH]; intros acc; cbn; [lia|].
  rewrite IH.
  rewrite (IH a).
  lia.
Qed.

Lemma digit_sum_list_cons_145 : forall a l,
  digit_sum_list (a :: l) = a + digit_sum_list l.
Proof.
  intros a l.
  unfold digit_sum_list.
  cbn.
  rewrite fold_left_Zadd_acc_145.
  lia.
Qed.

Lemma digit_sum_list_Z_to_list_nonneg_145 : forall n size,
  0 <= n ->
  0 <= digit_sum_list (Z_to_list 10 n size).
Proof.
  intros n size Hn.
  revert n Hn.
  induction size as [|size IH]; intros n Hn.
  - change (Z_to_list 10 n 0%nat) with (@nil Z).
    unfold digit_sum_list; cbn; lia.
  - change (Z_to_list 10 n (S size)) with
      ((n mod 10) :: Z_to_list 10 (n / 10) size).
    rewrite digit_sum_list_cons_145.
  pose proof (Z.mod_pos_bound n 10 ltac:(lia)).
  pose proof (IH (n / 10) ltac:(apply Z.div_pos; lia)).
  lia.
Qed.

Lemma digit_sum_list_Z_to_list_le_145 : forall n size,
  0 <= n ->
  digit_sum_list (Z_to_list 10 n size) <= n.
Proof.
  intros n size Hn.
  revert n Hn.
  induction size as [|size IH]; intros n Hn.
  - change (Z_to_list 10 n 0%nat) with (@nil Z).
    unfold digit_sum_list; cbn; lia.
  - change (Z_to_list 10 n (S size)) with
      ((n mod 10) :: Z_to_list 10 (n / 10) size).
    rewrite digit_sum_list_cons_145.
  pose proof (Z.mod_pos_bound n 10 ltac:(lia)) as Hmod.
  pose proof (Z.div_pos n 10 ltac:(lia) ltac:(lia)) as Hdiv_nonneg.
  pose proof (IH (n / 10) Hdiv_nonneg) as IHn.
  pose proof (Z.div_mod n 10 ltac:(lia)) as Hdivmod.
  nia.
Qed.

Lemma highest_power10_state_145_to_tail : forall x t p sum,
  INT_MIN < x ->
  x < INT_MAX ->
  p > Z.quot t 10 ->
  highest_power10_state_145 x t p sum ->
  signed_digit_tail_state_145 x (Z.rem t p) sum.
Proof.
  intros x t p sum Hx_min Hx_max Hexit Hstate.
  unfold highest_power10_state_145 in Hstate.
  destruct Hstate as [Ht_abs Hstate].
  destruct Hstate as [msd [k [tail [r Hstate]]]].
  destruct Hstate as [Hk [Hr [Hmsd [Htail [Ht [Hp Hsum]]]]]].
  pose proof (highest_power10_state_145_exit_index x t p msd k tail r
    Hexit Ht_abs Hk Hr Hmsd Htail Ht Hp) as Hr_eq.
  subst r.
  assert (Hp_eq : p = 10 ^ k) by exact Hp.
  assert (Htail_rem : Z.rem t p = tail).
  {
    assert (Hp_pos : 0 < p) by (rewrite Hp_eq; apply Z.pow_pos_nonneg; lia).
    rewrite Ht.
    replace (msd * 10 ^ k + tail) with (tail + msd * p) by (rewrite Hp_eq; ring).
    rewrite Z.rem_add by nia.
    rewrite Z.rem_small; lia.
  }
  subst t.
  rewrite Htail_rem.
  set (lower_digits := Z_to_list 10 tail (Z.to_nat k)).
  assert (Hlower_len : Zlength lower_digits = k).
  {
    unfold lower_digits.
    rewrite Z_to_list_length.
    lia.
  }
  assert (Hlower_bound : list_within_bound 10 lower_digits).
  {
    unfold lower_digits.
    apply Z_to_list_within_bound; lia.
  }
  assert (Hlower_val : list_to_Z 10 lower_digits = tail).
  {
    unfold lower_digits.
    rewrite (Z_to_list_correct 10) by lia.
    replace (Z.of_nat (Z.to_nat k)) with k by lia.
    rewrite Z.mod_small; lia.
  }
  exists (sum + digit_sum_list lower_digits), k.
  repeat split.
  - unfold signed_digit_sum.
    exists (lower_digits ++ [msd]).
    split.
    + unfold decimal_digits.
      repeat split.
      * apply list_within_bound_concat; try assumption.
        cbn; lia.
      * rewrite list_to_Z_app by lia.
        rewrite Hlower_val, list_to_Z_single, Hlower_len.
        rewrite Ht.
        ring.
      * right.
        repeat split.
        -- intro Hx0.
           rewrite Hx0, Z.abs_0 in Ht.
           assert (0 < msd * 10 ^ k + tail).
           { assert (0 < 10 ^ k) by (apply Z.pow_pos_nonneg; lia). nia. }
           lia.
        -- destruct lower_digits; cbn; discriminate.
        -- rewrite last_app_single_145; lia.
    + destruct (Z_lt_ge_dec x 0) as [Hxneg|Hxnonneg].
      * left.
        split; [lia|].
        rewrite removelast_app_single_145, last_app_single_145.
        rewrite Hsum.
        destruct (x <? 0) eqn:Hxlt; [ring|].
        apply Z.ltb_ge in Hxlt; lia.
      * right.
        split; [lia|].
        rewrite digit_sum_list_app_145, digit_sum_list_single_145.
        rewrite Hsum.
        destruct (x <? 0) eqn:Hxlt; [|ring].
        apply Z.ltb_lt in Hxlt; lia.
  - lia.
  - lia.
  - lia.
  - unfold lower_digits in *.
    pose proof (digit_sum_list_Z_to_list_nonneg_145 tail (Z.to_nat k) ltac:(lia)) as Hdigit_nonneg.
    destruct (x <? 0) eqn:Hxlt;
      rewrite Hsum; pose proof Hmsd; lia.
  - unfold lower_digits in *.
    pose proof (digit_sum_list_Z_to_list_le_145 tail (Z.to_nat k) ltac:(lia)) as Hdigit_le.
    assert (Hpow_ge_1 : 1 <= 10 ^ k).
    {
      replace 1 with (10 ^ 0) by reflexivity.
      apply Z.pow_le_mono_r; lia.
    }
    change (Zabs x) with (Z.abs x) in Ht.
    destruct (x <? 0) eqn:Hxlt.
    + apply Z.ltb_lt in Hxlt.
      assert (Htail_lt_abs : tail < Z.abs x).
      {
        rewrite Ht.
        assert (0 < msd * 10 ^ k) by nia.
        nia.
      }
      assert (Z.abs x <= INT_MAX) by (apply Z.abs_le; lia).
      rewrite Hsum.
      nia.
    + apply Z.ltb_ge in Hxlt.
      assert (Z.abs x = x) by (apply Z.abs_eq; lia).
      rewrite Hsum.
      rewrite H in Ht.
      nia.
Qed.

Lemma signed_digit_tail_state_145_step : forall x t sum,
  t > 0 ->
  signed_digit_tail_state_145 x t sum ->
  signed_digit_tail_state_145 x (Z.quot t 10) (sum + Z.rem t 10).
Proof.
  intros x t sum Ht Hstate.
  unfold signed_digit_tail_state_145 in *.
  destruct Hstate as [final [size [Hfinal [Hsize [Ht_bound [Hsum Hfinal_bounds]]]]]].
  assert (Hsize_pos : 0 < size) by
    (destruct (Z.eq_dec size 0); subst; cbn in Ht_bound; lia).
  exists final, (size - 1).
  repeat split.
  - exact Hfinal.
  - lia.
  - apply Z.quot_pos; lia.
  - apply Z.quot_lt_upper_bound; try lia.
    rewrite <- Z.pow_succ_r by lia.
    replace (Z.succ (size - 1)) with size by lia.
    lia.
  - rewrite digit_sum_list_Z_to_list_step_145 in Hsum by lia.
    lia.
  - tauto.
  - tauto.
Qed.

Lemma signed_digit_tail_state_145_add_upper : forall x t sum,
  t > 0 ->
  signed_digit_tail_state_145 x t sum ->
  sum + Z.rem t 10 <= INT_MAX.
Proof.
  intros x t sum Ht Hstate.
  unfold signed_digit_tail_state_145 in Hstate.
  destruct Hstate as [final [size [Hfinal [Hsize [Ht_bound [Hsum [_ Hfinal_upper]]]]]]].
  assert (Hsize_pos : 0 < size) by
    (destruct (Z.eq_dec size 0); subst; cbn in Ht_bound; lia).
  rewrite digit_sum_list_Z_to_list_step_145 in Hsum by lia.
  pose proof (Z.quot_pos t 10 ltac:(lia) ltac:(lia)) as Hquot_nonneg.
  pose proof (digit_sum_list_Z_to_list_nonneg_145 (Z.quot t 10)
    (Z.to_nat (size - 1)) Hquot_nonneg) as Hrest_nonneg.
  lia.
Qed.

Lemma signed_digit_tail_state_145_final_bounds : forall x t sum,
  t = 0 ->
  signed_digit_tail_state_145 x t sum ->
  INT_MIN < sum /\ sum < INT_MAX.
Proof.
  intros x t sum Ht Hstate.
  subst t.
  unfold signed_digit_tail_state_145 in Hstate.
  destruct Hstate as [final [size [_ [Hsize [_ [Hsum Hbounds]]]]]].
  rewrite digit_sum_list_Z_to_list_zero_145 in Hsum by lia.
  replace (sum + 0) with sum in Hsum by lia.
  subst final.
  exact Hbounds.
Qed.

Lemma signed_digit_tail_state_145_done : forall x sum,
  signed_digit_tail_state_145 x 0 sum ->
  signed_digit_sum x sum.
Proof.
  intros x sum Hstate.
  unfold signed_digit_tail_state_145 in Hstate.
  destruct Hstate as [final [size [Hfinal [Hsize [_ [Hsum _]]]]]].
  rewrite digit_sum_list_Z_to_list_zero_145 in Hsum by lia.
  replace (sum + 0) with sum in Hsum by lia.
  subst final.
  exact Hfinal.
Qed.

Lemma order_by_points_safe_145_at : forall input i,
  order_by_points_safe_145 input ->
  0 <= i < Zlength input ->
  INT_MIN < Znth i input 0 < INT_MAX.
Proof. auto. Qed.

Lemma sublist_snoc_Znth_145 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  replace (sublist i (i + 1) l) with [Znth i l 0].
  - reflexivity.
  - symmetry; apply sublist_single; lia.
Qed.

Lemma order_copy_prefix_145_nil : forall input,
  order_copy_prefix_145 0 input [].
Proof.
  intros; unfold order_copy_prefix_145, sublist; cbn; repeat split; try lia.
  rewrite Zlength_correct; lia.
Qed.

Lemma order_copy_prefix_145_step : forall i input output,
  order_copy_prefix_145 i input output ->
  i < Zlength input ->
  order_copy_prefix_145 (i + 1) input (output ++ [Znth i input 0]).
Proof.
  intros i input output Hprefix Hlt.
  unfold order_copy_prefix_145 in *.
  destruct Hprefix as [[Hlo Hhi] [Hlen Hout]].
  subst output.
  repeat split.
  - lia.
  - lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlen; lia.
  - rewrite sublist_snoc_Znth_145 by lia; reflexivity.
Qed.

Lemma order_score_prefix_145_nil : forall input,
  order_score_prefix_145 0 input [].
Proof.
  intros.
  unfold order_score_prefix_145, score_prefix_rel_145, sublist.
  cbn.
  repeat split.
  - lia.
  - rewrite Zlength_correct; lia.
  - intros k Hk; cbn in Hk; lia.
Qed.

Lemma order_score_prefix_145_step : forall i input scores score,
  order_score_prefix_145 i input scores ->
  i < Zlength input ->
  signed_digit_score_result_145 (Znth i input 0) score ->
  order_score_prefix_145 (i + 1) input (scores ++ [score]).
Proof.
  intros i input scores score Hprefix Hlt Hscore.
  unfold order_score_prefix_145 in *.
  destruct Hprefix as [[Hlo Hhi] [Hlen Hrel]].
  repeat split.
  - lia.
  - lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlen; lia.
  - unfold score_prefix_rel_145 in *.
    destruct Hrel as [Hrel_len Hrel_at].
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_sublist by lia.
    lia.
  - unfold score_prefix_rel_145 in *.
    destruct Hrel as [Hrel_len Hrel_at].
    intros k Hk.
    rewrite sublist_snoc_Znth_145 in Hk by lia.
    rewrite sublist_snoc_Znth_145 by lia.
    destruct (Z_lt_dec k i).
    + rewrite app_Znth1 by lia.
      rewrite app_Znth1 by lia.
      replace (Znth k input 0) with (Znth k (sublist 0 i input) 0)
        by (rewrite Znth_sublist0 by lia; reflexivity).
      apply Hrel_at.
      rewrite Zlength_sublist in * by lia.
      lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk.
      rewrite Zlength_sublist in Hk by lia.
      assert (k = i) by lia; subst k.
      rewrite app_Znth2 by lia.
      replace (i - i) with 0 by lia.
      cbn.
      rewrite app_Znth2.
      * replace (i - i) with 0 by lia.
        assert (Hfirstn_len : Zlength (firstn (Z.to_nat i) input) = i).
        { rewrite Zlength_correct, firstn_length.
          rewrite Nat.min_l.
          - rewrite Z2Nat.id by lia; reflexivity.
          - apply Nat2Z.inj_le.
            rewrite Z2Nat.id by lia.
            rewrite <- Zlength_correct; lia. }
        rewrite Hfirstn_len.
        rewrite Hlen.
        replace (i - i) with 0 by lia.
        cbn.
        exact Hscore.
      * lia.
Qed.

Lemma Zlength_map_145 : forall {A B : Type} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros.
  repeat rewrite Zlength_correct.
  rewrite map_length.
  reflexivity.
Qed.

Lemma Znth_map_145 : forall {A B : Type} (f : A -> B) (l : list A) i d d',
  0 <= i < Zlength l ->
  Znth i (map f l) d' = f (Znth i l d).
Proof.
  intros A B f l i d d' Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f d)).
  - apply nth_indep.
    rewrite map_length.
    rewrite Zlength_correct in Hi.
    lia.
  - rewrite (@map_nth A B f l d (Z.to_nat i)).
    reflexivity.
Qed.

Lemma replace_Znth_length_145 : forall {A : Type} (l : list A) i x,
  Zlength (replace_Znth i x l) = Zlength l.
Proof.
  intros A l i x.
  unfold replace_Znth.
  repeat rewrite Zlength_correct.
  f_equal.
  revert l.
  generalize (Z.to_nat i) as n.
  induction n; intros [|a l0]; simpl; try reflexivity.
  rewrite IHn.
  reflexivity.
Qed.

Lemma map_replace_Znth_145 : forall {A B : Type} (f : A -> B) l i x,
  map f (replace_Znth i x l) =
  replace_Znth i (f x) (map f l).
Proof.
  intros A B f l i x.
  assert (Hrep: forall n (l0 : list A),
    map f (@replace_nth A n l0 x) = @replace_nth B n (map f l0) (f x)).
  {
    induction n; intros [|a l0]; simpl; try reflexivity.
    rewrite IHn; reflexivity.
  }
  unfold replace_Znth.
  apply Hrep.
Qed.

Lemma score_pairs_values_145 : forall output scores,
  Zlength output = Zlength scores ->
  pair_values_145 (score_pairs_145 output scores) = output.
Proof.
  induction output as [|x xs IH]; intros scores Hlen.
  - destruct scores; [reflexivity|].
    repeat rewrite Zlength_correct in Hlen.
    simpl in Hlen; lia.
  - destruct scores as [|s ss].
    + repeat rewrite Zlength_correct in Hlen.
      simpl in Hlen; lia.
    + cbn.
      f_equal.
      apply IH.
      repeat rewrite Zlength_cons in Hlen.
      lia.
Qed.

Lemma score_pairs_scores_145 : forall output scores,
  Zlength output = Zlength scores ->
  pair_scores_145 (score_pairs_145 output scores) = scores.
Proof.
  induction output as [|x xs IH]; intros scores Hlen.
  - destruct scores; [reflexivity|].
    repeat rewrite Zlength_correct in Hlen.
    simpl in Hlen; lia.
  - destruct scores as [|s ss].
    + repeat rewrite Zlength_correct in Hlen.
      simpl in Hlen; lia.
    + cbn.
      f_equal.
      apply IH.
      repeat rewrite Zlength_cons in Hlen.
      lia.
Qed.

Lemma score_pairs_Zlength_145 : forall output scores,
  Zlength output = Zlength scores ->
  Zlength (score_pairs_145 output scores) = Zlength output.
Proof.
  intros output scores Hlen.
  unfold score_pairs_145.
  repeat rewrite Zlength_correct in *.
  rewrite combine_length.
  lia.
Qed.

Lemma nth_error_Znth_145 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  nth_error l (Z.to_nat i) = Some (Znth i l d).
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply (@nth_error_nth' A).
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma replace_nth_adjacent_145 : forall {A : Type} n (l : list A) d,
  (S n < length l)%nat ->
  firstn n l ++ nth (S n) l d :: nth n l d :: skipn (S (S n)) l =
  replace_nth n
    (replace_nth (S n) l (nth n l d))
    (nth (S n) l d).
Proof.
  intros A n.
  induction n; intros [|x xs] d Hlen; simpl in *; try lia.
  - destruct xs as [|y ys]; simpl in *; try lia.
    reflexivity.
  - f_equal.
    apply IHn.
    lia.
Qed.

Lemma replace_Znth_adjacent_145 : forall {A : Type} (l : list A) j d,
  0 <= j ->
  j + 1 < Zlength l ->
  firstn (Z.to_nat j) l ++
    Znth (j + 1) l d :: Znth j l d :: skipn (S (S (Z.to_nat j))) l =
  replace_Znth j (Znth (j + 1) l d)
    (replace_Znth (j + 1) (Znth j l d) l).
Proof.
  intros A l j d Hj Hjlen.
  unfold replace_Znth, Znth.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  apply replace_nth_adjacent_145.
  rewrite Zlength_correct in Hjlen.
  lia.
Qed.

Lemma stable_digit_sum_order_nil_145 :
  stable_digit_sum_order [] [].
Proof.
  unfold stable_digit_sum_order.
  exists [], [].
  repeat split; cbn; try reflexivity.
  - intros i x s Hx _.
    destruct i; inversion Hx.
  - intros i x s Hx _.
    destruct i; inversion Hx.
Qed.

Lemma swap_adjacent_pair_145_length : forall j pairs,
  length (swap_adjacent_pair_145 j pairs) = length pairs.
Proof.
  intros j pairs.
  unfold swap_adjacent_pair_145.
  destruct (nth_error pairs j) as [p1|] eqn:Hp1;
    destruct (nth_error pairs (S j)) as [p2|] eqn:Hp2; try reflexivity.
  destruct (should_swap_pair_145 p1 p2); try reflexivity.
  assert (Hlen: (S j < length pairs)%nat).
  {
    apply (proj1 (nth_error_Some pairs (S j))).
    rewrite Hp2; discriminate.
  }
  rewrite length_app.
  cbn [length].
  rewrite length_firstn, length_skipn.
  rewrite Nat.min_l by lia.
  lia.
Qed.

Lemma bubble_pass_pairs_from_145_length : forall fuel j pairs,
  length (bubble_pass_pairs_from_145 fuel j pairs) = length pairs.
Proof.
  induction fuel; intros j pairs; simpl.
  - reflexivity.
  - rewrite IHfuel.
    apply swap_adjacent_pair_145_length.
Qed.

Lemma bubble_pass_pairs_145_length : forall pairs,
  length (bubble_pass_pairs_145 pairs) = length pairs.
Proof.
  intros pairs.
  unfold bubble_pass_pairs_145.
  apply bubble_pass_pairs_from_145_length.
Qed.

Lemma bubble_sort_pairs_fuel_145_length : forall fuel pairs,
  length (bubble_sort_pairs_fuel_145 fuel pairs) = length pairs.
Proof.
  induction fuel; intros pairs; simpl.
  - reflexivity.
  - rewrite IHfuel.
    apply bubble_pass_pairs_145_length.
Qed.

Lemma bubble_pass_pairs_from_145_compose : forall n m start pairs,
  bubble_pass_pairs_from_145 (n + m) start pairs =
  bubble_pass_pairs_from_145 m (start + n)%nat
    (bubble_pass_pairs_from_145 n start pairs).
Proof.
  induction n; intros m start pairs; simpl.
  - replace (start + 0)%nat with start by lia.
    reflexivity.
  - rewrite IHn.
    replace (start + S n)%nat with (S (start + n))%nat by lia.
    reflexivity.
Qed.

Lemma bubble_pass_pairs_from_145_next : forall n start pairs,
  bubble_pass_pairs_from_145 (S n) start pairs =
  swap_adjacent_pair_145 (start + n)%nat
    (bubble_pass_pairs_from_145 n start pairs).
Proof.
  intros n start pairs.
  replace (S n) with (n + 1)%nat by lia.
  rewrite bubble_pass_pairs_from_145_compose.
  simpl.
  reflexivity.
Qed.

Lemma bubble_sort_pairs_fuel_145_snoc : forall n pairs,
  bubble_sort_pairs_fuel_145 (S n) pairs =
  bubble_pass_pairs_145 (bubble_sort_pairs_fuel_145 n pairs).
Proof.
  induction n; intros pairs.
  - reflexivity.
  - change (bubble_sort_pairs_fuel_145 (S n) (bubble_pass_pairs_145 pairs) =
      bubble_pass_pairs_145 (bubble_sort_pairs_fuel_145 (S n) pairs)).
    rewrite (IHn (bubble_pass_pairs_145 pairs)).
    reflexivity.
Qed.

Lemma should_swap_pair_145_true : forall p1 p2,
  snd p1 > snd p2 ->
  should_swap_pair_145 p1 p2 = true.
Proof.
  intros p1 p2 Hgt.
  unfold should_swap_pair_145.
  destruct (Z.gtb_spec (snd p1) (snd p2)); [reflexivity|lia].
Qed.

Lemma should_swap_pair_145_false : forall p1 p2,
  snd p1 <= snd p2 ->
  should_swap_pair_145 p1 p2 = false.
Proof.
  intros p1 p2 Hle.
  unfold should_swap_pair_145.
  destruct (Z.gtb_spec (snd p1) (snd p2)); [lia|reflexivity].
Qed.

Lemma swap_adjacent_pair_145_swap : forall pairs j,
  0 <= j ->
  j + 1 < Zlength pairs ->
  snd (Znth j pairs (0, 0)) > snd (Znth (j + 1) pairs (0, 0)) ->
  swap_adjacent_pair_145 (Z.to_nat j) pairs =
    replace_Znth j (Znth (j + 1) pairs (0, 0))
      (replace_Znth (j + 1) (Znth j pairs (0, 0)) pairs).
Proof.
  intros pairs j Hj Hjlen Hgt.
  unfold swap_adjacent_pair_145.
  rewrite (nth_error_Znth_145 pairs j (0, 0)) by lia.
  replace (S (Z.to_nat j)) with (Z.to_nat (j + 1)) by lia.
  rewrite (nth_error_Znth_145 pairs (j + 1) (0, 0)) by lia.
  rewrite should_swap_pair_145_true by exact Hgt.
  replace (S (Z.to_nat (j + 1))) with (S (S (Z.to_nat j))) by lia.
  apply replace_Znth_adjacent_145; lia.
Qed.

Lemma swap_adjacent_pair_145_keep : forall pairs j,
  0 <= j ->
  j + 1 < Zlength pairs ->
  snd (Znth j pairs (0, 0)) <= snd (Znth (j + 1) pairs (0, 0)) ->
  swap_adjacent_pair_145 (Z.to_nat j) pairs = pairs.
Proof.
  intros pairs j Hj Hjlen Hle.
  unfold swap_adjacent_pair_145.
  rewrite (nth_error_Znth_145 pairs j (0, 0)) by lia.
  replace (S (Z.to_nat j)) with (Z.to_nat (j + 1)) by lia.
  rewrite (nth_error_Znth_145 pairs (j + 1) (0, 0)) by lia.
  rewrite should_swap_pair_145_false by exact Hle.
  reflexivity.
Qed.

Definition score_eqb_145 (s : Z) (p : Z * Z) : bool :=
  Z.eqb (snd p) s.

Lemma list_adjacent_split_145 : forall {A : Type} (l : list A) j x y,
  nth_error l j = Some x ->
  nth_error l (S j) = Some y ->
  l = firstn j l ++ x :: y :: skipn (S (S j)) l.
Proof.
  intros A l.
  induction l as [|a l IH]; intros [|j] x y Hj HSj; cbn in *; try discriminate.
  - destruct l as [|b l]; cbn in HSj; try discriminate.
    inversion Hj; inversion HSj; subst; reflexivity.
  - f_equal.
    apply IH; assumption.
Qed.

Lemma swap_adjacent_pair_145_perm : forall j pairs,
  Permutation pairs (swap_adjacent_pair_145 j pairs).
Proof.
  intros j pairs.
  unfold swap_adjacent_pair_145.
  destruct (nth_error pairs j) as [p1|] eqn:Hp1;
    destruct (nth_error pairs (S j)) as [p2|] eqn:Hp2; try reflexivity.
  destruct (should_swap_pair_145 p1 p2) eqn:Hsw; try reflexivity.
  assert (Hsplit :
    pairs = firstn j pairs ++ p1 :: p2 :: skipn (S (S j)) pairs).
  { apply list_adjacent_split_145; assumption. }
  rewrite Hsplit at 1.
  apply Permutation_app_head.
  apply perm_swap.
Qed.

Lemma bubble_pass_pairs_from_145_perm : forall fuel j pairs,
  Permutation pairs (bubble_pass_pairs_from_145 fuel j pairs).
Proof.
  induction fuel as [|fuel IH]; intros j pairs; cbn.
  - reflexivity.
  - eapply Permutation_trans.
    + apply swap_adjacent_pair_145_perm.
    + apply IH.
Qed.

Lemma bubble_pass_pairs_145_perm : forall pairs,
  Permutation pairs (bubble_pass_pairs_145 pairs).
Proof.
  intros pairs.
  unfold bubble_pass_pairs_145.
  apply bubble_pass_pairs_from_145_perm.
Qed.

Lemma bubble_sort_pairs_fuel_145_perm : forall fuel pairs,
  Permutation pairs (bubble_sort_pairs_fuel_145 fuel pairs).
Proof.
  induction fuel as [|fuel IH]; intros pairs; cbn.
  - reflexivity.
  - eapply Permutation_trans.
    + apply bubble_pass_pairs_145_perm.
    + apply IH.
Qed.

Lemma filter_score_swap_adjacent_pair_145 : forall s j pairs,
  filter (score_eqb_145 s) (swap_adjacent_pair_145 j pairs) =
  filter (score_eqb_145 s) pairs.
Proof.
  intros s j pairs.
  unfold swap_adjacent_pair_145.
  destruct (nth_error pairs j) as [p1|] eqn:Hp1;
    destruct (nth_error pairs (S j)) as [p2|] eqn:Hp2; try reflexivity.
  destruct (should_swap_pair_145 p1 p2) eqn:Hsw; try reflexivity.
  unfold should_swap_pair_145 in Hsw.
  destruct (snd p1 >? snd p2) eqn:Hgt; try discriminate.
  apply Z.gtb_lt in Hgt.
  assert (Hneq : snd p1 <> snd p2) by lia.
  assert (Hsplit :
    pairs = firstn j pairs ++ p1 :: p2 :: skipn (S (S j)) pairs).
  { apply list_adjacent_split_145; assumption. }
  replace (filter (score_eqb_145 s) pairs) with
    (filter (score_eqb_145 s)
       (firstn j pairs ++ p1 :: p2 :: skipn (S (S j)) pairs))
    by (rewrite <- Hsplit; reflexivity).
  repeat rewrite filter_app.
  cbn.
  unfold score_eqb_145.
  destruct (Z.eqb_spec (snd p1) s);
    destruct (Z.eqb_spec (snd p2) s); subst; try lia; reflexivity.
Qed.

Lemma filter_score_bubble_pass_pairs_from_145 : forall s fuel j pairs,
  filter (score_eqb_145 s) (bubble_pass_pairs_from_145 fuel j pairs) =
  filter (score_eqb_145 s) pairs.
Proof.
  induction fuel as [|fuel IH]; intros j pairs; cbn.
  - reflexivity.
  - rewrite IH.
    apply filter_score_swap_adjacent_pair_145.
Qed.

Lemma filter_score_bubble_pass_pairs_145 : forall s pairs,
  filter (score_eqb_145 s) (bubble_pass_pairs_145 pairs) =
  filter (score_eqb_145 s) pairs.
Proof.
  intros s pairs.
  unfold bubble_pass_pairs_145.
  apply filter_score_bubble_pass_pairs_from_145.
Qed.

Lemma filter_score_bubble_sort_pairs_fuel_145 : forall s fuel pairs,
  filter (score_eqb_145 s) (bubble_sort_pairs_fuel_145 fuel pairs) =
  filter (score_eqb_145 s) pairs.
Proof.
  induction fuel as [|fuel IH]; intros pairs; cbn.
  - reflexivity.
  - rewrite IH.
    apply filter_score_bubble_pass_pairs_145.
Qed.

Definition pair_score_le_145 (p q : Z * Z) : Prop :=
  snd p <= snd q.

Lemma pair_score_le_refl_145 : forall p, pair_score_le_145 p p.
Proof. unfold pair_score_le_145; lia. Qed.

Lemma pair_score_le_trans_145 : forall p q r,
  pair_score_le_145 p q ->
  pair_score_le_145 q r ->
  pair_score_le_145 p r.
Proof. unfold pair_score_le_145; lia. Qed.

Lemma should_swap_pair_145_true_le : forall p q,
  should_swap_pair_145 p q = true ->
  pair_score_le_145 q p.
Proof.
  intros p q H.
  unfold should_swap_pair_145 in H.
  destruct (snd p >? snd q) eqn:Hgt; try discriminate.
  apply Z.gtb_lt in Hgt.
  unfold pair_score_le_145; lia.
Qed.

Lemma should_swap_pair_145_false_le : forall p q,
  should_swap_pair_145 p q = false ->
  pair_score_le_145 p q.
Proof.
  intros p q H.
  unfold should_swap_pair_145 in H.
  destruct (Z.gtb_spec (snd p) (snd q)); try discriminate.
  unfold pair_score_le_145; lia.
Qed.

Lemma pair_score_le_should_swap_pair_145_false : forall p q,
  pair_score_le_145 p q ->
  should_swap_pair_145 p q = false.
Proof.
  intros p q Hle.
  unfold pair_score_le_145 in Hle.
  unfold should_swap_pair_145.
  destruct (Z.gtb_spec (snd p) (snd q)); try reflexivity; lia.
Qed.

Lemma swap_adjacent_pair_145_cons : forall j x l,
  swap_adjacent_pair_145 (S j) (x :: l) =
  x :: swap_adjacent_pair_145 j l.
Proof.
  intros j x l.
  destruct l as [|y ys].
  - unfold swap_adjacent_pair_145; cbn.
    rewrite nth_error_nil.
    reflexivity.
  - unfold swap_adjacent_pair_145; cbn.
    destruct (nth_error (y :: ys) j);
      destruct (nth_error ys j);
      try destruct (should_swap_pair_145 p p0);
      reflexivity.
Qed.

Lemma bubble_pass_pairs_from_145_cons : forall fuel j x l,
  bubble_pass_pairs_from_145 fuel (S j) (x :: l) =
  x :: bubble_pass_pairs_from_145 fuel j l.
Proof.
  induction fuel as [|fuel IH]; intros j x l; cbn.
  - reflexivity.
  - rewrite swap_adjacent_pair_145_cons.
    rewrite IH.
    reflexivity.
Qed.

Lemma bubble_pass_pairs_from_145_cons0 : forall fuel x l,
  bubble_pass_pairs_from_145 fuel 1 (x :: l) =
  x :: bubble_pass_pairs_from_145 fuel 0 l.
Proof.
  intros fuel x l.
  change 1%nat with (S 0%nat).
  apply bubble_pass_pairs_from_145_cons.
Qed.

Lemma bubble_pass_pairs_from_145_step : forall fuel j l,
  bubble_pass_pairs_from_145 (S fuel) j l =
  bubble_pass_pairs_from_145 fuel (S j) (swap_adjacent_pair_145 j l).
Proof. reflexivity. Qed.

Lemma swap_adjacent_pair_145_zero_true : forall x y ys,
  should_swap_pair_145 x y = true ->
  swap_adjacent_pair_145 0 (x :: y :: ys) = y :: x :: ys.
Proof.
  intros x y ys Hsw.
  unfold swap_adjacent_pair_145; cbn.
  rewrite Hsw.
  reflexivity.
Qed.

Lemma swap_adjacent_pair_145_zero_false : forall x y ys,
  should_swap_pair_145 x y = false ->
  swap_adjacent_pair_145 0 (x :: y :: ys) = x :: y :: ys.
Proof.
  intros x y ys Hsw.
  unfold swap_adjacent_pair_145; cbn.
  rewrite Hsw.
  reflexivity.
Qed.

Fixpoint bubble_pass_pairs_prefix_145 (x : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with
  | [] => []
  | y :: ys =>
      if should_swap_pair_145 x y
      then y :: bubble_pass_pairs_prefix_145 x ys
      else x :: bubble_pass_pairs_prefix_145 y ys
  end.

Fixpoint bubble_pass_pairs_max_145 (x : Z * Z) (l : list (Z * Z)) : Z * Z :=
  match l with
  | [] => x
  | y :: ys =>
      if should_swap_pair_145 x y
      then bubble_pass_pairs_max_145 x ys
      else bubble_pass_pairs_max_145 y ys
  end.

Lemma bubble_pass_pairs_145_cons_true : forall x y ys,
  should_swap_pair_145 x y = true ->
  bubble_pass_pairs_145 (x :: y :: ys) =
  y :: bubble_pass_pairs_145 (x :: ys).
Proof.
  intros x y ys Hsw.
  unfold bubble_pass_pairs_145.
  change (length (x :: y :: ys) - 1)%nat with (S (length ys)).
  rewrite bubble_pass_pairs_from_145_step.
  rewrite (swap_adjacent_pair_145_zero_true x y ys Hsw).
  rewrite bubble_pass_pairs_from_145_cons0.
  replace (length (x :: ys) - 1)%nat with (length ys) by (cbn; lia).
  reflexivity.
Qed.

Lemma bubble_pass_pairs_145_cons_false : forall x y ys,
  should_swap_pair_145 x y = false ->
  bubble_pass_pairs_145 (x :: y :: ys) =
  x :: bubble_pass_pairs_145 (y :: ys).
Proof.
  intros x y ys Hsw.
  unfold bubble_pass_pairs_145.
  change (length (x :: y :: ys) - 1)%nat with (S (length ys)).
  rewrite bubble_pass_pairs_from_145_step.
  rewrite (swap_adjacent_pair_145_zero_false x y ys Hsw).
  rewrite bubble_pass_pairs_from_145_cons0.
  replace (length (y :: ys) - 1)%nat with (length ys) by (cbn; lia).
  reflexivity.
Qed.

Lemma bubble_pass_pairs_prefix_eq_145 : forall x l,
  bubble_pass_pairs_145 (x :: l) =
  bubble_pass_pairs_prefix_145 x l ++
  [bubble_pass_pairs_max_145 x l].
Proof.
  intros x l.
  revert x.
  induction l as [|y ys IH]; intros x.
  - reflexivity.
  - destruct (should_swap_pair_145 x y) eqn:Hsw.
    + rewrite bubble_pass_pairs_145_cons_true by exact Hsw.
      cbn [bubble_pass_pairs_prefix_145 bubble_pass_pairs_max_145].
      rewrite Hsw.
      rewrite IH.
      reflexivity.
    + rewrite bubble_pass_pairs_145_cons_false by exact Hsw.
      cbn [bubble_pass_pairs_prefix_145 bubble_pass_pairs_max_145].
      rewrite Hsw.
      rewrite IH.
      reflexivity.
Qed.

Local Transparent bubble_pass_pairs_from_145.

Lemma bubble_pass_pairs_max_forall_145 : forall x l,
  Forall (fun y => pair_score_le_145 y (bubble_pass_pairs_max_145 x l)) (x :: l).
Proof.
  intros x l.
  revert x.
  induction l as [|y ys IH]; intros x.
  - constructor; [apply pair_score_le_refl_145 | constructor].
  - cbn [bubble_pass_pairs_max_145].
    destruct (should_swap_pair_145 x y) eqn:Hsw.
    + specialize (IH x).
      inversion_clear IH as [|? ? Hxm Htail].
      constructor.
      * exact Hxm.
      * constructor.
        -- eapply pair_score_le_trans_145.
           ++ apply should_swap_pair_145_true_le. exact Hsw.
           ++ exact Hxm.
        -- exact Htail.
    + specialize (IH y).
      inversion_clear IH as [|? ? Hym Htail].
      constructor.
      * eapply pair_score_le_trans_145.
        -- apply should_swap_pair_145_false_le. exact Hsw.
        -- exact Hym.
      * constructor; [exact Hym | exact Htail].
Qed.

Lemma Forall_permutation_145 : forall {A : Type} (P : A -> Prop) l1 l2,
  Permutation l1 l2 ->
  Forall P l1 ->
  Forall P l2.
Proof.
  intros A P l1 l2 Hperm Hall.
  eapply Permutation_Forall; eauto.
Qed.

Lemma bubble_pass_pairs_145_app_last : forall p m,
  Forall (fun y => pair_score_le_145 y m) p ->
  bubble_pass_pairs_145 (p ++ [m]) =
  bubble_pass_pairs_145 p ++ [m].
Proof.
  intros p m Hall.
  destruct p as [|x xs].
  - reflexivity.
  - simpl in Hall.
    revert x Hall.
    induction xs as [|y ys IH]; intros x Hall.
    + simpl in Hall.
      inversion Hall as [|? ? Hxm _]; subst.
      change (bubble_pass_pairs_145 (x :: m :: []) =
        bubble_pass_pairs_145 (x :: []) ++ [m]).
      rewrite bubble_pass_pairs_145_cons_false
        by (apply pair_score_le_should_swap_pair_145_false; exact Hxm).
      reflexivity.
    + simpl in Hall.
      inversion Hall as [|? ? Hxm Hall_tail]; subst.
      inversion Hall_tail as [|? ? Hym Hys]; subst.
      change (bubble_pass_pairs_145 (x :: y :: (ys ++ [m])) =
        bubble_pass_pairs_145 (x :: y :: ys) ++ [m]).
      destruct (should_swap_pair_145 x y) eqn:Hsw.
      * rewrite bubble_pass_pairs_145_cons_true by exact Hsw.
        rewrite bubble_pass_pairs_145_cons_true by exact Hsw.
        change (bubble_pass_pairs_145 (x :: ys ++ [m])) with
          (bubble_pass_pairs_145 ((x :: ys) ++ [m])).
        rewrite IH.
        -- reflexivity.
        -- constructor; assumption.
      * rewrite bubble_pass_pairs_145_cons_false by exact Hsw.
        rewrite bubble_pass_pairs_145_cons_false by exact Hsw.
        change (bubble_pass_pairs_145 (y :: ys ++ [m])) with
          (bubble_pass_pairs_145 ((y :: ys) ++ [m])).
        rewrite IH.
        -- reflexivity.
        -- exact Hall_tail.
Qed.

Lemma bubble_sort_pairs_fuel_145_app_last : forall fuel p m,
  Forall (fun y => pair_score_le_145 y m) p ->
  bubble_sort_pairs_fuel_145 fuel (p ++ [m]) =
  bubble_sort_pairs_fuel_145 fuel p ++ [m].
Proof.
  induction fuel as [|fuel IH]; intros p m Hall; cbn.
  - reflexivity.
  - rewrite bubble_pass_pairs_145_app_last by exact Hall.
    rewrite IH.
    + reflexivity.
    + eapply Forall_permutation_145.
      * apply bubble_pass_pairs_145_perm.
      * exact Hall.
Qed.

Lemma HdRel_snoc_145 : forall a l m,
  HdRel pair_score_le_145 a l ->
  pair_score_le_145 a m ->
  HdRel pair_score_le_145 a (l ++ [m]).
Proof.
  intros a l m Hhd Ham.
  induction l as [|x xs IH].
  - cbn. constructor. exact Ham.
  - cbn.
    inversion Hhd; subst.
    constructor. assumption.
Qed.

Lemma Sorted_snoc_145 : forall l m,
  Sorted pair_score_le_145 l ->
  Forall (fun x => pair_score_le_145 x m) l ->
  Sorted pair_score_le_145 (l ++ [m]).
Proof.
  induction l as [|x xs IH]; intros m Hsorted Hall.
  - cbn. constructor; [constructor | constructor].
  - cbn.
    inversion Hsorted as [|? ? Hsorted_tail Hhd]; subst.
    inversion Hall as [|? ? Hxm Hall_tail]; subst.
    constructor.
    + apply IH; assumption.
    + apply HdRel_snoc_145; assumption.
Qed.

Local Opaque bubble_pass_pairs_145.

Lemma bubble_sort_pairs_fuel_145_sorted_length : forall n pairs,
  length pairs = n ->
  Sorted pair_score_le_145 (bubble_sort_pairs_fuel_145 n pairs).
Proof.
  induction n as [|n IH]; intros pairs Hlen.
  - destruct pairs; cbn in Hlen; try lia.
    cbn. constructor.
  - destruct pairs as [|x xs].
    + cbn in Hlen; lia.
    + cbn.
      set (p := bubble_pass_pairs_prefix_145 x xs).
      set (m := bubble_pass_pairs_max_145 x xs).
      pose proof (bubble_pass_pairs_prefix_eq_145 x xs) as Hpass.
      fold p in Hpass.
      fold m in Hpass.
      pose proof (bubble_pass_pairs_max_forall_145 x xs) as Hall.
      fold m in Hall.
      pose proof (bubble_pass_pairs_145_perm (x :: xs)) as Hperm.
      rewrite Hpass in Hperm.
      rewrite Hpass.
      assert (Hp_forall : Forall (fun y => pair_score_le_145 y m) p).
      {
        pose proof (Forall_permutation_145
          (fun y => pair_score_le_145 y m) (x :: xs) (p ++ [m]) Hperm Hall) as Hall_pm.
        apply Forall_app in Hall_pm.
        tauto.
      }
      rewrite bubble_sort_pairs_fuel_145_app_last by exact Hp_forall.
      apply Sorted_snoc_145.
      * apply IH.
        apply Permutation_length in Hperm.
        rewrite app_length in Hperm.
        cbn in Hperm.
        cbn in Hlen.
        lia.
      * eapply Forall_permutation_145.
        -- apply bubble_sort_pairs_fuel_145_perm.
        -- exact Hp_forall.
Qed.

Local Transparent bubble_pass_pairs_145.

Lemma bubble_sort_pairs_fuel_145_sorted : forall pairs,
  Sorted pair_score_le_145
    (bubble_sort_pairs_fuel_145 (length pairs) pairs).
Proof.
  intros pairs.
  apply bubble_sort_pairs_fuel_145_sorted_length.
  reflexivity.
Qed.

Definition pair_score_ok_145 (p : Z * Z) : Prop :=
  signed_digit_sum (fst p) (snd p).

Lemma score_prefix_rel_pairs_Forall_145 : forall input scores,
  score_prefix_rel_145 input scores ->
  Forall pair_score_ok_145 (score_pairs_145 input scores).
Proof.
  intros input scores Hrel.
  unfold score_prefix_rel_145 in Hrel.
  destruct Hrel as [Hlen Hscore].
  unfold score_pairs_145.
  revert scores Hlen Hscore.
  induction input as [|x xs IH]; intros scores Hlen Hscore.
  - destruct scores.
    + constructor.
    + repeat rewrite Zlength_correct in Hlen; cbn in Hlen; lia.
  - destruct scores as [|s ss].
    + repeat rewrite Zlength_correct in Hlen; cbn in Hlen; lia.
    + cbn.
      constructor.
      * unfold pair_score_ok_145; cbn.
        specialize (Hscore 0).
        rewrite !Znth0_cons in Hscore.
        apply Hscore.
        rewrite Zlength_cons.
        pose proof (Zlength_nonneg xs); lia.
      * apply IH.
        -- repeat rewrite Zlength_cons in Hlen; lia.
        -- intros i Hi.
           specialize (Hscore (i + 1)).
           rewrite !Znth_cons in Hscore by lia.
           replace (i + 1 - 1) with i in Hscore by lia.
           apply Hscore.
           rewrite Zlength_cons.
           lia.
Qed.

Lemma bubble_sort_pairs_values_perm_145 : forall input scores fuel,
  Zlength scores = Zlength input ->
  Permutation
    (pair_values_145 (bubble_sort_pairs_fuel_145 fuel (score_pairs_145 input scores)))
    input.
Proof.
  intros input scores fuel Hlen.
  unfold pair_values_145.
  transitivity (map fst (score_pairs_145 input scores)).
  - symmetry.
    apply Permutation_map.
    apply bubble_sort_pairs_fuel_145_perm.
  - rewrite score_pairs_values_145 by lia.
    reflexivity.
Qed.

Lemma pair_score_sorted_values_145 : forall pairs,
  Sorted pair_score_le_145 pairs ->
  Forall pair_score_ok_145 pairs ->
  Sorted le_digit_sum (pair_values_145 pairs).
Proof.
  induction pairs as [|p ps IH]; intros Hsorted Hall.
  - constructor.
  - cbn [pair_values_145 map].
    inversion Hsorted as [|? ? Hsorted_tail Hhd]; subst.
    inversion Hall as [|? ? Hok Hall_tail]; subst.
    constructor.
    + apply IH; assumption.
    + destruct ps as [|q qs].
      * constructor.
      * inversion Hhd as [|? ? Hle]; subst.
        inversion Hall_tail as [|? ? Hokq _]; subst.
        constructor.
        unfold le_digit_sum.
        exists (snd p), (snd q).
        repeat split; try assumption.
Qed.

Lemma bubble_sort_pairs_values_sorted_145 : forall input scores fuel,
  score_prefix_rel_145 input scores ->
  fuel = length (score_pairs_145 input scores) ->
  Sorted le_digit_sum
    (pair_values_145 (bubble_sort_pairs_fuel_145 fuel (score_pairs_145 input scores))).
Proof.
  intros input scores fuel Hrel Hfuel.
  subst fuel.
  apply pair_score_sorted_values_145.
  - apply bubble_sort_pairs_fuel_145_sorted.
  - eapply Forall_permutation_145.
    + apply bubble_sort_pairs_fuel_145_perm.
    + apply score_prefix_rel_pairs_Forall_145.
      exact Hrel.
Qed.

Lemma final_output_perm_sorted_145 : forall input scores output,
  score_prefix_rel_145 input scores ->
  output =
    pair_values_145
      (bubble_sort_pairs_fuel_145 (Z.to_nat (Zlength input))
        (score_pairs_145 input scores)) ->
  Permutation output input /\ Sorted le_digit_sum output.
Proof.
  intros input scores output Hrel Hout.
  unfold score_prefix_rel_145 in Hrel.
  destruct Hrel as [Hlen Hscore].
  split.
  - subst output.
    apply bubble_sort_pairs_values_perm_145.
    exact Hlen.
  - subst output.
    apply bubble_sort_pairs_values_sorted_145.
    + unfold score_prefix_rel_145.
      split; assumption.
    + apply Nat2Z.inj.
      rewrite Z2Nat.id by apply Zlength_nonneg.
      rewrite <- Zlength_correct.
      rewrite score_pairs_Zlength_145 by lia.
      reflexivity.
Qed.

Lemma combine_pair_values_scores_145 : forall pairs,
  combine (pair_values_145 pairs) (pair_scores_145 pairs) = pairs.
Proof.
  induction pairs as [|[x s] ps IH]; cbn; f_equal; exact IH.
Qed.

Lemma scored_by_digit_sum_of_score_prefix_rel_145 : forall values scores,
  score_prefix_rel_145 values scores ->
  scored_by_digit_sum values scores.
Proof.
  intros values scores Hrel.
  unfold score_prefix_rel_145 in Hrel.
  destruct Hrel as [Hlen Hscore].
  unfold scored_by_digit_sum.
  split.
  - repeat rewrite Zlength_correct in Hlen.
    symmetry.
    apply Nat2Z.inj.
    exact Hlen.
  - intros i x s Hx Hs.
    assert (Hi : 0 <= Z.of_nat i < Zlength values).
    {
      pose proof (proj1 (nth_error_Some values i)) as Hsome.
      specialize (Hsome ltac:(rewrite Hx; discriminate)).
      rewrite Zlength_correct.
      lia.
    }
    specialize (Hscore (Z.of_nat i) Hi).
    pose proof (nth_error_Znth_145 values (Z.of_nat i) 0 Hi) as Hx_z.
    rewrite Nat2Z.id in Hx_z.
    pose proof (nth_error_Znth_145 scores (Z.of_nat i) 0
      ltac:(rewrite Hlen; exact Hi)) as Hs_z.
    rewrite Nat2Z.id in Hs_z.
    rewrite Hx in Hx_z.
    rewrite Hs in Hs_z.
    inversion Hx_z; inversion Hs_z; subst.
      exact Hscore.
Qed.

Lemma score_prefix_rel_pair_values_scores_145 : forall pairs,
  Forall pair_score_ok_145 pairs ->
  score_prefix_rel_145 (pair_values_145 pairs) (pair_scores_145 pairs).
Proof.
  intros pairs Hall.
  unfold score_prefix_rel_145.
  split.
  - unfold pair_scores_145, pair_values_145.
    repeat rewrite Zlength_map_145.
    reflexivity.
  - intros i Hi.
    assert (Hpair_i : 0 <= i < Zlength pairs).
    {
      unfold pair_values_145 in Hi.
      rewrite Zlength_map_145 in Hi.
      exact Hi.
    }
    assert (Hin : In (Znth i pairs (0, 0)) pairs).
    {
      eapply nth_error_In.
      rewrite <- (nth_error_Znth_145 pairs i (0, 0)) by exact Hpair_i.
      reflexivity.
    }
    apply Forall_forall with (x := Znth i pairs (0, 0)) in Hall; [|exact Hin].
    unfold pair_score_ok_145 in Hall.
    unfold pair_values_145, pair_scores_145.
    rewrite (Znth_map_145 fst pairs i (0, 0) 0) by exact Hpair_i.
    rewrite (Znth_map_145 snd pairs i (0, 0) 0) by exact Hpair_i.
    exact Hall.
Qed.

Lemma final_output_stable_145 : forall input initial_scores output scores,
  score_prefix_rel_145 input initial_scores ->
  output =
    pair_values_145
      (bubble_sort_pairs_fuel_145 (Z.to_nat (Zlength input))
        (score_pairs_145 input initial_scores)) ->
  scores =
    pair_scores_145
      (bubble_sort_pairs_fuel_145 (Z.to_nat (Zlength input))
        (score_pairs_145 input initial_scores)) ->
  stable_digit_sum_order input output.
Proof.
  intros input initial_scores output scores Hrel Hout Hscores.
  set (pairs :=
    bubble_sort_pairs_fuel_145 (Z.to_nat (Zlength input))
      (score_pairs_145 input initial_scores)).
  subst output scores.
  unfold stable_digit_sum_order.
  exists initial_scores, (pair_scores_145 pairs).
  split.
  - apply scored_by_digit_sum_of_score_prefix_rel_145.
    exact Hrel.
  - split.
    + apply scored_by_digit_sum_of_score_prefix_rel_145.
      apply score_prefix_rel_pair_values_scores_145.
      eapply Forall_permutation_145.
      * unfold pairs.
        apply bubble_sort_pairs_fuel_145_perm.
      * apply score_prefix_rel_pairs_Forall_145.
        exact Hrel.
    + intros s.
      rewrite combine_pair_values_scores_145.
      unfold score_pairs_145.
      unfold pairs.
      pose proof (filter_score_bubble_sort_pairs_fuel_145
        s (Z.to_nat (Zlength input)) (combine input initial_scores)) as Hfilter.
      unfold score_eqb_145 in Hfilter.
      exact Hfilter.
Qed.

Lemma final_output_spec_145 : forall input scores output,
  score_prefix_rel_145 input scores ->
  output =
    pair_values_145
      (bubble_sort_pairs_fuel_145 (Z.to_nat (Zlength input))
        (score_pairs_145 input scores)) ->
  problem_145_spec_z input output.
Proof.
  intros input scores output Hrel Hout.
  unfold problem_145_spec_z, problem_145_spec.
  destruct (final_output_perm_sorted_145 input scores output Hrel Hout)
    as [Hperm Hsorted].
  split; [exact Hperm|].
  split; [exact Hsorted|].
  eapply final_output_stable_145.
  - exact Hrel.
  - exact Hout.
  - reflexivity.
Qed.

Lemma pair_values_length_145 : forall pairs,
  Zlength (pair_values_145 pairs) = Zlength pairs.
Proof. intros; unfold pair_values_145; apply Zlength_map_145. Qed.

Lemma pair_scores_length_145 : forall pairs,
  Zlength (pair_scores_145 pairs) = Zlength pairs.
Proof. intros; unfold pair_scores_145; apply Zlength_map_145. Qed.

Lemma initial_pair_values_145 : forall input scores,
  Zlength scores = Zlength input ->
  pair_values_145 (score_pairs_145 input scores) = input.
Proof.
  intros input scores Hlen.
  apply score_pairs_values_145.
  lia.
Qed.

Lemma initial_pair_scores_145 : forall input scores,
  Zlength scores = Zlength input ->
  pair_scores_145 (score_pairs_145 input scores) = scores.
Proof.
  intros input scores Hlen.
  apply score_pairs_scores_145.
  lia.
Qed.

Lemma order_outer_state_145_init : forall input scores,
  order_score_prefix_145 (Zlength input) input scores ->
  order_outer_state_145 0 input scores input scores.
Proof.
  intros input scores Hprefix.
  unfold order_score_prefix_145 in Hprefix.
  destruct Hprefix as [[Hlo Hhi] [Hlen Hrel]].
  replace (sublist 0 (Zlength input) input) with input in Hrel
    by (symmetry; apply sublist_self; lia).
  destruct Hrel as [Hrel_len Hrel_at].
  unfold order_outer_state_145, bubble_outer_pairs_145.
  cbn.
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split.
  - split; [lia|exact Hrel_at].
  - split.
    + split.
      * symmetry; apply initial_pair_values_145; lia.
      * symmetry; apply initial_pair_scores_145; lia.
    + intros Hzero.
      symmetry in Hzero.
      apply Zlength_nil_inv in Hzero.
      subst input.
      unfold problem_145_spec_z, problem_145_spec.
      split.
      * reflexivity.
      * split.
        -- constructor.
        -- apply stable_digit_sum_order_nil_145.
Qed.

Lemma order_inner_state_145_init : forall i input initial_scores output scores,
  order_outer_state_145 i input initial_scores output scores ->
  0 <= i < Zlength input ->
  order_inner_state_145 i 1 input initial_scores output scores.
Proof.
  intros i input initial_scores output scores Hstate Hi.
  unfold order_outer_state_145, order_inner_state_145,
    bubble_outer_pairs_145, bubble_inner_pairs_145 in *.
  destruct Hstate as [Hi0 [Hout_len [Hscore_len [Hrel [Hpairs Hfinal]]]]].
  split; [lia|].
  split; [lia|].
  split; [exact Hout_len|].
  split; [exact Hscore_len|].
  split; [exact Hrel|].
  eexists.
  split; [reflexivity|].
  cbn.
  exact Hpairs.
Qed.

Lemma order_inner_state_145_step_keep : forall i j input initial_scores output scores,
  order_inner_state_145 i j input initial_scores output scores ->
  1 <= j < Zlength input ->
  Znth (j - 1) scores 0 <= Znth j scores 0 ->
  order_inner_state_145 i (j + 1) input initial_scores output scores.
Proof.
  intros i j input initial_scores output scores Hstate Hj Hkeep.
  unfold order_inner_state_145, bubble_inner_pairs_145 in *.
  destruct Hstate as [Hi [Hj0 [Hout_len [Hscore_len [Hrel Hpairs]]]]].
  destruct Hpairs as [outer_pairs [Houter [Houtput Hscores]]].
  split; [lia|].
  split; [lia|].
  split; [exact Hout_len|].
  split; [exact Hscore_len|].
  split; [exact Hrel|].
  eexists.
  split; [exact Houter|].
  replace (Z.to_nat (j + 1 - 1)) with (S (Z.to_nat (j - 1))) by lia.
  rewrite bubble_pass_pairs_from_145_next.
  replace (0 + Z.to_nat (j - 1))%nat with (Z.to_nat (j - 1)) by lia.
  set (pairs := bubble_pass_pairs_from_145 (Z.to_nat (j - 1)) 0 outer_pairs).
  assert (Hlen_pairs : Zlength pairs = Zlength input).
  {
    unfold pairs.
    repeat rewrite Zlength_correct.
    rewrite bubble_pass_pairs_from_145_length.
    subst outer_pairs.
    rewrite bubble_sort_pairs_fuel_145_length.
    unfold score_prefix_rel_145 in Hrel.
    destruct Hrel as [Hinit_len _].
    rewrite <- Zlength_correct.
    rewrite <- (Zlength_correct input).
    apply score_pairs_Zlength_145.
    lia.
  }
  assert (Hkeep_pair :
    snd (Znth (j - 1) pairs (0, 0)) <= snd (Znth ((j - 1) + 1) pairs (0, 0))).
  {
    rewrite Hscores in Hkeep.
    fold pairs in Hkeep.
    unfold pair_scores_145 in Hkeep.
    rewrite (Znth_map_145 snd pairs (j - 1) (0, 0) 0) in Hkeep by lia.
    rewrite (Znth_map_145 snd pairs j (0, 0) 0) in Hkeep by lia.
    replace (j - 1 + 1) with j by lia.
    exact Hkeep.
  }
  rewrite swap_adjacent_pair_145_keep by (try lia; exact Hkeep_pair).
  unfold pairs.
  split; assumption.
Qed.

Lemma order_inner_state_145_step_swap : forall i j input initial_scores output scores,
  order_inner_state_145 i j input initial_scores output scores ->
  1 <= j < Zlength input ->
  Znth (j - 1) scores 0 > Znth j scores 0 ->
  order_inner_state_145 i (j + 1) input initial_scores
    (replace_Znth (j - 1) (Znth j output 0)
      (replace_Znth j (Znth (j - 1) output 0) output))
    (replace_Znth (j - 1) (Znth j scores 0)
      (replace_Znth j (Znth (j - 1) scores 0) scores)).
Proof.
  intros i j input initial_scores output scores Hstate Hj Hswap.
  unfold order_inner_state_145, bubble_inner_pairs_145 in *.
  destruct Hstate as [Hi [Hj0 [Hout_len [Hscore_len [Hrel Hpairs]]]]].
  destruct Hpairs as [outer_pairs [Houter [Houtput Hscores]]].
  split; [lia|].
  split; [lia|].
  split; [repeat rewrite replace_Znth_length_145; lia|].
  split; [repeat rewrite replace_Znth_length_145; lia|].
  split; [exact Hrel|].
  - eexists.
    split; [exact Houter|].
    replace (Z.to_nat (j + 1 - 1)) with (S (Z.to_nat (j - 1))) by lia.
    rewrite bubble_pass_pairs_from_145_next.
    replace (0 + Z.to_nat (j - 1))%nat with (Z.to_nat (j - 1)) by lia.
    set (pairs := bubble_pass_pairs_from_145 (Z.to_nat (j - 1)) 0 outer_pairs).
    assert (Hlen_pairs : Zlength pairs = Zlength input).
    {
      unfold pairs.
      repeat rewrite Zlength_correct.
      rewrite bubble_pass_pairs_from_145_length.
      subst outer_pairs.
      rewrite bubble_sort_pairs_fuel_145_length.
      unfold score_prefix_rel_145 in Hrel.
      destruct Hrel as [Hinit_len _].
      rewrite <- Zlength_correct.
      rewrite <- (Zlength_correct input).
      apply score_pairs_Zlength_145.
      lia.
    }
    assert (Hswap_pair :
      snd (Znth (j - 1) pairs (0, 0)) > snd (Znth ((j - 1) + 1) pairs (0, 0))).
    {
      rewrite Hscores in Hswap.
      fold pairs in Hswap.
      unfold pair_scores_145 in Hswap.
      rewrite (Znth_map_145 snd pairs (j - 1) (0, 0) 0) in Hswap by lia.
      rewrite (Znth_map_145 snd pairs j (0, 0) 0) in Hswap by lia.
      replace (j - 1 + 1) with j by lia.
      exact Hswap.
    }
    rewrite swap_adjacent_pair_145_swap by (try lia; exact Hswap_pair).
    replace (j - 1 + 1) with j by lia.
    rewrite Houtput, Hscores.
    split.
    + unfold pair_values_145.
      fold pairs.
      rewrite (Znth_map_145 fst pairs j (0, 0) 0) by lia.
      rewrite (Znth_map_145 fst pairs (j - 1) (0, 0) 0) by lia.
      rewrite !map_replace_Znth_145.
      reflexivity.
    + unfold pair_scores_145.
      fold pairs.
      rewrite (Znth_map_145 snd pairs j (0, 0) 0) by lia.
      rewrite (Znth_map_145 snd pairs (j - 1) (0, 0) 0) by lia.
      rewrite !map_replace_Znth_145.
      reflexivity.
Qed.

Lemma order_inner_state_145_final_spec : forall i input initial_scores output scores,
  order_inner_state_145 i (Zlength input) input initial_scores output scores ->
  i + 1 = Zlength input ->
  problem_145_spec_z input output.
Proof.
  intros i input initial_scores output scores Hstate Hdone.
  unfold order_inner_state_145, bubble_inner_pairs_145 in Hstate.
  destruct Hstate as [Hi [Hj [Hout_len [Hscore_len [Hrel Hpairs]]]]].
  destruct Hpairs as [outer_pairs [Houter [Houtput Hscores]]].
  eapply final_output_spec_145.
  - exact Hrel.
  - replace (Z.to_nat (Zlength input)) with (S (Z.to_nat i)) by lia.
    rewrite bubble_sort_pairs_fuel_145_snoc.
    unfold bubble_pass_pairs_145.
    rewrite bubble_sort_pairs_fuel_145_length.
    assert (Hfuel : Z.to_nat (Zlength input - 1) = (length input - 1)%nat).
    {
      rewrite Zlength_correct.
      rewrite Z2Nat.inj_sub by lia.
      rewrite Nat2Z.id.
      reflexivity.
    }
    rewrite Hfuel in Houtput.
    subst outer_pairs.
    assert (Hpair_len_nat :
      length (score_pairs_145 input initial_scores) = length input).
    {
      apply Nat2Z.inj.
      repeat rewrite <- Zlength_correct.
      rewrite score_pairs_Zlength_145.
      - reflexivity.
      - unfold score_prefix_rel_145 in Hrel.
        destruct Hrel as [Hrel_len _].
        lia.
    }
    rewrite Hpair_len_nat.
    exact Houtput.
Qed.

Lemma order_outer_state_145_step : forall i input initial_scores output scores,
  order_inner_state_145 i (Zlength input) input initial_scores output scores ->
  0 <= i < Zlength input ->
  (i + 1 = Zlength input -> problem_145_spec_z input output) ->
  order_outer_state_145 (i + 1) input initial_scores output scores.
Proof.
  intros i input initial_scores output scores Hstate Hi Hfinal.
  unfold order_inner_state_145, order_outer_state_145 in *.
  destruct Hstate as [_ [Hj [Hout_len [Hscore_len [Hrel Hpairs]]]]].
  destruct Hpairs as [outer_pairs [Houter [Houtput Hscores]]].
  split; [lia|].
  split; [exact Hout_len|].
  split; [exact Hscore_len|].
  split; [exact Hrel|].
  split.
  - unfold bubble_outer_pairs_145, bubble_inner_pairs_145 in *.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    rewrite bubble_sort_pairs_fuel_145_snoc.
    unfold bubble_pass_pairs_145.
    rewrite bubble_sort_pairs_fuel_145_length.
    assert (Hfuel : Z.to_nat (Zlength input - 1) = (length input - 1)%nat).
    {
      rewrite Zlength_correct.
      rewrite Z2Nat.inj_sub by lia.
      rewrite Nat2Z.id.
      reflexivity.
    }
    rewrite Hfuel in Houtput, Hscores.
    subst outer_pairs.
    assert (Hpair_len_nat :
      length (score_pairs_145 input initial_scores) = length input).
    {
      apply Nat2Z.inj.
      repeat rewrite <- Zlength_correct.
      rewrite score_pairs_Zlength_145.
      - reflexivity.
      - unfold score_prefix_rel_145 in Hrel.
        destruct Hrel as [Hrel_len _].
        lia.
    }
    rewrite Hpair_len_nat.
    split.
    + exact Houtput.
    + exact Hscores.
  - exact Hfinal.
Qed.
