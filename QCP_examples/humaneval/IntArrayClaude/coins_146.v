Load "../spec/146".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_146_pre_z (nums : list Z) : Prop :=
  problem_146_pre nums.

Definition problem_146_spec_z (nums : list Z) (output : Z) : Prop :=
  problem_146_spec nums output.

Definition first_digit_value (n : Z) : Z :=
  msd_fuel (Z.to_nat n) n.

Definition first_digit_state (original current : Z) : Prop :=
  exists fuel,
    0 <= current <= original /\
    current < 10 ^ Z.of_nat fuel /\
    first_digit_value original = msd_fuel fuel current.

Definition special_number_c (n : Z) : Prop :=
  special_number_b n = true.

Definition not_special_number_c (n : Z) : Prop :=
  special_number_b n = false.

Definition special_filter_prefix (i : Z) (nums : list Z) (count : Z) : Prop :=
  0 <= i <= Zlength nums /\
  count = Z.of_nat (length (filter special_number_b (sublist 0 i nums))).

Definition special_scalar_int_range (x : Z) : Prop :=
  INT_MIN <= x <= INT_MAX.

Definition special_filter_int_range (nums : list Z) : Prop :=
  forall i, 0 <= i < Zlength nums -> special_scalar_int_range (Znth i nums 0).

Lemma special_filter_prefix_0 : forall nums,
  special_filter_prefix 0 nums 0.
Proof.
  intros nums.
  unfold special_filter_prefix.
  rewrite sublist_nil by lia.
  simpl.
  split.
  - split; [lia | rewrite Zlength_correct; lia].
  - reflexivity.
Qed.

Lemma special_filter_prefix_snoc_special : forall nums i count,
  special_filter_prefix i nums count ->
  0 <= i < Zlength nums ->
  special_number_c (Znth i nums 0) ->
  special_filter_prefix (i + 1) nums (count + 1).
Proof.
  intros nums i count [Hbounds Hcount] Hi Hspecial.
  unfold special_filter_prefix in *.
  split; [lia|].
  rewrite (sublist_split 0 (i + 1) i nums)
    by (try rewrite <- Zlength_correct; lia).
  rewrite (sublist_single i nums 0) by (rewrite <- Zlength_correct; lia).
  rewrite filter_app.
  simpl.
  rewrite Hspecial.
  rewrite app_length.
  simpl.
  rewrite Hcount.
  lia.
Qed.

Lemma special_filter_prefix_snoc_not_special : forall nums i count,
  special_filter_prefix i nums count ->
  0 <= i < Zlength nums ->
  not_special_number_c (Znth i nums 0) ->
  special_filter_prefix (i + 1) nums count.
Proof.
  intros nums i count [Hbounds Hcount] Hi Hspecial.
  unfold special_filter_prefix in *.
  split; [lia|].
  rewrite (sublist_split 0 (i + 1) i nums)
    by (try rewrite <- Zlength_correct; lia).
  rewrite (sublist_single i nums 0) by (rewrite <- Zlength_correct; lia).
  rewrite filter_app.
  simpl.
  rewrite Hspecial.
  rewrite app_length.
  simpl.
  rewrite Nat.add_0_r.
  assumption.
Qed.

Lemma problem_146_spec_z_of_prefix_full : forall nums out,
  special_filter_prefix (Zlength nums) nums out ->
  problem_146_spec_z nums out.
Proof.
  intros nums out [_ Hout].
  unfold problem_146_spec_z, problem_146_spec, specialFilter_impl.
  rewrite Hout.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.

Lemma special_filter_prefix_count_bounds : forall i nums count,
  special_filter_prefix i nums count ->
  0 <= count <= i.
Proof.
  intros i nums count [Hi Hcount].
  subst count.
  split.
  - apply Nat2Z.is_nonneg.
  - assert (Hfilter :
        Z.of_nat (length (filter special_number_b (sublist 0 i nums))) <=
        Z.of_nat (length (sublist 0 i nums))).
    {
      apply Nat2Z.inj_le.
      induction (sublist 0 i nums) as [|x xs IH]; simpl.
      - lia.
      - destruct (special_number_b x); simpl; lia.
    }
    rewrite sublist_length in Hfilter.
    + rewrite Z2Nat.id in Hfilter by lia.
      lia.
    + lia.
    + destruct Hi as [_ Hi].
      rewrite <- Zlength_correct.
      exact Hi.
Qed.

Lemma special_scalar_int_range_of_list : forall nums i,
  special_filter_int_range nums ->
  0 <= i < Zlength nums ->
  special_scalar_int_range (Znth i nums 0).
Proof.
  intros nums i Hrange Hi.
  apply Hrange; assumption.
Qed.

Lemma first_digit_state_init : forall x,
  0 <= x ->
  first_digit_state x x.
Proof.
  intros x Hx.
  unfold first_digit_state.
  exists (Z.to_nat x).
  split; [lia|].
  split.
  - rewrite Z2Nat.id by lia.
    apply Z.pow_gt_lin_r; lia.
  - reflexivity.
Qed.

Lemma msd_fuel_small : forall fuel n,
  0 <= n < 10 ->
  msd_fuel fuel n = n.
Proof.
  induction fuel; intros n Hn; simpl.
  - rewrite Z.mod_small by lia. reflexivity.
  - destruct (Z_lt_dec n 10); lia.
Qed.

Lemma first_digit_value_small : forall n,
  0 <= n < 10 ->
  first_digit_value n = n.
Proof.
  intros n Hn.
  unfold first_digit_value.
  apply msd_fuel_small; assumption.
Qed.

Lemma first_digit_state_step : forall original current,
  first_digit_state original current ->
  10 <= current ->
  first_digit_state original (current ÷ 10).
Proof.
  intros original current [fuel [Hrange [Hpow Hval]]] Hcur.
  destruct fuel as [|fuel].
  - simpl in Hpow. lia.
  - unfold first_digit_state.
    exists fuel.
    split.
    + rewrite Z.quot_div_nonneg by lia.
      pose proof (Z.div_pos current 10 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound current 10 current ltac:(lia) ltac:(nia)).
      lia.
    + split.
      * rewrite Z.quot_div_nonneg by lia.
        apply Z.div_lt_upper_bound; try lia.
        replace (10 ^ Z.of_nat (S fuel)) with (10 * 10 ^ Z.of_nat fuel) in Hpow
          by (rewrite Nat2Z.inj_succ; rewrite Z.pow_succ_r by lia; reflexivity).
        exact Hpow.
      * rewrite Hval.
        simpl.
        destruct (Z_lt_dec current 10); [lia|].
        rewrite Z.quot_div_nonneg by lia.
        reflexivity.
Qed.

Lemma last_digit_rem_bounds : forall x,
  0 < x ->
  0 <= x % 10 <= 9.
Proof.
  intros x Hx.
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound x 10 ltac:(lia)).
  lia.
Qed.

Lemma odd_rem_iff_odd : forall n,
  0 <= n ->
  (n % 2 = 1 <-> Z.odd n = true).
Proof.
  intros n Hn.
  rewrite Z.rem_mod_nonneg by lia.
  rewrite Zmod_odd.
  destruct (Z.odd n); split; intros H; try reflexivity; try discriminate.
Qed.

Lemma special_number_intro_from_digits : forall x first last,
  10 < x ->
  first_digit_state x first ->
  0 <= first < 10 ->
  0 <= last <= 9 ->
  last = x % 10 ->
  first % 2 = 1 ->
  last % 2 = 1 ->
  special_number_c x.
Proof.
  intros x first last Hx [fuel [Hfr [Hpow Hfv]]] Hfirst Hlast_range Hlast Hfirst_odd Hlast_odd.
  assert (Hfirst_bool : Z.odd (msd_fuel fuel first) = true).
  {
    rewrite msd_fuel_small by lia.
    destruct (odd_rem_iff_odd first ltac:(lia)) as [H _].
    apply H in Hfirst_odd.
    exact Hfirst_odd.
  }
  assert (Hlast_bool : Z.odd (last_digit x) = true).
  {
    unfold last_digit.
    replace (Z.abs x) with x by lia.
    rewrite <- Z.rem_mod_nonneg by lia.
    rewrite Z.abs_eq.
    - destruct (odd_rem_iff_odd last ltac:(lia)) as [H _].
      apply H in Hlast_odd.
      rewrite Hlast in Hlast_odd.
      exact Hlast_odd.
    - pose proof (last_digit_rem_bounds x ltac:(lia)).
      lia.
  }
  unfold special_number_c, special_number_b, first_digit_value in *.
  rewrite Z.abs_eq by lia.
  apply andb_true_intro.
  split.
  - apply andb_true_intro.
    split.
    + apply Z.ltb_lt; lia.
    + rewrite Hfv. exact Hfirst_bool.
  - exact Hlast_bool.
Qed.

Lemma special_number_false_of_le10 : forall x,
  x <= 10 ->
  not_special_number_c x.
Proof.
  intros x Hx.
  unfold not_special_number_c, special_number_b.
  destruct (10 <? x) eqn:Hlt; [apply Z.ltb_lt in Hlt; lia|reflexivity].
Qed.

Lemma special_number_false_first_even : forall x first last,
  10 < x ->
  first_digit_state x first ->
  0 <= first < 10 ->
  0 <= last <= 9 ->
  last = x % 10 ->
  first % 2 <> 1 ->
  not_special_number_c x.
Proof.
  intros x first last Hx [fuel [Hfr [Hpow Hfv]]] Hfirst Hlast_range Hlast Hfirst_even.
  unfold not_special_number_c, special_number_b, first_digit_value in *.
  rewrite Z.abs_eq by lia.
  replace (10 <? x) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite Hfv.
  rewrite msd_fuel_small by lia.
  destruct (Z.odd first) eqn:Hodd; [|reflexivity].
  exfalso.
  apply Hfirst_even.
  destruct (odd_rem_iff_odd first ltac:(lia)) as [_ H].
  apply H; exact Hodd.
Qed.

Lemma special_number_false_last_even : forall x first last,
  10 < x ->
  first_digit_state x first ->
  0 <= first < 10 ->
  0 <= last <= 9 ->
  last = x % 10 ->
  last % 2 <> 1 ->
  not_special_number_c x.
Proof.
  intros x first last Hx [fuel [Hfr [Hpow Hfv]]] Hfirst Hlast_range Hlast Hlast_even.
  unfold not_special_number_c, special_number_b, first_digit_value in *.
  rewrite Z.abs_eq by lia.
  replace (10 <? x) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite Hfv.
  rewrite msd_fuel_small by lia.
  destruct (Z.odd first) eqn:Hfirst_odd; [|reflexivity].
  unfold last_digit.
  rewrite <- Z.rem_mod_nonneg by lia.
  rewrite Z.abs_eq.
  - rewrite <- Hlast.
    destruct (Z.odd last) eqn:Hodd; [|reflexivity].
    exfalso.
    apply Hlast_even.
    destruct (odd_rem_iff_odd last ltac:(lia)) as [_ H].
    apply H; exact Hodd.
  - pose proof (last_digit_rem_bounds x ltac:(lia)).
    lia.
Qed.
