Load "../spec/84".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
From SimpleC.EE Require Import string_bridge.
From SimpleC.EE Require Export coins_44 coins_103.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_84_pre_z (N : Z) : Prop :=
  problem_84_pre (Z.to_nat N).

Definition problem_84_spec_z (N : Z) (output : list Z) : Prop :=
  problem_84_spec (Z.to_nat N) (string_of_list_z output).

Definition decimal_sum_value_z (orig sum : Z) : Prop :=
  sum = Z.of_nat (sum_decimal_digits (Z.to_nat orig)).

Definition decimal_sum_state_z (orig x sum : Z) : Prop :=
  0 <= x /\
  0 <= sum /\
  sum + x <= orig /\
  exists fuel,
    (Z.to_nat x <= fuel)%nat /\
    sum + Z.of_nat (sum_decimal_digits_aux fuel (Z.to_nat x)) =
      Z.of_nat (sum_decimal_digits (Z.to_nat orig)).

Lemma decimal_sum_state_init : forall orig,
  0 <= orig ->
  decimal_sum_state_z orig orig 0.
Proof.
  intros orig Horig.
  unfold decimal_sum_state_z.
  repeat split; try lia.
  exists (Z.to_nat orig).
  split; [lia|].
  unfold sum_decimal_digits.
  reflexivity.
Qed.

Lemma sum_decimal_digits_aux_step_z : forall fuel x,
  0 < x ->
  Z.of_nat (sum_decimal_digits_aux (S fuel) (Z.to_nat x)) =
    x mod 10 +
    Z.of_nat (sum_decimal_digits_aux fuel (Z.to_nat (x / 10))).
Proof.
  intros fuel x Hx.
  destruct (Z.to_nat x) as [|xn] eqn:Hxnat; [lia|].
  change (sum_decimal_digits_aux (S fuel) (S xn)) with
    ((S xn mod 10 + sum_decimal_digits_aux fuel (S xn / 10))%nat).
  rewrite Nat2Z.inj_add.
  replace (Z.of_nat (S xn mod 10)) with (x mod 10).
  2:{
    rewrite <- Hxnat.
    rewrite Nat2Z.inj_mod by lia.
    rewrite Z2Nat.id by lia.
    reflexivity.
  }
  replace (sum_decimal_digits_aux fuel (S xn / 10)) with
    (sum_decimal_digits_aux fuel (Z.to_nat (x / 10))).
  2:{
    rewrite <- Hxnat.
    rewrite Z2Nat.inj_div by lia.
    reflexivity.
  }
  reflexivity.
Qed.

Lemma decimal_sum_state_step : forall orig x sum,
  0 < x ->
  decimal_sum_state_z orig x sum ->
  decimal_sum_state_z orig (x / 10) (sum + x mod 10).
Proof.
  intros orig x sum Hx [Hx_nonneg [Hsum [Hbound Hstate]]].
  unfold decimal_sum_state_z.
  repeat split.
  - apply Z.div_pos; lia.
  - pose proof (Z.mod_pos_bound x 10 ltac:(lia)).
    lia.
  - assert (x = 10 * (x / 10) + x mod 10).
    { apply Z.div_mod; lia. }
    assert (x / 10 <= 10 * (x / 10)).
    { pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)). nia. }
    lia.
  - destruct Hstate as [fuel [Hfuel Hstate]].
    destruct fuel as [|fuel']; [lia|].
    exists fuel'.
    split.
    + rewrite Z2Nat.inj_div by lia.
      apply Nat.lt_succ_r.
      eapply Nat.lt_le_trans.
      * apply Nat.div_lt; lia.
      * exact Hfuel.
    + rewrite <- Hstate.
      rewrite sum_decimal_digits_aux_step_z by lia.
      lia.
Qed.

Lemma decimal_sum_state_sum_bound : forall orig x sum,
  0 <= orig ->
  orig <= 10000 ->
  decimal_sum_state_z orig x sum ->
  sum <= 10000.
Proof.
  intros orig x sum Horig Horig_bound [Hx [Hsum [Hbound _]]].
  lia.
Qed.

Lemma decimal_sum_state_done : forall orig sum,
  decimal_sum_state_z orig 0 sum ->
  decimal_sum_value_z orig sum.
Proof.
  intros orig sum [_ [_ [_ [fuel [_ Hstate]]]]].
  unfold decimal_sum_value_z.
  assert (sum_decimal_digits_aux fuel 0 = 0)%nat as Hzero.
  { destruct fuel; reflexivity. }
  change (Z.to_nat 0) with 0%nat in Hstate.
  rewrite Hzero in Hstate.
  lia.
Qed.

Lemma nat_to_binary_string_pos_aux_zero : forall fuel,
  nat_to_binary_string_pos_aux fuel 0 = "".
Proof.
  destruct fuel; reflexivity.
Qed.

Lemma nat_to_binary_string_pos_aux_to_digits : forall fuel n,
  (0 < n)%nat ->
  (n < Nat.pow 2 fuel)%nat ->
  nat_to_binary_string_pos_aux fuel n =
    string_of_list_z (binary_digits_z (Z.of_nat n)).
Proof.
  induction fuel as [|fuel IH]; intros n Hn Hbound.
  - simpl in Hbound. lia.
  - destruct n as [|n']; [lia|].
    simpl nat_to_binary_string_pos_aux.
    replace (Nat.eqb (S n') 0) with false by (symmetry; apply Nat.eqb_neq; lia).
    destruct n' as [|n''].
    + rewrite nat_to_binary_string_pos_aux_zero.
      unfold binary_digits_z.
      rewrite base_digits_z_small by lia.
      reflexivity.
    + rewrite IH.
      2:{ change (0 < S (S n'') / 2)%nat.
          apply Nat.div_str_pos; lia. }
      2:{
        change (S (S n'') / 2 < 2 ^ fuel)%nat.
        apply Nat.div_lt_upper_bound; [lia|].
        replace (2 ^ S fuel)%nat with (2 * 2 ^ fuel)%nat in Hbound by (simpl; lia).
        lia.
      }
      unfold binary_digits_z at 2.
      rewrite base_digits_z_step by lia.
      rewrite string_of_list_z_app.
      unfold binary_digits_z.
      replace (Z.of_nat (S (S n'')) / 2) with
        (Z.of_nat (S (S n'') / 2)) by
        (rewrite Nat2Z.inj_div by lia; reflexivity).
      replace (Z.of_nat (S (S n'')) mod 2) with
        (Z.of_nat (S (S n'') mod 2)) by
        (rewrite Nat2Z.inj_mod by lia; reflexivity).
      destruct (Nat.eqb (S (S n'') mod 2) 0) eqn:Hmod.
      * apply Nat.eqb_eq in Hmod.
        rewrite Hmod.
        simpl.
        rewrite ascii_of_z_48.
        change (match snd (Nat.divmod n'' 1 1 1) with
                | O => 1%nat
                | S _ => 0%nat
                end) with (S (S n'') mod 2)%nat.
        rewrite Hmod.
        reflexivity.
      * apply Nat.eqb_neq in Hmod.
        assert (S (S n'') mod 2 = 1)%nat as Hone.
        { pose proof (Nat.mod_upper_bound (S (S n'')) 2 ltac:(lia)).
          lia. }
        rewrite Hone.
        simpl.
        rewrite ascii_of_z_49.
        change (match snd (Nat.divmod n'' 1 1 1) with
                | O => 1%nat
                | S _ => 0%nat
                end) with (S (S n'') mod 2)%nat.
        rewrite Hone.
        reflexivity.
Qed.

Lemma nat_lt_pow2_self_84 : forall n,
  (0 < n)%nat -> (n < 2 ^ n)%nat.
Proof.
  induction n; intros Hn; try lia.
  destruct n.
  - simpl. lia.
  - replace (2 ^ S (S n))%nat with (2 * 2 ^ S n)%nat by (simpl; lia).
    pose proof (IHn ltac:(lia)).
    assert (1 <= 2 ^ S n)%nat.
    { pose proof (Nat.pow_nonzero 2 (S n) ltac:(lia)). lia. }
    lia.
Qed.

Lemma nat_to_binary_string_84_to_digits : forall n,
  nat_to_binary_string n =
    string_of_list_z (binary_digits_z (Z.of_nat n)).
Proof.
  intros n.
  unfold nat_to_binary_string.
  destruct (Nat.eqb n 0) eqn:Hn0.
  - apply Nat.eqb_eq in Hn0. subst n.
    unfold binary_digits_z.
    rewrite base_digits_z_zero by lia.
    reflexivity.
  - apply Nat.eqb_neq in Hn0.
    apply nat_to_binary_string_pos_aux_to_digits.
    + lia.
    + apply nat_lt_pow2_self_84. lia.
Qed.

Lemma problem_84_spec_z_intro : forall N out_l sum,
  0 <= N ->
  decimal_sum_value_z N sum ->
  out_l = binary_digits_z sum ->
  problem_84_spec_z N out_l.
Proof.
  intros N out_l sum HN Hsum Hout.
  subst out_l.
  unfold problem_84_spec_z, problem_84_spec, solve_impl.
  unfold decimal_sum_value_z in Hsum.
  subst sum.
  symmetry.
  apply nat_to_binary_string_84_to_digits.
Qed.

Lemma problem_84_spec_z_zero :
  problem_84_spec_z 0 [48].
Proof.
  apply problem_84_spec_z_intro with (sum := 0).
  - lia.
  - reflexivity.
  - unfold binary_digits_z.
    rewrite base_digits_z_zero by lia.
    reflexivity.
Qed.
