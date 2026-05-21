Load "../spec/124".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_digit_z (x : Z) : Prop :=
  48 <= x <= 57.

Definition is_separator_index (i : Z) : Prop :=
  i = 2 \/ i = 5.

Definition date_char_valid (i : Z) (l : list Z) : Prop :=
  if orb (Z.eqb i 2) (Z.eqb i 5)
  then Znth i l 0 = 45
  else is_digit_z (Znth i l 0).

Definition date_prefix_valid (i : Z) (l : list Z) : Prop :=
  forall k, 0 <= k < i -> date_char_valid k l.

Definition month_z (l : list Z) : Z :=
  (Znth 0 l 0 - 48) * 10 + (Znth 1 l 0 - 48).

Definition day_z (l : list Z) : Z :=
  (Znth 3 l 0 - 48) * 10 + (Znth 4 l 0 - 48).

Definition year_z (l : list Z) : Z :=
  (Znth 6 l 0 - 48) * 1000 +
  (Znth 7 l 0 - 48) * 100 +
  (Znth 8 l 0 - 48) * 10 +
  (Znth 9 l 0 - 48).

Definition days_in_month_z (m : Z) : Z :=
  if orb (orb (orb (orb (orb (orb (Z.eqb m 1) (Z.eqb m 3)) (Z.eqb m 5)) (Z.eqb m 7))
              (Z.eqb m 8)) (Z.eqb m 10)) (Z.eqb m 12) then 31
  else if orb (orb (orb (Z.eqb m 4) (Z.eqb m 6)) (Z.eqb m 9)) (Z.eqb m 11) then 30
  else if Z.eqb m 2 then 29
  else 0.

Definition date_format_z (l : list Z) : Prop :=
  Zlength l = 10 /\
  Znth 2 l 0 = 45 /\
  Znth 5 l 0 = 45 /\
  is_digit_z (Znth 0 l 0) /\
  is_digit_z (Znth 1 l 0) /\
  is_digit_z (Znth 3 l 0) /\
  is_digit_z (Znth 4 l 0) /\
  is_digit_z (Znth 6 l 0) /\
  is_digit_z (Znth 7 l 0) /\
  is_digit_z (Znth 8 l 0) /\
  is_digit_z (Znth 9 l 0).

Definition valid_date_z (l : list Z) : Prop :=
  date_format_z l /\
  1 <= month_z l <= 12 /\
  1 <= day_z l <= days_in_month_z (month_z l).

Definition problem_124_pre_z (s : list Z) : Prop :=
  problem_124_pre (list_ascii_of_string (string_of_list_z s)).

Definition problem_124_spec_z (s : list Z) (output : Z) : Prop :=
  output = 1 <-> problem_124_spec (string_of_list_z s).

Lemma date_prefix_valid_0 : forall l,
  date_prefix_valid 0 l.
Proof.
  unfold date_prefix_valid.
  intros l k Hk.
  lia.
Qed.

Lemma date_prefix_valid_step_sep : forall i l,
  0 <= i ->
  date_prefix_valid i l ->
  (i = 2 \/ i = 5) ->
  Znth i l 0 = 45 ->
  date_prefix_valid (i + 1) l.
Proof.
  unfold date_prefix_valid, date_char_valid.
  intros i l Hi Hpre Hsep Hchar k Hk.
  destruct (Z.eq_dec k i) as [-> | Hne].
  - destruct Hsep as [-> | ->]; simpl; exact Hchar.
  - apply Hpre; lia.
Qed.

Lemma date_prefix_valid_step_digit : forall i l,
  0 <= i ->
  date_prefix_valid i l ->
  i <> 2 ->
  i <> 5 ->
  is_digit_z (Znth i l 0) ->
  date_prefix_valid (i + 1) l.
Proof.
  unfold date_prefix_valid, date_char_valid.
  intros i l Hi Hpre H2 H5 Hdigit k Hk.
  destruct (Z.eq_dec k i) as [-> | Hne].
  - replace (Z.eqb i 2) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.eqb i 5) with false by (symmetry; apply Z.eqb_neq; lia).
    exact Hdigit.
  - apply Hpre; lia.
Qed.

Lemma date_prefix_valid_10_format : forall l,
  Zlength l = 10 ->
  date_prefix_valid 10 l ->
  date_format_z l.
Proof.
  intros l Hlen Hpre.
  unfold date_format_z.
  repeat split; try assumption.
  - specialize (Hpre 2 ltac:(lia)).
    unfold date_char_valid in Hpre.
    simpl in Hpre.
    exact Hpre.
  - specialize (Hpre 5 ltac:(lia)).
    unfold date_char_valid in Hpre.
    simpl in Hpre.
    exact Hpre.
  - specialize (Hpre 0 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 0 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 1 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 1 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 3 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 3 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 4 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 4 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 6 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 6 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 7 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 7 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 8 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 8 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 9 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 9 ltac:(lia)); unfold date_char_valid, is_digit_z in Hpre; simpl in Hpre; lia.
Qed.

Lemma date_prefix_valid_digit_at : forall i l k,
  date_prefix_valid i l ->
  0 <= k < i ->
  k <> 2 ->
  k <> 5 ->
  is_digit_z (Znth k l 0).
Proof.
  intros i l k Hpre Hk H2 H5.
  specialize (Hpre k Hk).
  unfold date_char_valid in Hpre.
  replace (Z.eqb k 2) with false in Hpre by (symmetry; apply Z.eqb_neq; lia).
  replace (Z.eqb k 5) with false in Hpre by (symmetry; apply Z.eqb_neq; lia).
  exact Hpre.
Qed.

Lemma valid_date_z_format : forall l,
  valid_date_z l -> date_format_z l.
Proof.
  intros l H.
  unfold valid_date_z in H.
  tauto.
Qed.

Lemma valid_date_z_len : forall l,
  valid_date_z l -> Zlength l = 10.
Proof.
  intros l H.
  destruct (valid_date_z_format l H) as [Hlen _].
  exact Hlen.
Qed.

Lemma valid_date_z_sep_at : forall l i,
  valid_date_z l ->
  (i = 2 \/ i = 5) ->
  Znth i l 0 = 45.
Proof.
  intros l i Hvalid Hsep.
  destruct (valid_date_z_format l Hvalid) as
    [_ [H2 [H5 _]]].
  destruct Hsep as [-> | ->]; assumption.
Qed.

Lemma valid_date_z_digit_at : forall l i,
  valid_date_z l ->
  0 <= i < 10 ->
  i <> 2 ->
  i <> 5 ->
  is_digit_z (Znth i l 0).
Proof.
  intros l i Hvalid Hi H2 H5.
  destruct (valid_date_z_format l Hvalid) as
    [_ [_ [_ [H0 [H1 [H3 [H4 [H6 [H7 [H8 H9]]]]]]]]]].
  assert (i = 0 \/ i = 1 \/ i = 3 \/ i = 4 \/
          i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; assumption.
Qed.

Lemma valid_date_z_month : forall l,
  valid_date_z l -> 1 <= month_z l <= 12.
Proof.
  intros l H.
  unfold valid_date_z in H.
  tauto.
Qed.

Lemma valid_date_z_day : forall l,
  valid_date_z l -> 1 <= day_z l <= days_in_month_z (month_z l).
Proof.
  intros l H.
  unfold valid_date_z in H.
  tauto.
Qed.

Lemma days_in_month_z_31_bad : forall m,
  (m = 4 \/ m = 6 \/ m = 9 \/ m = 11 \/ m = 2) ->
  days_in_month_z m < 31.
Proof.
  intros m Hm.
  unfold days_in_month_z.
  destruct Hm as [-> | [-> | [-> | [-> | ->]]]]; reflexivity.
Qed.

Lemma days_in_month_z_feb_lt_30 :
  days_in_month_z 2 < 30.
Proof.
  unfold days_in_month_z.
  reflexivity.
Qed.

Lemma days_in_month_z_le_31 : forall m,
  days_in_month_z m <= 31.
Proof.
  intro m.
  unfold days_in_month_z.
  destruct (Z.eqb m 1); destruct (Z.eqb m 3); destruct (Z.eqb m 5);
  destruct (Z.eqb m 7); destruct (Z.eqb m 8); destruct (Z.eqb m 10);
  destruct (Z.eqb m 12); destruct (Z.eqb m 4); destruct (Z.eqb m 6);
  destruct (Z.eqb m 9); destruct (Z.eqb m 11); destruct (Z.eqb m 2);
  simpl; lia.
Qed.

Lemma valid_date_z_intro_from_checks : forall l,
  date_format_z l ->
  1 <= month_z l <= 12 ->
  1 <= day_z l <= 31 ->
  ~(day_z l = 31 /\
    (month_z l = 4 \/ month_z l = 6 \/ month_z l = 9 \/
     month_z l = 11 \/ month_z l = 2)) ->
  ~(day_z l = 30 /\ month_z l = 2) ->
  valid_date_z l.
Proof.
  intros l Hfmt Hmonth Hday Hnot31 HnotFeb30.
  unfold valid_date_z.
  split; [exact Hfmt |].
  split; [exact Hmonth |].
  unfold days_in_month_z.
  assert (month_z l = 1 \/ month_z l = 2 \/ month_z l = 3 \/
          month_z l = 4 \/ month_z l = 5 \/ month_z l = 6 \/
          month_z l = 7 \/ month_z l = 8 \/ month_z l = 9 \/
          month_z l = 10 \/ month_z l = 11 \/ month_z l = 12) by lia.
  destruct H as [Hm | [Hm | [Hm | [Hm | [Hm | [Hm | [Hm | [Hm | [Hm | [Hm | [Hm | Hm]]]]]]]]]]];
    rewrite Hm; simpl in *; lia.
Qed.

Lemma ascii_of_z_inj_const_124 : forall x n,
  0 <= x < 256 ->
  (n < 256)%nat ->
  ascii_of_z x = ascii_of_nat n ->
  x = Z.of_nat n.
Proof.
  intros x n Hx Hn Heq.
  apply (f_equal nat_of_ascii) in Heq.
  rewrite nat_of_ascii_ascii_of_z in Heq by exact Hx.
  rewrite nat_ascii_embedding in Heq by lia.
  lia.
Qed.

Lemma nat_of_digit_ascii_of_z : forall x,
  is_digit_z x ->
  nat_of_digit (ascii_of_z x) = Some (Z.to_nat (x - 48)).
Proof.
  intros x Hdigit.
  unfold is_digit_z in Hdigit.
  assert (x = 48 \/ x = 49 \/ x = 50 \/ x = 51 \/ x = 52 \/
          x = 53 \/ x = 54 \/ x = 55 \/ x = 56 \/ x = 57) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    reflexivity.
Qed.

Lemma nat_of_digit_ascii_of_z_inv : forall x d,
  0 <= x < 256 ->
  nat_of_digit (ascii_of_z x) = Some d ->
  is_digit_z x /\ d = Z.to_nat (x - 48).
Proof.
  intros x d Hrange Hdigit.
  assert (Hcase :
    ascii_of_z x = "0"%char \/ ascii_of_z x = "1"%char \/
    ascii_of_z x = "2"%char \/ ascii_of_z x = "3"%char \/
    ascii_of_z x = "4"%char \/ ascii_of_z x = "5"%char \/
    ascii_of_z x = "6"%char \/ ascii_of_z x = "7"%char \/
    ascii_of_z x = "8"%char \/ ascii_of_z x = "9"%char).
  {
    remember (ascii_of_z x) as c.
    destruct c as [[] [] [] [] [] [] [] []]; simpl in Hdigit; try discriminate;
      repeat (first [left; subst; reflexivity | right]); subst; reflexivity.
  }
  destruct Hcase as [E | [E | [E | [E | [E | [E | [E | [E | [E | E]]]]]]]]].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_z_inj_const_124 with (n := 48%nat) in E; try lia.
    subst; split; [unfold is_digit_z; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_z_inj_const_124 with (n := 49%nat) in E; try lia.
    subst; split; [unfold is_digit_z; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_z_inj_const_124 with (n := 50%nat) in E; try lia.
    subst; split; [unfold is_digit_z; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_z_inj_const_124 with (n := 51%nat) in E; try lia.
    subst; split; [unfold is_digit_z; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_z_inj_const_124 with (n := 52%nat) in E; try lia.
    subst; split; [unfold is_digit_z; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_z_inj_const_124 with (n := 53%nat) in E; try lia.
    subst; split; [unfold is_digit_z; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_z_inj_const_124 with (n := 54%nat) in E; try lia.
    subst; split; [unfold is_digit_z; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_z_inj_const_124 with (n := 55%nat) in E; try lia.
    subst; split; [unfold is_digit_z; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_z_inj_const_124 with (n := 56%nat) in E; try lia.
    subst; split; [unfold is_digit_z; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_z_inj_const_124 with (n := 57%nat) in E; try lia.
    subst; split; [unfold is_digit_z; lia | reflexivity].
Qed.

Lemma nat_of_2_digits_ascii_of_z : forall x y,
  is_digit_z x ->
  is_digit_z y ->
  nat_of_2_digits (ascii_of_z x) (ascii_of_z y) =
    Some (Z.to_nat ((x - 48) * 10 + (y - 48))).
Proof.
  intros x y Hx Hy.
  unfold nat_of_2_digits.
  rewrite nat_of_digit_ascii_of_z by exact Hx.
  rewrite nat_of_digit_ascii_of_z by exact Hy.
  f_equal.
  unfold is_digit_z in *.
  rewrite Z2Nat.inj_add by lia.
  rewrite Z2Nat.inj_mul by lia.
  lia.
Qed.

Lemma nat_of_4_digits_ascii_of_z : forall a b c d,
  is_digit_z a ->
  is_digit_z b ->
  is_digit_z c ->
  is_digit_z d ->
  nat_of_4_digits (ascii_of_z a) (ascii_of_z b) (ascii_of_z c) (ascii_of_z d) =
    Some (Z.to_nat ((a - 48) * 1000 + (b - 48) * 100 + (c - 48) * 10 + (d - 48))).
Proof.
  intros a b c d Ha Hb Hc Hd.
  unfold nat_of_4_digits.
  rewrite nat_of_digit_ascii_of_z by exact Ha.
  rewrite nat_of_digit_ascii_of_z by exact Hb.
  rewrite nat_of_digit_ascii_of_z by exact Hc.
  rewrite nat_of_digit_ascii_of_z by exact Hd.
  f_equal.
  unfold is_digit_z in *.
  repeat rewrite Z2Nat.inj_add by lia.
  repeat rewrite Z2Nat.inj_mul by lia.
  lia.
Qed.

Lemma days_in_month_z_nat : forall m,
  1 <= m <= 12 ->
  Z.of_nat (days_in_month (Z.to_nat m)) = days_in_month_z m.
Proof.
  intros m Hm.
  assert (m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/
          m = 7 \/ m = 8 \/ m = 9 \/ m = 10 \/ m = 11 \/ m = 12) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
    reflexivity.
Qed.

Ltac destruct_date_list l :=
  destruct l as [| z0 [| z1 [| z2 [| z3 [| z4 [| z5 [| z6 [| z7 [| z8 [| z9 [| extra]]]]]]]]]]];
  simpl in *; try repeat rewrite Zlength_cons in *; try rewrite Zlength_nil in *;
  simpl in *;
  try match goal with
      | H : context[Zlength ?xs] |- _ => pose proof (Zlength_nonneg xs); lia
      end;
  try lia.

Lemma valid_date_z_to_problem_124_spec : forall l,
  ascii_range_z l ->
  valid_date_z l ->
  problem_124_spec (string_of_list_z l).
Proof.
  intros l Hrange Hvalid.
  destruct Hvalid as [Hfmt [Hmonth Hday]].
  unfold date_format_z in Hfmt.
  destruct Hfmt as
    [Hlen [Hsep2 [Hsep5 [H0 [H1 [H3 [H4 [H6 [H7 [H8 H9]]]]]]]]]].
  destruct_date_list l.
  simpl in Hsep2, Hsep5.
  change (z2 = 45) in Hsep2.
  change (z5 = 45) in Hsep5.
  change (is_digit_z z0) in H0.
  change (is_digit_z z1) in H1.
  change (is_digit_z z3) in H3.
  change (is_digit_z z4) in H4.
  change (is_digit_z z6) in H6.
  change (is_digit_z z7) in H7.
  change (is_digit_z z8) in H8.
  change (is_digit_z z9) in H9.
  unfold problem_124_spec.
  simpl.
  repeat split.
  - rewrite Hsep2. reflexivity.
  - rewrite Hsep5. reflexivity.
  - exists (Z.to_nat (month_z [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9])).
    exists (Z.to_nat (day_z [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9])).
    exists (Z.to_nat (year_z [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9])).
    repeat split.
    + unfold month_z.
      simpl.
      apply nat_of_2_digits_ascii_of_z; assumption.
    + unfold day_z.
      simpl.
      apply nat_of_2_digits_ascii_of_z; assumption.
    + unfold year_z.
      simpl.
      apply nat_of_4_digits_ascii_of_z; assumption.
    + replace 1%nat with (Z.to_nat 1) by reflexivity.
      apply Z2Nat.inj_le; lia.
    + replace 12%nat with (Z.to_nat 12) by reflexivity.
      apply Z2Nat.inj_le; lia.
    + replace 1%nat with (Z.to_nat 1) by reflexivity.
      apply Z2Nat.inj_le; lia.
    + apply Nat2Z.inj_le.
      rewrite Z2Nat.id by lia.
      rewrite days_in_month_z_nat by exact Hmonth.
      apply Hday.
Qed.

Lemma problem_124_spec_to_valid_date_z : forall l,
  ascii_range_z l ->
  problem_124_spec (string_of_list_z l) ->
  valid_date_z l.
Proof.
  intros l Hrange Hspec.
  unfold problem_124_spec in Hspec.
  rewrite list_ascii_of_string_string_of_list_z in Hspec.
  destruct_date_list l.
  destruct Hspec as [Hsep2 [Hsep5 [m [d [y [Hm [Hd [Hy [Hmonth Hday]]]]]]]]].
  assert (Hz2 : z2 = 45).
  {
    apply ascii_of_z_inj_const_124 with (n := 45%nat); try lia.
    - pose proof (Hrange 2 ltac:(change (0 <= 2 < 10); lia)) as Hz2range. exact Hz2range.
    - exact Hsep2.
  }
  assert (Hz5 : z5 = 45).
  {
    apply ascii_of_z_inj_const_124 with (n := 45%nat); try lia.
    - pose proof (Hrange 5 ltac:(change (0 <= 5 < 10); lia)) as Hz5range. exact Hz5range.
    - exact Hsep5.
  }
  unfold nat_of_2_digits in Hm.
  unfold nat_of_2_digits in Hd.
  unfold nat_of_4_digits in Hy.
  destruct (nat_of_digit (ascii_of_z z0)) as [d0|] eqn:Hz0; try discriminate.
  destruct (nat_of_digit (ascii_of_z z1)) as [d1|] eqn:Hz1; try discriminate.
  destruct (nat_of_digit (ascii_of_z z3)) as [d3|] eqn:Hz3; try discriminate.
  destruct (nat_of_digit (ascii_of_z z4)) as [d4|] eqn:Hz4; try discriminate.
  destruct (nat_of_digit (ascii_of_z z6)) as [d6|] eqn:Hz6; try discriminate.
  destruct (nat_of_digit (ascii_of_z z7)) as [d7|] eqn:Hz7; try discriminate.
  destruct (nat_of_digit (ascii_of_z z8)) as [d8|] eqn:Hz8; try discriminate.
  destruct (nat_of_digit (ascii_of_z z9)) as [d9|] eqn:Hz9; try discriminate.
  inversion Hm; subst m; clear Hm.
  inversion Hd; subst d; clear Hd.
  inversion Hy; subst y; clear Hy.
  change (1 <= 10 * d0 + d1 <= 12)%nat in Hmonth.
  change (1 <= 10 * d3 + d4 <= days_in_month (10 * d0 + d1))%nat in Hday.
  pose proof (Hrange 0 ltac:(change (0 <= 0 < 10); lia)) as Hr0.
  pose proof (Hrange 1 ltac:(change (0 <= 1 < 10); lia)) as Hr1.
  pose proof (Hrange 3 ltac:(change (0 <= 3 < 10); lia)) as Hr3.
  pose proof (Hrange 4 ltac:(change (0 <= 4 < 10); lia)) as Hr4.
  pose proof (Hrange 6 ltac:(change (0 <= 6 < 10); lia)) as Hr6.
  pose proof (Hrange 7 ltac:(change (0 <= 7 < 10); lia)) as Hr7.
  pose proof (Hrange 8 ltac:(change (0 <= 8 < 10); lia)) as Hr8.
  pose proof (Hrange 9 ltac:(change (0 <= 9 < 10); lia)) as Hr9.
  change (0 <= z0 < 256) in Hr0.
  change (0 <= z1 < 256) in Hr1.
  change (0 <= z3 < 256) in Hr3.
  change (0 <= z4 < 256) in Hr4.
  change (0 <= z6 < 256) in Hr6.
  change (0 <= z7 < 256) in Hr7.
  change (0 <= z8 < 256) in Hr8.
  change (0 <= z9 < 256) in Hr9.
  pose proof (nat_of_digit_ascii_of_z_inv z0 d0 Hr0 Hz0) as [Hz0d Hz0v].
  pose proof (nat_of_digit_ascii_of_z_inv z1 d1 Hr1 Hz1) as [Hz1d Hz1v].
  pose proof (nat_of_digit_ascii_of_z_inv z3 d3 Hr3 Hz3) as [Hz3d Hz3v].
  pose proof (nat_of_digit_ascii_of_z_inv z4 d4 Hr4 Hz4) as [Hz4d Hz4v].
  pose proof (nat_of_digit_ascii_of_z_inv z6 d6 Hr6 Hz6) as [Hz6d Hz6v].
  pose proof (nat_of_digit_ascii_of_z_inv z7 d7 Hr7 Hz7) as [Hz7d Hz7v].
  pose proof (nat_of_digit_ascii_of_z_inv z8 d8 Hr8 Hz8) as [Hz8d Hz8v].
  pose proof (nat_of_digit_ascii_of_z_inv z9 d9 Hr9 Hz9) as [Hz9d Hz9v].
  assert (HmonthZ : 1 <= Z.of_nat (10 * d0 + d1) <= 12) by lia.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul in HmonthZ.
  rewrite Hz0v, Hz1v in HmonthZ.
  repeat rewrite Z2Nat.id in HmonthZ by (unfold is_digit_z in *; lia).
  change (1 <= 10 * (z0 - 48) + (z1 - 48) <= 12) in HmonthZ.
  assert (HdayZ : 1 <= Z.of_nat (10 * d3 + d4) <=
                    Z.of_nat (days_in_month (10 * d0 + d1))) by lia.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul in HdayZ.
  rewrite Hz3v, Hz4v in HdayZ.
  repeat rewrite Z2Nat.id in HdayZ by (unfold is_digit_z in *; lia).
  change (1 <= 10 * (z3 - 48) + (z4 - 48) <=
          Z.of_nat (days_in_month (10 * d0 + d1))) in HdayZ.
  replace (Z.of_nat (days_in_month (10 * d0 + d1)))
    with (days_in_month_z ((z0 - 48) * 10 + (z1 - 48))) in HdayZ.
  2:{
    rewrite Hz0v, Hz1v.
    replace (10 * Z.to_nat (z0 - 48) + Z.to_nat (z1 - 48))%nat
      with (Z.to_nat ((z0 - 48) * 10 + (z1 - 48))).
    rewrite days_in_month_z_nat by lia.
    reflexivity.
    rewrite Z2Nat.inj_add by (unfold is_digit_z in *; lia).
    rewrite Z2Nat.inj_mul by (unfold is_digit_z in *; lia).
    lia.
  }
  unfold valid_date_z, date_format_z, month_z, day_z.
  simpl.
  change (Znth 0 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z0 in *.
  change (Znth 1 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z1 in *.
  change (Znth 2 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z2 in *.
  change (Znth 3 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z3 in *.
  change (Znth 4 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z4 in *.
  change (Znth 5 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z5 in *.
  change (Znth 6 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z6 in *.
  change (Znth 7 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z7 in *.
  change (Znth 8 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z8 in *.
  change (Znth 9 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z9 in *.
  repeat split;
    repeat rewrite Znth_cons by lia;
    unfold is_digit_z in *; subst; try lia; try reflexivity.
Qed.

Lemma problem_124_spec_z_true : forall l,
  ascii_range_z l ->
  valid_date_z l ->
  problem_124_spec_z l 1.
Proof.
  intros l Hrange H.
  unfold problem_124_spec_z.
  split; intros _.
  - apply valid_date_z_to_problem_124_spec; assumption.
  - reflexivity.
Qed.

Lemma problem_124_spec_z_false : forall l,
  ascii_range_z l ->
  ~ valid_date_z l ->
  problem_124_spec_z l 0.
Proof.
  intros l Hrange H.
  unfold problem_124_spec_z.
  split; intros Hbad.
  - lia.
  - exfalso.
    apply H.
    apply problem_124_spec_to_valid_date_z; assumption.
Qed.
