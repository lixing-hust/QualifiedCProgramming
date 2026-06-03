Load "../spec/156".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
From SimpleC.EE Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_156_pre_z (number : Z) : Prop :=
  problem_156_pre (Z.to_nat number).

Definition problem_156_spec_z (number : Z) (output : list Z) : Prop :=
  problem_156_spec (Z.to_nat number) (string_of_list_z output).

Definition roman_digit_list_z (one ten five digit : Z) : list Z :=
  match digit with
  | 0 => []
  | 1 => [one]
  | 2 => [one; one]
  | 3 => [one; one; one]
  | 4 => [one; five]
  | 5 => [five]
  | 6 => [five; one]
  | 7 => [five; one; one]
  | 8 => [five; one; one; one]
  | 9 => [one; ten]
  | _ => []
  end.

Definition roman_digit_z
  (one ten five digit : Z) (chunk : list Z) : Prop :=
  chunk = roman_digit_list_z one ten five digit.

Definition roman_thousand_list_z (number : Z) : list Z :=
  if Z.eqb number 1000 then [109] else [].

Definition roman_thousand_z (number : Z) (out_l : list Z) : Prop :=
  out_l = roman_thousand_list_z number.

Definition roman_prefix1_list_z (number : Z) : list Z :=
  roman_thousand_list_z number ++
  roman_digit_list_z 99 109 100 ((number / 100) mod 10).

Definition roman_prefix1_z (number : Z) (out_l : list Z) : Prop :=
  out_l = roman_prefix1_list_z number.

Definition roman_prefix2_list_z (number : Z) : list Z :=
  roman_prefix1_list_z number ++
  roman_digit_list_z 120 99 108 ((number / 10) mod 10).

Definition roman_prefix2_z (number : Z) (out_l : list Z) : Prop :=
  out_l = roman_prefix2_list_z number.

Definition roman_output_list_z (number : Z) : list Z :=
  roman_prefix2_list_z number ++
  roman_digit_list_z 105 120 118 (number mod 10).

Definition roman_output_z (number : Z) (out_l : list Z) : Prop :=
  out_l = roman_output_list_z number.

Lemma roman_digit_z_length_bound : forall one ten five digit chunk,
  0 <= digit <= 9 ->
  roman_digit_z one ten five digit chunk ->
  0 <= Zlength chunk <= 4.
Proof.
  intros one ten five digit chunk Hdig Hchunk.
  unfold roman_digit_z, roman_digit_list_z in Hchunk.
  subst chunk.
  assert ((Z.to_nat digit <= 9)%nat) by lia.
  rewrite <- (Z2Nat.id digit) by lia.
  destruct (Z.to_nat digit) as
    [|[|[|[|[|[|[|[|[|[|d]]]]]]]]]]; cbn; lia.
Qed.

Lemma roman_output_z_length_bound : forall number out_l,
  1 <= number <= 1000 ->
  roman_output_z number out_l ->
  0 <= Zlength out_l < 64.
Proof.
  intros number out_l Hnum Hout.
  unfold roman_output_z, roman_output_list_z, roman_prefix2_list_z,
    roman_prefix1_list_z, roman_thousand_list_z in Hout.
  subst out_l.
  repeat rewrite Zlength_app.
  pose proof (roman_digit_z_length_bound 99 109 100
    ((number / 100) mod 10)
    (roman_digit_list_z 99 109 100 ((number / 100) mod 10))
    ltac:(pose proof (Z.mod_pos_bound (number / 100) 10 ltac:(lia)); lia)
    ltac:(reflexivity)).
  pose proof (roman_digit_z_length_bound 120 99 108
    ((number / 10) mod 10)
    (roman_digit_list_z 120 99 108 ((number / 10) mod 10))
    ltac:(pose proof (Z.mod_pos_bound (number / 10) 10 ltac:(lia)); lia)
    ltac:(reflexivity)).
  pose proof (roman_digit_z_length_bound 105 120 118
    (number mod 10)
    (roman_digit_list_z 105 120 118 (number mod 10))
    ltac:(pose proof (Z.mod_pos_bound number 10 ltac:(lia)); lia)
    ltac:(reflexivity)).
  assert (0 <= Zlength (if Z.eqb number 1000 then [109] else []) <= 1).
  { destruct (Z.eqb number 1000); cbn; lia. }
  lia.
Qed.

Lemma roman_thousand_z_length_bound : forall number out_l,
  1 <= number <= 1000 ->
  roman_thousand_z number out_l ->
  0 <= Zlength out_l <= 1.
Proof.
  intros number out_l _ Hout.
  unfold roman_thousand_z, roman_thousand_list_z in Hout.
  subst out_l.
  destruct (Z.eqb number 1000); cbn; lia.
Qed.

Lemma roman_prefix1_z_length_bound : forall number out_l,
  1 <= number <= 1000 ->
  roman_prefix1_z number out_l ->
  0 <= Zlength out_l <= 5.
Proof.
  intros number out_l Hnum Hout.
  unfold roman_prefix1_z, roman_prefix1_list_z in Hout.
  subst out_l.
  rewrite Zlength_app.
  pose proof (roman_thousand_z_length_bound number
    (roman_thousand_list_z number) Hnum ltac:(reflexivity)).
  pose proof (roman_digit_z_length_bound 99 109 100
    ((number / 100) mod 10)
    (roman_digit_list_z 99 109 100 ((number / 100) mod 10))
    ltac:(pose proof (Z.mod_pos_bound (number / 100) 10 ltac:(lia)); lia)
    ltac:(reflexivity)).
  lia.
Qed.

Lemma roman_prefix2_z_length_bound : forall number out_l,
  1 <= number <= 1000 ->
  roman_prefix2_z number out_l ->
  0 <= Zlength out_l <= 9.
Proof.
  intros number out_l Hnum Hout.
  unfold roman_prefix2_z, roman_prefix2_list_z in Hout.
  subst out_l.
  rewrite Zlength_app.
  pose proof (roman_prefix1_z_length_bound number
    (roman_prefix1_list_z number) Hnum ltac:(reflexivity)).
  pose proof (roman_digit_z_length_bound 120 99 108
    ((number / 10) mod 10)
    (roman_digit_list_z 120 99 108 ((number / 10) mod 10))
    ltac:(pose proof (Z.mod_pos_bound (number / 10) 10 ltac:(lia)); lia)
    ltac:(reflexivity)).
  lia.
Qed.

Lemma roman_prefix1_step : forall number chunk,
  0 <= number ->
  roman_digit_z 99 109 100 ((number / 100) mod 10) chunk ->
  roman_prefix1_list_z number = roman_thousand_list_z number ++ chunk.
Proof.
  intros number chunk Hnum Hchunk.
  unfold roman_digit_z in Hchunk.
  unfold roman_prefix1_list_z.
  subst chunk; reflexivity.
Qed.

Lemma roman_prefix2_step : forall number chunk,
  0 <= number ->
  roman_digit_z 120 99 108 ((number / 10) mod 10) chunk ->
  roman_prefix2_list_z number = roman_prefix1_list_z number ++ chunk.
Proof.
  intros number chunk Hnum Hchunk.
  unfold roman_digit_z in Hchunk.
  unfold roman_prefix2_list_z.
  subst chunk; reflexivity.
Qed.

Lemma roman_output_step : forall number chunk,
  roman_digit_z 105 120 118 (number mod 10) chunk ->
  roman_output_list_z number = roman_prefix2_list_z number ++ chunk.
Proof.
  intros number chunk Hchunk.
  unfold roman_digit_z in Hchunk.
  unfold roman_output_list_z.
  subst chunk; reflexivity.
Qed.

Lemma ascii_of_z_of_ascii_156 : forall c,
  ascii_of_z (Z.of_nat (nat_of_ascii c)) = c.
Proof.
  intros [[] [] [] [] [] [] [] []]; reflexivity.
Qed.

Lemma string_of_list_ascii_app_156 : forall a b,
  string_of_list_ascii (a ++ b) =
  (string_of_list_ascii a ++ string_of_list_ascii b)%string.
Proof.
  induction a; simpl; intros; congruence.
Qed.

Lemma string_of_list_z_app_156 : forall a b,
  string_of_list_z (a ++ b) =
  (string_of_list_z a ++ string_of_list_z b)%string.
Proof.
  induction a; simpl; intros; congruence.
Qed.

Lemma string_append_assoc_156 : forall a b c,
  ((a ++ b) ++ c = a ++ (b ++ c))%string.
Proof.
  induction a; simpl; intros; congruence.
Qed.

Lemma roman_digit_spec_string : forall one ten five one_z ten_z five_z digit,
  0 <= digit <= 9 ->
  one_z = Z.of_nat (nat_of_ascii one) ->
  ten_z = Z.of_nat (nat_of_ascii ten) ->
  five_z = Z.of_nat (nat_of_ascii five) ->
  exists chars,
    roman_digit_spec one ten five (Z.to_nat digit) chars /\
    string_of_list_z (roman_digit_list_z one_z ten_z five_z digit) =
      string_of_list_ascii chars.
Proof.
  intros one ten five one_z ten_z five_z digit Hdig Hone Hten Hfive.
  subst one_z ten_z five_z.
  assert ((Z.to_nat digit <= 9)%nat) by lia.
  rewrite <- (Z2Nat.id digit) by lia.
  destruct (Z.to_nat digit) as
    [|[|[|[|[|[|[|[|[|[|d]]]]]]]]]]; try lia.
  - exists []; split; cbn; [left; split; reflexivity | reflexivity].
  - exists [one]; split; cbn; [right; left; split; reflexivity |].
    rewrite ascii_of_z_of_ascii_156. reflexivity.
  - exists [one; one]; split; cbn; [right; right; left; split; reflexivity |].
    repeat rewrite ascii_of_z_of_ascii_156. reflexivity.
  - exists [one; one; one]; split; cbn; [right; right; right; left; split; reflexivity |].
    repeat rewrite ascii_of_z_of_ascii_156. reflexivity.
  - exists [one; five]; split; cbn; [right; right; right; right; left; split; reflexivity |].
    repeat rewrite ascii_of_z_of_ascii_156. reflexivity.
  - exists [five]; split; cbn; [right; right; right; right; right; left; split; reflexivity |].
    repeat rewrite ascii_of_z_of_ascii_156. reflexivity.
  - exists [five; one]; split; cbn; [right; right; right; right; right; right; left; split; reflexivity |].
    repeat rewrite ascii_of_z_of_ascii_156. reflexivity.
  - exists [five; one; one]; split; cbn; [right; right; right; right; right; right; right; left; split; reflexivity |].
    repeat rewrite ascii_of_z_of_ascii_156. reflexivity.
  - exists [five; one; one; one]; split; cbn; [right; right; right; right; right; right; right; right; left; split; reflexivity |].
    repeat rewrite ascii_of_z_of_ascii_156. reflexivity.
  - exists [one; ten]; split; cbn; [right; right; right; right; right; right; right; right; right; split; reflexivity |].
    repeat rewrite ascii_of_z_of_ascii_156. reflexivity.
Qed.

Lemma decimal_decomp_156_nat : forall number,
  0 <= number ->
  Z.to_nat number =
    (1000 * Z.to_nat (number / 1000) +
     100 * Z.to_nat ((number / 100) mod 10) +
     10 * Z.to_nat ((number / 10) mod 10) +
     Z.to_nat (number mod 10))%nat.
Proof.
  intros number Hnumber.
  apply Nat2Z.inj.
  repeat rewrite Nat2Z.inj_add.
  repeat rewrite Nat2Z.inj_mul.
  repeat rewrite Z2Nat.id by
    (try apply Z.div_pos; try apply Z.mod_pos_bound; lia).
  assert (number = 10 * (number / 10) + number mod 10) as H0
    by (apply Z.div_mod; lia).
  assert (number / 10 =
    10 * (number / 100) + (number / 10) mod 10) as H1.
  { pose proof (Z.div_mod (number / 10) 10 ltac:(lia)) as H.
    replace ((number / 10) / 10) with (number / 100) in H
      by (rewrite Z.div_div by lia; reflexivity).
    exact H. }
  assert (number / 100 =
    10 * (number / 1000) + (number / 100) mod 10) as H2.
  { pose proof (Z.div_mod (number / 100) 10 ltac:(lia)) as H.
    replace ((number / 100) / 10) with (number / 1000) in H
      by (rewrite Z.div_div by lia; reflexivity).
    exact H. }
  lia.
Qed.

Lemma problem_156_spec_z_intro : forall number out_l,
  1 <= number <= 1000 ->
  roman_output_z number out_l ->
  problem_156_spec_z number out_l.
Proof.
  intros number out_l Hnum Hout.
  unfold problem_156_spec_z, problem_156_spec.
  unfold roman_output_z, roman_output_list_z, roman_prefix2_list_z,
    roman_prefix1_list_z, roman_thousand_list_z in Hout.
  subst out_l.
  split.
  - lia.
  - exists (Z.to_nat (number / 1000)).
  exists (Z.to_nat ((number / 100) mod 10)).
  exists (Z.to_nat ((number / 10) mod 10)).
  exists (Z.to_nat (number mod 10)).
  destruct (Z.eqb number 1000) eqn:Hthousand.
  + exists ["m"%char].
    assert (Hnum1000 : number = 1000) by
      (apply Z.eqb_eq; exact Hthousand).
    destruct (roman_digit_spec_string "c"%char "m"%char "d"%char
      99 109 100 ((number / 100) mod 10)
      ltac:(pose proof (Z.mod_pos_bound (number / 100) 10 ltac:(lia)); lia)
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [rc [Hrc Hrcs]].
    destruct (roman_digit_spec_string "x"%char "c"%char "l"%char
      120 99 108 ((number / 10) mod 10)
      ltac:(pose proof (Z.mod_pos_bound (number / 10) 10 ltac:(lia)); lia)
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [rx [Hrx Hrxs]].
    destruct (roman_digit_spec_string "i"%char "x"%char "v"%char
      105 120 118 (number mod 10)
      ltac:(pose proof (Z.mod_pos_bound number 10 ltac:(lia)); lia)
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [ri [Hri Hris]].
    exists rc, rx, ri.
    repeat split.
    * apply decimal_decomp_156_nat; lia.
    * rewrite Z2Nat.inj_div by lia. reflexivity.
    * rewrite Z2Nat.inj_mod by (try apply Z.div_pos; lia).
      rewrite Z2Nat.inj_div by lia.
      reflexivity.
    * rewrite Z2Nat.inj_mod by (try apply Z.div_pos; lia).
      rewrite Z2Nat.inj_div by lia.
      reflexivity.
    * rewrite Z2Nat.inj_mod by lia. reflexivity.
    * rewrite Hnum1000.
      left. split; reflexivity.
    * exact Hrc.
    * exact Hrx.
    * exact Hri.
    * repeat rewrite string_of_list_z_app_156.
      rewrite Hnum1000.
      rewrite Hnum1000 in Hrcs, Hrxs, Hris.
      cbn in Hrcs, Hrxs, Hris.
      cbn.
      repeat rewrite string_of_list_ascii_app_156.
      try rewrite <- Hrcs; try rewrite <- Hrxs; try rewrite <- Hris.
      reflexivity.
  + exists (@nil ascii).
    destruct (roman_digit_spec_string "c"%char "m"%char "d"%char
      99 109 100 ((number / 100) mod 10)
      ltac:(pose proof (Z.mod_pos_bound (number / 100) 10 ltac:(lia)); lia)
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [rc [Hrc Hrcs]].
    destruct (roman_digit_spec_string "x"%char "c"%char "l"%char
      120 99 108 ((number / 10) mod 10)
      ltac:(pose proof (Z.mod_pos_bound (number / 10) 10 ltac:(lia)); lia)
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [rx [Hrx Hrxs]].
    destruct (roman_digit_spec_string "i"%char "x"%char "v"%char
      105 120 118 (number mod 10)
      ltac:(pose proof (Z.mod_pos_bound number 10 ltac:(lia)); lia)
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [ri [Hri Hris]].
    exists rc, rx, ri.
    repeat split.
    * apply decimal_decomp_156_nat; lia.
    * rewrite Z2Nat.inj_div by lia. reflexivity.
    * rewrite Z2Nat.inj_mod by (try apply Z.div_pos; lia).
      rewrite Z2Nat.inj_div by lia.
      reflexivity.
    * rewrite Z2Nat.inj_mod by (try apply Z.div_pos; lia).
      rewrite Z2Nat.inj_div by lia.
      reflexivity.
    * rewrite Z2Nat.inj_mod by lia. reflexivity.
    * apply Z.eqb_neq in Hthousand.
      right.
      assert (number / 1000 = 0) by (apply Z.div_small; lia).
      split; [rewrite H; reflexivity|reflexivity].
    * exact Hrc.
    * exact Hrx.
    * exact Hri.
    * repeat rewrite string_of_list_z_app_156.
      cbn in Hrcs, Hrxs, Hris.
      repeat rewrite string_of_list_ascii_app_156.
      try rewrite <- Hrcs; try rewrite <- Hrxs; try rewrite <- Hris.
      cbn.
      repeat rewrite string_of_list_z_app_156.
      rewrite string_append_assoc_156.
      destruct (Z.eqb number 1000); reflexivity.
Qed.
