Load "../spec/18".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition problem_18_pre_z (input substring : list Z) : Prop :=
  problem_18_pre (string_of_list_z input) (string_of_list_z substring).

Definition problem_18_spec_z (input substring : list Z) (output : Z) : Prop :=
  0 <= output /\
  problem_18_spec
    (string_of_list_z input)
    (string_of_list_z substring)
    (Z.to_nat output).

Definition match_prefix_z (i j : Z) (input substring : list Z) : Prop :=
  forall k, 0 <= k < j ->
    Znth (i + k) input 0 = Znth k substring 0.

Definition mismatch_prefix_z (i j : Z) (input substring : list Z) : Prop :=
  exists k, 0 <= k < j /\
    Znth (i + k) input 0 <> Znth k substring 0.

Definition match_progress_z
  (i j ok : Z) (input substring : list Z) : Prop :=
  (ok = 1 -> match_prefix_z i j input substring) /\
  (ok = 0 -> mismatch_prefix_z i j input substring).

Fixpoint list_eq_zb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => Z.eqb x y && list_eq_zb xs ys
  | _, _ => false
  end.

Definition match_at_zb (i : Z) (input substring : list Z) : bool :=
  (Z.ltb 0 (Zlength substring)) &&
  (Z.leb (i + Zlength substring) (Zlength input)) &&
  list_eq_zb (sublist i (i + Zlength substring) input) substring.

Fixpoint count_matches_upto_nat
  (fuel : nat) (input substring : list Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      count_matches_upto_nat fuel' input substring +
      if match_at_zb (Z.of_nat fuel') input substring then 1 else 0
  end.

Definition count_matches_upto
  (i : Z) (input substring : list Z) : Z :=
  count_matches_upto_nat (Z.to_nat i) input substring.

Lemma count_matches_upto_zero : forall input substring,
  count_matches_upto 0 input substring = 0.
Proof. reflexivity. Qed.

Lemma count_matches_upto_nonneg : forall i input substring,
  0 <= count_matches_upto i input substring.
Proof.
  intros i input substring.
  unfold count_matches_upto.
  induction (Z.to_nat i) as [| fuel IH]; simpl; [lia |].
  destruct (match_at_zb (Z.of_nat fuel) input substring); lia.
Qed.

Lemma count_matches_upto_le : forall i input substring,
  0 <= i ->
  count_matches_upto i input substring <= i.
Proof.
  intros i input substring Hi.
  unfold count_matches_upto.
  remember (Z.to_nat i) as fuel.
  assert (Hfuel : Z.of_nat fuel = i) by lia.
  rewrite <- Hfuel.
  clear i Hi Hfuel Heqfuel.
  induction fuel as [| fuel IH]; simpl.
  - lia.
  - destruct (match_at_zb (Z.of_nat fuel) input substring); lia.
Qed.

Lemma count_matches_upto_step : forall i input substring,
  0 <= i ->
  count_matches_upto (i + 1) input substring =
    count_matches_upto i input substring +
    if match_at_zb i input substring then 1 else 0.
Proof.
  intros i input substring Hi.
  unfold count_matches_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma count_matches_upto_step_hit : forall i input substring,
  0 <= i ->
  match_at_zb i input substring = true ->
  count_matches_upto (i + 1) input substring =
    count_matches_upto i input substring + 1.
Proof.
  intros i input substring Hi Hhit.
  rewrite count_matches_upto_step by lia.
  rewrite Hhit.
  reflexivity.
Qed.

Lemma count_matches_upto_step_miss : forall i input substring,
  0 <= i ->
  match_at_zb i input substring = false ->
  count_matches_upto (i + 1) input substring =
    count_matches_upto i input substring.
Proof.
  intros i input substring Hi Hmiss.
  rewrite count_matches_upto_step by lia.
  rewrite Hmiss.
  lia.
Qed.

Lemma match_progress_init : forall i input substring,
  match_progress_z i 0 1 input substring.
Proof.
  unfold match_progress_z, match_prefix_z, mismatch_prefix_z.
  intros.
  split.
  - intros _ k Hk. lia.
  - intros H; discriminate.
Qed.

Lemma match_progress_step_same : forall i j input substring,
  0 <= j ->
  match_progress_z i j 1 input substring ->
  Znth (i + j) input 0 = Znth j substring 0 ->
  match_progress_z i (j + 1) 1 input substring.
Proof.
  unfold match_progress_z, match_prefix_z, mismatch_prefix_z.
  intros i j input substring Hj [Hprefix _] Heq.
  split.
  - intros _ k Hk.
    destruct (Z.eq_dec k j) as [-> | Hne].
    + exact Heq.
    + apply Hprefix; lia.
  - intros H; discriminate.
Qed.

Lemma match_progress_step_keep_mismatch : forall i j input substring,
  0 <= j ->
  match_progress_z i j 0 input substring ->
  match_progress_z i (j + 1) 0 input substring.
Proof.
  unfold match_progress_z, match_prefix_z, mismatch_prefix_z.
  intros i j input substring Hj [_ Hmis].
  split.
  - intros H; discriminate.
  - intros _. destruct (Hmis eq_refl) as [k [Hk Hneq]].
    exists k. split; [lia | exact Hneq].
Qed.

Lemma match_progress_step_new_mismatch : forall i j input substring,
  0 <= j ->
  Znth (i + j) input 0 <> Znth j substring 0 ->
  match_progress_z i (j + 1) 0 input substring.
Proof.
  unfold match_progress_z, match_prefix_z, mismatch_prefix_z.
  intros i j input substring Hj Hneq.
  split.
  - intros H; discriminate.
  - intros _. exists j. split; [lia | exact Hneq].
Qed.

Lemma list_eq_zb_true_iff : forall l1 l2,
  list_eq_zb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [| x xs IH]; destruct l2 as [| y ys]; simpl; split; intros H;
    try reflexivity; try discriminate.
  - apply andb_true_iff in H as [Hxy Hxs].
    apply Z.eqb_eq in Hxy.
    apply IH in Hxs.
    congruence.
  - inversion H; subst.
    rewrite Z.eqb_refl.
    rewrite (proj2 (IH ys)); reflexivity.
Qed.

Lemma list_eq_zb_false_neq : forall l1 l2,
  l1 <> l2 ->
  list_eq_zb l1 l2 = false.
Proof.
  intros l1 l2 Hneq.
  destruct (list_eq_zb l1 l2) eqn:H; [| reflexivity].
  apply list_eq_zb_true_iff in H.
  contradiction.
Qed.

Lemma prefix_sublist_eq : forall i j input substring,
  0 <= i ->
  0 <= j ->
  i + j <= Zlength input ->
  j <= Zlength substring ->
  match_prefix_z i j input substring ->
  sublist i (i + j) input = sublist 0 j substring.
Proof.
  intros i j input substring Hi Hj Hin Hsub Hprefix.
  apply (proj2 (@list_eq_ext Z
    0
    (sublist i (i + j) input)
    (sublist 0 j substring))).
  split.
  - rewrite !Zlength_sublist by lia. lia.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by lia.
    rewrite !Znth_sublist by lia.
    replace (k + i) with (i + k) by lia.
    replace (k + 0) with k by lia.
    apply Hprefix.
    lia.
Qed.

Lemma mismatch_sublist_neq : forall i j input substring,
  0 <= i ->
  0 <= j ->
  i + j <= Zlength input ->
  j <= Zlength substring ->
  mismatch_prefix_z i j input substring ->
  sublist i (i + j) input <> sublist 0 j substring.
Proof.
  intros i j input substring Hi Hj Hin Hsub [k [Hk Hneq]] Heq.
  assert (Hklen : 0 <= k < Zlength (sublist i (i + j) input)).
  { rewrite Zlength_sublist by lia. lia. }
  pose proof (proj1 (@list_eq_ext Z 0
    (sublist i (i + j) input)
    (sublist 0 j substring)) Heq) as [_ Hnth_all].
  specialize (Hnth_all k Hklen) as Hnth.
  rewrite (Znth_sublist i k (i + j) input) in Hnth by lia.
  rewrite (Znth_sublist 0 k j substring) in Hnth by lia.
  replace (k + 0) with k in Hnth by lia.
  replace (k + i) with (i + k) in Hnth by lia.
  contradiction.
Qed.

Lemma match_progress_true_at_end : forall i input substring,
  0 <= i ->
  0 < Zlength substring ->
  i + Zlength substring <= Zlength input ->
  match_progress_z i (Zlength substring) 1 input substring ->
  match_at_zb i input substring = true.
Proof.
  intros i input substring Hi Hsub_pos Hin [Hprefix _].
  unfold match_at_zb.
  rewrite (proj2 (Z.ltb_lt 0 (Zlength substring))) by exact Hsub_pos.
  rewrite (proj2 (Z.leb_le (i + Zlength substring) (Zlength input))) by exact Hin.
  rewrite andb_true_r.
  apply list_eq_zb_true_iff.
  replace substring with (sublist 0 (Zlength substring) substring) at 2.
  - apply prefix_sublist_eq; try lia.
    apply Hprefix. reflexivity.
  - rewrite sublist_self by reflexivity.
    reflexivity.
Qed.

Lemma match_progress_false_at_end : forall i input substring,
  0 <= i ->
  0 < Zlength substring ->
  i + Zlength substring <= Zlength input ->
  match_progress_z i (Zlength substring) 0 input substring ->
  match_at_zb i input substring = false.
Proof.
  intros i input substring Hi Hsub_pos Hin [_ Hmis].
  unfold match_at_zb.
  rewrite (proj2 (Z.ltb_lt 0 (Zlength substring))) by exact Hsub_pos.
  rewrite (proj2 (Z.leb_le (i + Zlength substring) (Zlength input))) by exact Hin.
  rewrite andb_true_r.
  apply list_eq_zb_false_neq.
  replace substring with (sublist 0 (Zlength substring) substring) at 2.
  - apply mismatch_sublist_neq; try lia.
    apply Hmis. reflexivity.
  - rewrite sublist_self by reflexivity.
    reflexivity.
Qed.

Lemma match_at_zb_false_empty_substring : forall input substring i,
  Zlength substring = 0 ->
  match_at_zb i input substring = false.
Proof.
  intros input substring i Hlen.
  unfold match_at_zb.
  rewrite Hlen.
  reflexivity.
Qed.

Lemma match_at_zb_false_too_long : forall input substring i,
  Zlength input < Zlength substring ->
  0 <= i ->
  match_at_zb i input substring = false.
Proof.
  intros input substring i Hlt Hi.
  unfold match_at_zb.
  assert (Hgt : Zlength input < i + Zlength substring) by lia.
  pose proof (proj2 (Z.leb_gt (i + Zlength substring) (Zlength input)) Hgt) as Hleb.
  rewrite Hleb.
  destruct ((0 <? Zlength substring)%Z); reflexivity.
Qed.

Lemma count_matches_upto_zero_output : forall i input substring,
  i = 0 ->
  count_matches_upto i input substring = 0.
Proof. intros; subst; reflexivity. Qed.

Lemma problem_18_spec_z_zero_when_no_matches : forall input substring,
  (forall i,
    (i + String.length (string_of_list_z substring) <=
     String.length (string_of_list_z input))%nat ->
    ~ match_at i (string_of_list_z input) (string_of_list_z substring)) ->
  problem_18_spec_z input substring 0.
Proof.
  intros input substring Hnone.
  unfold problem_18_spec_z.
  split; [lia |].
  unfold problem_18_spec.
  exists nil.
  split; [constructor |].
  split.
  - intros idx Hin. contradiction.
  - split.
    + intros idx Hbound Hmatch.
      exfalso.
      apply (Hnone idx Hbound Hmatch).
    + reflexivity.
Qed.

Lemma problem_18_spec_z_zero_empty_substring : forall input substring,
  Zlength substring = 0 ->
  problem_18_spec_z input substring 0.
Proof.
  intros input substring Hlen.
  apply problem_18_spec_z_zero_when_no_matches.
  intros i _ Hmatch.
  unfold match_at in Hmatch.
  destruct Hmatch as [Hpos _].
  rewrite string_of_list_z_length in Hpos.
  rewrite Zlength_correct in Hlen.
  lia.
Qed.

Lemma problem_18_spec_z_zero_empty_input : forall input substring,
  Zlength input = 0 ->
  problem_18_spec_z input substring 0.
Proof.
  intros input substring Hlen.
  apply problem_18_spec_z_zero_when_no_matches.
  intros i Hbound Hmatch.
  unfold match_at in Hmatch.
  destruct Hmatch as [Hpos [_ _]].
  rewrite !string_of_list_z_length in Hbound, Hpos.
  rewrite Zlength_correct in Hlen.
  assert (String.length (string_of_list_z input) = 0%nat).
  { rewrite string_of_list_z_length. lia. }
  rewrite H in Hbound.
  lia.
Qed.

Lemma problem_18_spec_z_zero_too_long : forall input substring,
  Zlength input < Zlength substring ->
  problem_18_spec_z input substring 0.
Proof.
  intros input substring Hlt.
  apply problem_18_spec_z_zero_when_no_matches.
  intros i Hbound _.
  rewrite !string_of_list_z_length in Hbound.
  rewrite !Zlength_correct in Hlt.
  lia.
Qed.

Fixpoint matching_indices_nat
  (fuel : nat) (input substring : list Z) : list nat :=
  match fuel with
  | O => nil
  | S fuel' =>
      if match_at_zb (Z.of_nat fuel') input substring
      then fuel' :: matching_indices_nat fuel' input substring
      else matching_indices_nat fuel' input substring
  end.

Lemma matching_indices_in_iff : forall fuel input substring idx,
  In idx (matching_indices_nat fuel input substring) <->
  (idx < fuel)%nat /\
  match_at_zb (Z.of_nat idx) input substring = true.
Proof.
  induction fuel as [| fuel IH]; intros input substring idx; simpl.
  - split; intros H.
    + contradiction.
    + lia.
  - destruct (match_at_zb (Z.of_nat fuel) input substring) eqn:Hfuel.
    + simpl.
      rewrite IH.
      split.
      * intros [-> | [Hlt Hhit]].
        -- split; [lia | exact Hfuel].
        -- split; [lia | exact Hhit].
      * intros [Hlt Hhit].
        destruct (Nat.eq_dec idx fuel) as [-> | Hne].
        -- left. reflexivity.
        -- right. split; [lia | exact Hhit].
    + rewrite IH.
      split.
      * intros [Hlt Hhit].
        split; [lia | exact Hhit].
      * intros [Hlt Hhit].
        destruct (Nat.eq_dec idx fuel) as [-> | Hne].
        -- rewrite Hhit in Hfuel. discriminate.
        -- split; [lia | exact Hhit].
Qed.

Lemma matching_indices_NoDup : forall fuel input substring,
  NoDup (matching_indices_nat fuel input substring).
Proof.
  induction fuel as [| fuel IH]; intros input substring; simpl.
  - constructor.
  - destruct (match_at_zb (Z.of_nat fuel) input substring) eqn:Hfuel.
    + constructor.
      * rewrite matching_indices_in_iff.
        intros [Hlt _]. lia.
      * apply IH.
    + apply IH.
Qed.

Lemma matching_indices_length_count : forall fuel input substring,
  Z.of_nat (List.length (matching_indices_nat fuel input substring)) =
  count_matches_upto_nat fuel input substring.
Proof.
  induction fuel as [| fuel IH]; intros input substring; cbn [matching_indices_nat count_matches_upto_nat].
  - reflexivity.
  - destruct (match_at_zb (Z.of_nat fuel) input substring); cbn [List.length];
      rewrite ?Nat2Z.inj_succ; rewrite (IH input substring); lia.
Qed.

Lemma match_at_zb_sound_match_at : forall input substring z,
  0 <= z ->
  match_at_zb z input substring = true ->
  match_at (Z.to_nat z) (string_of_list_z input) (string_of_list_z substring).
Proof.
  intros input substring z Hz Hmatch.
  unfold match_at_zb in Hmatch.
  apply andb_true_iff in Hmatch as [Hab Hlist].
  apply andb_true_iff in Hab as [Hsub_pos Hbound].
  apply Z.ltb_lt in Hsub_pos.
  apply Z.leb_le in Hbound.
  apply list_eq_zb_true_iff in Hlist.
  unfold match_at.
  repeat split.
  - rewrite string_of_list_z_length.
    rewrite Zlength_correct in Hsub_pos.
    lia.
  - rewrite !string_of_list_z_length.
    rewrite !Zlength_correct in Hbound.
    lia.
  - intros j Hj.
    assert (Hget_input :
      String.get (Z.to_nat z + j) (string_of_list_z input) =
      Some (ascii_of_z (Znth (z + Z.of_nat j) input 0))).
    {
      replace (Z.to_nat z + j)%nat with (Z.to_nat (z + Z.of_nat j)) by lia.
      apply string_get_string_of_list_z_z.
      rewrite string_of_list_z_length in Hj.
      apply Nat2Z.inj_lt in Hj.
      rewrite <- Zlength_correct in Hj.
      lia.
    }
    assert (Hget_sub :
      String.get j (string_of_list_z substring) =
      Some (ascii_of_z (Znth (Z.of_nat j) substring 0))).
    {
      rewrite <- (Nat2Z.id j) at 1.
      apply string_get_string_of_list_z_z.
      rewrite string_of_list_z_length in Hj.
      apply Nat2Z.inj_lt in Hj.
      rewrite <- Zlength_correct in Hj.
      lia.
    }
    rewrite Hget_input, Hget_sub.
    f_equal.
    assert (Hjz : 0 <= Z.of_nat j < Zlength substring).
    {
      rewrite string_of_list_z_length in Hj.
      apply Nat2Z.inj_lt in Hj.
      rewrite <- Zlength_correct in Hj.
      lia.
    }
    assert (Hj_sublist :
      0 <= Z.of_nat j <
      Zlength (sublist z (z + Zlength substring) input)).
    {
      rewrite Zlength_sublist by lia.
      lia.
    }
    pose proof (proj1 (@list_eq_ext Z 0
      (sublist z (z + Zlength substring) input)
      substring) Hlist) as [_ Hall].
    specialize (Hall (Z.of_nat j) Hj_sublist) as Hnth.
    rewrite (Znth_sublist z (Z.of_nat j) (z + Zlength substring) input) in Hnth by lia.
    replace (Z.of_nat j + z) with (z + Z.of_nat j) in Hnth by lia.
    exact (f_equal ascii_of_z Hnth).
Qed.

Lemma ascii_of_z_inj_18 : forall x y,
  0 <= x < 256 ->
  0 <= y < 256 ->
  ascii_of_z x = ascii_of_z y ->
  x = y.
Proof.
  intros x y Hx Hy H.
  apply f_equal with (f := nat_of_ascii) in H.
  rewrite !nat_of_ascii_ascii_of_z in H by assumption.
  lia.
Qed.

Lemma match_at_complete_match_at_zb : forall input substring idx,
  ascii_range_z input ->
  ascii_range_z substring ->
  match_at idx (string_of_list_z input) (string_of_list_z substring) ->
  match_at_zb (Z.of_nat idx) input substring = true.
Proof.
  intros input substring idx Hrange_input Hrange_sub Hmatch.
  unfold match_at in Hmatch.
  destruct Hmatch as [Hsub_pos [Hbound Hchars]].
  assert (Hbound_z : Z.of_nat idx + Zlength substring <= Zlength input).
  {
    rewrite !string_of_list_z_length in Hbound.
    apply Nat2Z.inj_le in Hbound.
    rewrite Nat2Z.inj_add in Hbound.
    rewrite <- !Zlength_correct in Hbound.
    exact Hbound.
  }
  pose proof (Zlength_nonneg substring) as Hsub_nonneg.
  unfold match_at_zb.
  rewrite (proj2 (Z.ltb_lt 0 (Zlength substring))).
  2:{ rewrite Zlength_correct, <- string_of_list_z_length. lia. }
  rewrite (proj2 (Z.leb_le (Z.of_nat idx + Zlength substring) (Zlength input))).
  2:{ rewrite !Zlength_correct, <- !string_of_list_z_length. lia. }
  simpl.
  apply list_eq_zb_true_iff.
  apply (proj2 (@list_eq_ext Z 0
    (sublist (Z.of_nat idx) (Z.of_nat idx + Zlength substring) input)
    substring)).
  split.
  - rewrite Zlength_sublist by
      (rewrite !Zlength_correct, <- !string_of_list_z_length; lia).
    lia.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by lia.
    rewrite Znth_sublist by lia.
    replace (k + Z.of_nat idx) with (Z.of_nat idx + k) by lia.
    assert (Hj : (Z.to_nat k < String.length (string_of_list_z substring))%nat).
    {
      rewrite string_of_list_z_length.
      apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct.
      lia.
    }
    specialize (Hchars (Z.to_nat k) Hj).
    assert (Hget_input :
      String.get (idx + Z.to_nat k) (string_of_list_z input) =
      Some (ascii_of_z (Znth (Z.of_nat idx + k) input 0))).
    {
      replace (idx + Z.to_nat k)%nat with (Z.to_nat (Z.of_nat idx + k)) by lia.
      apply string_get_string_of_list_z_z.
      lia.
    }
    assert (Hget_sub :
      String.get (Z.to_nat k) (string_of_list_z substring) =
      Some (ascii_of_z (Znth k substring 0))).
    {
      apply string_get_string_of_list_z_z.
      lia.
    }
    rewrite Hget_input, Hget_sub in Hchars.
    injection Hchars as Hascii.
    apply ascii_of_z_inj_18; try assumption.
    + apply Hrange_input.
      rewrite Zlength_correct, <- string_of_list_z_length.
      lia.
    + apply Hrange_sub.
      rewrite Zlength_correct, <- string_of_list_z_length.
      lia.
Qed.

Lemma problem_18_spec_z_count_matches_full : forall input substring,
  ascii_range_z input ->
  ascii_range_z substring ->
  0 < Zlength substring ->
  Zlength substring <= Zlength input ->
  problem_18_spec_z input substring
    (count_matches_upto (Zlength input - Zlength substring + 1) input substring).
Proof.
  intros input substring Hrange_input Hrange_sub Hsub_pos Hlen.
  set (fuel_z := Zlength input - Zlength substring + 1).
  set (indices := matching_indices_nat (Z.to_nat fuel_z) input substring).
  unfold problem_18_spec_z.
  split.
  - apply count_matches_upto_nonneg.
  - unfold problem_18_spec.
    exists indices.
    split.
    + subst indices. apply matching_indices_NoDup.
    + split.
      * subst indices.
        intros idx Hin.
        apply matching_indices_in_iff in Hin as [Hidx Hhit].
        replace idx with (Z.to_nat (Z.of_nat idx)) by lia.
        apply match_at_zb_sound_match_at; [lia | exact Hhit].
      * split.
        -- subst indices.
           intros idx Hbound Hmatch.
           apply matching_indices_in_iff.
           split.
           ++ subst fuel_z.
              rewrite !string_of_list_z_length in Hbound.
              rewrite !Zlength_correct in *.
              lia.
           ++ apply match_at_complete_match_at_zb; assumption.
        -- subst indices fuel_z.
           unfold count_matches_upto.
           rewrite <- matching_indices_length_count.
           rewrite Nat2Z.id.
           reflexivity.
Qed.
