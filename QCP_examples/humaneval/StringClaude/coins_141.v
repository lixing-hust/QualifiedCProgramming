Load "../spec/141".

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

Definition yesno_of_z_141 (z : Z) : string :=
  if Z.eqb z 1 then "Yes" else "No".

Definition problem_141_pre_z (file_name : list Z) : Prop :=
  problem_141_pre (string_of_list_z file_name).

Definition problem_141_spec_z (file_name : list Z) (output : Z) : Prop :=
  problem_141_spec (string_of_list_z file_name) (yesno_of_z_141 output).

Definition is_digit_z (x : Z) : Prop :=
  48 <= x <= 57.

Definition is_digit_zb (x : Z) : bool :=
  Z.leb 48 x && Z.leb x 57.

Definition is_alpha_z (x : Z) : Prop :=
  65 <= x <= 90 \/ 97 <= x <= 122.

Definition is_dot_zb (x : Z) : bool :=
  Z.eqb x 46.

Fixpoint count_by_zb (f : Z -> bool) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if f x then 1 else 0) + count_by_zb f xs
  end.

Definition digit_count_upto (i : Z) (l : list Z) : Z :=
  count_by_zb is_digit_zb (sublist 0 i l).

Definition dot_count_upto (i : Z) (l : list Z) : Z :=
  count_by_zb is_dot_zb (sublist 0 i l).

Definition suffix_txt_z (l : list Z) : Prop :=
  Znth (Zlength l - 4) l 0 = 46 /\
  Znth (Zlength l - 3) l 0 = 116 /\
  Znth (Zlength l - 2) l 0 = 120 /\
  Znth (Zlength l - 1) l 0 = 116.

Definition suffix_exe_z (l : list Z) : Prop :=
  Znth (Zlength l - 4) l 0 = 46 /\
  Znth (Zlength l - 3) l 0 = 101 /\
  Znth (Zlength l - 2) l 0 = 120 /\
  Znth (Zlength l - 1) l 0 = 101.

Definition suffix_dll_z (l : list Z) : Prop :=
  Znth (Zlength l - 4) l 0 = 46 /\
  Znth (Zlength l - 3) l 0 = 100 /\
  Znth (Zlength l - 2) l 0 = 108 /\
  Znth (Zlength l - 1) l 0 = 108.

Definition suffix_ok_z (l : list Z) : Prop :=
  suffix_txt_z l \/ suffix_exe_z l \/ suffix_dll_z l.

Definition file_name_checks_z (l : list Z) : Prop :=
  5 <= Zlength l /\
  is_alpha_z (Znth 0 l 0) /\
  suffix_ok_z l /\
  digit_count_upto (Zlength l) l <= 3 /\
  dot_count_upto (Zlength l) l = 1.

Definition is_dot_ascii_bool (c : ascii) : bool :=
  Ascii.eqb c "."%char.

Definition file_name_valid_ascii_141 (file_name : list ascii) : Prop :=
  (List.length (filter is_digit_bool file_name) <= 3)%nat /\
  exists (prefix suffix : list ascii),
    file_name = (prefix ++ "."%char :: suffix)%list /\
    ~ In "."%char (prefix ++ suffix)%list /\
    (exists first_char rest_prefix,
       prefix = first_char :: rest_prefix /\ is_alpha first_char) /\
    (suffix = ["t"; "x"; "t"]%char \/
     suffix = ["e"; "x"; "e"]%char \/
     suffix = ["d"; "l"; "l"]%char).

Lemma ascii_of_z_46_141 : ascii_of_z 46 = "."%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_100_141 : ascii_of_z 100 = "d"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_101_141 : ascii_of_z 101 = "e"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_108_141 : ascii_of_z 108 = "l"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_116_141 : ascii_of_z 116 = "t"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_120_141 : ascii_of_z 120 = "x"%char.
Proof. reflexivity. Qed.

Lemma ascii_range_z_head_141 : forall c rest,
  ascii_range_z (c :: rest) ->
  0 <= c < 256.
Proof.
  intros c rest Hrange.
  specialize (Hrange 0).
  rewrite Znth0_cons in Hrange.
  apply Hrange.
  rewrite Zlength_cons.
  pose proof (Zlength_nonneg rest).
  lia.
Qed.

Lemma ascii_range_z_tail_141 : forall c rest,
  ascii_range_z (c :: rest) ->
  ascii_range_z rest.
Proof.
  unfold ascii_range_z.
  intros c rest Hrange i Hi.
  specialize (Hrange (i + 1)).
  rewrite Znth_cons in Hrange by lia.
  replace (i + 1 - 1) with i in Hrange by lia.
  apply Hrange.
  rewrite Zlength_cons.
  lia.
Qed.

Lemma is_digit_bool_ascii_of_z_141 : forall z,
  0 <= z < 256 ->
  is_digit_bool (ascii_of_z z) = is_digit_zb z.
Proof.
  intros z Hz.
  unfold is_digit_bool, is_digit_zb.
  rewrite nat_of_ascii_ascii_of_z by exact Hz.
  change (nat_of_ascii "0"%char) with 48%nat.
  change (nat_of_ascii "9"%char) with 57%nat.
  replace ((48 <=? Z.to_nat z)%nat) with (Z.leb 48 z).
  2:{
    destruct (Z.leb_spec 48 z).
    - symmetry. apply Nat.leb_le. lia.
    - symmetry. apply Nat.leb_gt. lia.
  }
  replace ((Z.to_nat z <=? 57)%nat) with (Z.leb z 57).
  2:{
    destruct (Z.leb_spec z 57).
    - symmetry. apply Nat.leb_le. lia.
    - symmetry. apply Nat.leb_gt. lia.
  }
  reflexivity.
Qed.

Lemma is_dot_ascii_bool_ascii_of_z_141 : forall z,
  0 <= z < 256 ->
  is_dot_ascii_bool (ascii_of_z z) = is_dot_zb z.
Proof.
  intros z Hz.
  unfold is_dot_ascii_bool, is_dot_zb.
  destruct (Ascii.eqb_spec (ascii_of_z z) "."%char) as [Heq | Hneq].
  - apply (f_equal nat_of_ascii) in Heq.
    rewrite nat_of_ascii_ascii_of_z in Heq by exact Hz.
    change (nat_of_ascii "."%char) with 46%nat in Heq.
    replace (Z.eqb z 46) with true by (symmetry; apply Z.eqb_eq; lia).
    reflexivity.
  - replace (Z.eqb z 46) with false.
    + reflexivity.
    + symmetry. apply Z.eqb_neq.
      intro Hz46. subst z. apply Hneq. reflexivity.
Qed.

Lemma is_alpha_ascii_of_z_141 : forall z,
  0 <= z < 256 ->
  (is_alpha (ascii_of_z z) <-> is_alpha_z z).
Proof.
  intros z Hz.
  unfold is_alpha, is_alpha_z.
  rewrite nat_of_ascii_ascii_of_z by exact Hz.
  change (nat_of_ascii "a"%char) with 97%nat.
  change (nat_of_ascii "z"%char) with 122%nat.
  change (nat_of_ascii "A"%char) with 65%nat.
  change (nat_of_ascii "Z"%char) with 90%nat.
  lia.
Qed.

Lemma count_by_zb_digits_filter_141 : forall l,
  ascii_range_z l ->
  Z.of_nat (List.length (filter is_digit_bool (map ascii_of_z l))) =
  count_by_zb is_digit_zb l.
Proof.
  induction l as [| c rest IH]; intros Hrange.
  - reflexivity.
  - cbn [map filter count_by_zb List.length].
    rewrite is_digit_bool_ascii_of_z_141 by
      (apply ascii_range_z_head_141 with (rest := rest); exact Hrange).
    pose proof (IH (ascii_range_z_tail_141 c rest Hrange)) as Hrest.
    destruct (is_digit_zb c); cbn [List.length].
    + rewrite Nat2Z.inj_succ. rewrite Hrest. lia.
    + rewrite Hrest. lia.
Qed.

Lemma count_by_zb_dot_filter_141 : forall l,
  ascii_range_z l ->
  Z.of_nat (List.length (filter is_dot_ascii_bool (map ascii_of_z l))) =
  count_by_zb is_dot_zb l.
Proof.
  induction l as [| c rest IH]; intros Hrange.
  - reflexivity.
  - cbn [map filter count_by_zb List.length].
    rewrite is_dot_ascii_bool_ascii_of_z_141 by
      (apply ascii_range_z_head_141 with (rest := rest); exact Hrange).
    pose proof (IH (ascii_range_z_tail_141 c rest Hrange)) as Hrest.
    destruct (is_dot_zb c); cbn [List.length].
    + rewrite Nat2Z.inj_succ. rewrite Hrest. lia.
    + rewrite Hrest. lia.
Qed.

Lemma digit_count_full_141 : forall l,
  digit_count_upto (Zlength l) l = count_by_zb is_digit_zb l.
Proof.
  intros l.
  unfold digit_count_upto.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.

Lemma dot_count_full_141 : forall l,
  dot_count_upto (Zlength l) l = count_by_zb is_dot_zb l.
Proof.
  intros l.
  unfold dot_count_upto.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.

Lemma problem_141_spec_z_yes_from_valid_ascii : forall l,
  file_name_valid_ascii_141 (map ascii_of_z l) ->
  problem_141_spec_z l 1.
Proof.
  intros l Hvalid.
  unfold problem_141_spec_z, yesno_of_z_141.
  simpl.
  unfold problem_141_spec.
  rewrite list_ascii_of_string_string_of_list_z.
  left.
  split; exact Hvalid || reflexivity.
Qed.

Lemma problem_141_spec_z_no_from_not_valid_ascii : forall l,
  ~ file_name_valid_ascii_141 (map ascii_of_z l) ->
  problem_141_spec_z l 0.
Proof.
  intros l Hnot.
  unfold problem_141_spec_z, yesno_of_z_141.
  simpl.
  unfold problem_141_spec.
  rewrite list_ascii_of_string_string_of_list_z.
  right.
  split; exact Hnot || reflexivity.
Qed.

Lemma file_name_valid_ascii_len_ge_5_141 : forall file_name,
  file_name_valid_ascii_141 file_name ->
  (5 <= List.length file_name)%nat.
Proof.
  intros file_name [_ [prefix [suffix [Hsplit [_ [[first [rest [Hprefix _]]] Hsuffix]]]]]].
  subst prefix file_name.
  destruct Hsuffix as [-> | [-> | ->]];
    repeat rewrite app_length; simpl; lia.
Qed.

Lemma problem_141_spec_z_no_len_lt : forall l,
  Zlength l < 5 ->
  problem_141_spec_z l 0.
Proof.
  intros l Hlen.
  apply problem_141_spec_z_no_from_not_valid_ascii.
  intro Hvalid.
  pose proof (file_name_valid_ascii_len_ge_5_141 _ Hvalid) as Hvalid_len.
  rewrite length_map in Hvalid_len.
  rewrite Zlength_correct in Hlen.
  lia.
Qed.

Lemma file_name_valid_ascii_alpha_141 : forall l,
  ascii_range_z l ->
  file_name_valid_ascii_141 (map ascii_of_z l) ->
  is_alpha_z (Znth 0 l 0).
Proof.
  intros l Hrange Hvalid.
  destruct Hvalid as [_ [prefix [suffix [Hsplit [_ [[first [rest [Hprefix Halpha]]] _]]]]]].
  destruct l as [| c tail].
  - simpl in Hsplit.
    subst prefix.
    discriminate.
  - simpl in Hsplit.
    subst prefix.
    inversion Hsplit; subst first.
    rewrite Znth0_cons.
    apply (proj1 (is_alpha_ascii_of_z_141 c
      (ascii_range_z_head_141 c tail Hrange))).
    exact Halpha.
Qed.

Lemma problem_141_spec_z_no_not_alpha : forall l,
  ascii_range_z l ->
  ~ is_alpha_z (Znth 0 l 0) ->
  problem_141_spec_z l 0.
Proof.
  intros l Hrange Hnot.
  apply problem_141_spec_z_no_from_not_valid_ascii.
  intro Hvalid.
  apply Hnot.
  apply file_name_valid_ascii_alpha_141; assumption.
Qed.

Lemma file_name_valid_ascii_digit_count_141 : forall l,
  ascii_range_z l ->
  file_name_valid_ascii_141 (map ascii_of_z l) ->
  digit_count_upto (Zlength l) l <= 3.
Proof.
  intros l Hrange [Hdigits _].
  rewrite digit_count_full_141.
  rewrite <- count_by_zb_digits_filter_141 by exact Hrange.
  lia.
Qed.

Lemma problem_141_spec_z_no_digit_gt : forall l,
  ascii_range_z l ->
  digit_count_upto (Zlength l) l > 3 ->
  problem_141_spec_z l 0.
Proof.
  intros l Hrange Hgt.
  apply problem_141_spec_z_no_from_not_valid_ascii.
  intro Hvalid.
  pose proof (file_name_valid_ascii_digit_count_141 _ Hrange Hvalid).
  lia.
Qed.

Lemma is_dot_ascii_bool_true_iff_141 : forall c,
  is_dot_ascii_bool c = true <-> c = "."%char.
Proof.
  intros c.
  unfold is_dot_ascii_bool.
  split.
  - intro H. apply Ascii.eqb_eq. exact H.
  - intro H. subst. apply Ascii.eqb_refl.
Qed.

Lemma filter_dot_nil_not_in_141 : forall l,
  ~ In "."%char l ->
  filter is_dot_ascii_bool l = [].
Proof.
  induction l as [| c rest IH]; intros Hnot.
  - reflexivity.
  - simpl.
    destruct (is_dot_ascii_bool c) eqn:Hdot.
    + apply is_dot_ascii_bool_true_iff_141 in Hdot.
      subst c.
      exfalso. apply Hnot. left. reflexivity.
    + apply IH.
      intro Hin. apply Hnot. right. exact Hin.
Qed.

Lemma file_name_valid_ascii_dot_count_141 : forall file_name,
  file_name_valid_ascii_141 file_name ->
  List.length (filter is_dot_ascii_bool file_name) = 1%nat.
Proof.
  intros file_name [_ [prefix [suffix [Hsplit [Hnodot _]]]]].
  subst file_name.
  rewrite filter_app.
  rewrite filter_dot_nil_not_in_141.
  2:{ intro Hin. apply Hnodot. apply in_or_app. left. exact Hin. }
  change (is_dot_ascii_bool "."%char) with true.
  simpl.
  rewrite filter_dot_nil_not_in_141.
  2:{ intro Hin. apply Hnodot. apply in_or_app. right. exact Hin. }
  reflexivity.
Qed.

Lemma file_name_valid_ascii_dot_count_z_141 : forall l,
  ascii_range_z l ->
  file_name_valid_ascii_141 (map ascii_of_z l) ->
  dot_count_upto (Zlength l) l = 1.
Proof.
  intros l Hrange Hvalid.
  rewrite dot_count_full_141.
  rewrite <- count_by_zb_dot_filter_141 by exact Hrange.
  rewrite file_name_valid_ascii_dot_count_141 by exact Hvalid.
  reflexivity.
Qed.

Lemma problem_141_spec_z_no_dot_ne : forall l,
  ascii_range_z l ->
  dot_count_upto (Zlength l) l <> 1 ->
  problem_141_spec_z l 0.
Proof.
  intros l Hrange Hne.
  apply problem_141_spec_z_no_from_not_valid_ascii.
  intro Hvalid.
  apply Hne.
  apply file_name_valid_ascii_dot_count_z_141; assumption.
Qed.

Lemma map_sublist_141 : forall {A B : Type} (f : A -> B) lo hi (l : list A),
  map f (sublist lo hi l) = sublist lo hi (map f l).
Proof.
  intros A B f lo hi l.
  unfold sublist.
  rewrite firstn_map.
  rewrite skipn_map.
  reflexivity.
Qed.

Lemma filter_dot_in_length_pos_141 : forall l,
  In "."%char l ->
  (1 <= List.length (filter is_dot_ascii_bool l))%nat.
Proof.
  induction l as [| c rest IH]; intros Hin.
  - contradiction.
  - simpl in Hin.
    destruct Hin as [-> | Hin].
    + change (is_dot_ascii_bool "."%char) with true.
      simpl. lia.
    + simpl.
      destruct (is_dot_ascii_bool c); simpl.
      * lia.
      * apply IH. exact Hin.
Qed.

Lemma filter_dot_middle_no_other_141 : forall prefix suffix,
  List.length (filter is_dot_ascii_bool (prefix ++ "."%char :: suffix)) = 1%nat ->
  ~ In "."%char (prefix ++ suffix)%list.
Proof.
  intros prefix suffix Hcount Hin.
  rewrite filter_app in Hcount.
  change (is_dot_ascii_bool "."%char) with true in Hcount.
  simpl in Hcount.
  rewrite app_length in Hcount.
  simpl in Hcount.
  apply in_app_or in Hin.
  destruct Hin as [Hin | Hin].
  - pose proof (filter_dot_in_length_pos_141 _ Hin).
    lia.
  - pose proof (filter_dot_in_length_pos_141 _ Hin).
    lia.
Qed.

Lemma dot_filter_length_full_141 : forall l,
  ascii_range_z l ->
  dot_count_upto (Zlength l) l = 1 ->
  List.length (filter is_dot_ascii_bool (map ascii_of_z l)) = 1%nat.
Proof.
  intros l Hrange Hdot.
  rewrite dot_count_full_141 in Hdot.
  pose proof (count_by_zb_dot_filter_141 l Hrange) as Hcount.
  rewrite Hdot in Hcount.
  lia.
Qed.

Lemma prefix_alpha_decomp_141 : forall l,
  5 <= Zlength l ->
  ascii_range_z l ->
  is_alpha_z (Znth 0 l 0) ->
  exists first_char rest_prefix,
    map ascii_of_z (sublist 0 (Zlength l - 4) l) = first_char :: rest_prefix /\
    is_alpha first_char.
Proof.
  intros l Hlen Hrange Halpha.
  exists (ascii_of_z (Znth 0 l 0)).
  exists (map ascii_of_z (sublist 1 (Zlength l - 4) l)).
  split.
  - rewrite (sublist_split 0 (Zlength l - 4) 1 l) by
      (rewrite Zlength_correct in *; lia).
    replace (sublist 0 1 l) with [Znth 0 l 0].
    2:{ replace 1 with (0 + 1) by lia.
        symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
    simpl.
    reflexivity.
  - apply (proj2 (is_alpha_ascii_of_z_141 (Znth 0 l 0)
      ltac:(apply Hrange; rewrite Zlength_correct in *; lia))).
    exact Halpha.

Qed.

Lemma suffix_txt_sublist_for_valid_141 : forall l,
  5 <= Zlength l ->
  suffix_txt_z l ->
  sublist (Zlength l - 4) (Zlength l) l = [46; 116; 120; 116].
Proof.
  intros l Hlen [H0 [H1 [H2 H3]]].
  rewrite (sublist_split (Zlength l - 4) (Zlength l) (Zlength l - 3) l) by
    (rewrite Zlength_correct in *; lia).
  rewrite (sublist_split (Zlength l - 3) (Zlength l) (Zlength l - 2) l) by
    (rewrite Zlength_correct in *; lia).
  rewrite (sublist_split (Zlength l - 2) (Zlength l) (Zlength l - 1) l) by
    (rewrite Zlength_correct in *; lia).
  replace (sublist (Zlength l - 4) (Zlength l - 3) l)
    with [Znth (Zlength l - 4) l 0].
  2:{ replace (Zlength l - 3) with (Zlength l - 4 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 3) (Zlength l - 2) l)
    with [Znth (Zlength l - 3) l 0].
  2:{ replace (Zlength l - 2) with (Zlength l - 3 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 2) (Zlength l - 1) l)
    with [Znth (Zlength l - 2) l 0].
  2:{ replace (Zlength l - 1) with (Zlength l - 2 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 1) (Zlength l) l)
    with [Znth (Zlength l - 1) l 0].
  2:{ replace (Zlength l) with (Zlength l - 1 + 1) by lia.
      replace (Zlength l - 1 + 1 - 1) with (Zlength l - 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  rewrite H0, H1, H2, H3.
  reflexivity.
Qed.

Lemma suffix_exe_sublist_for_valid_141 : forall l,
  5 <= Zlength l ->
  suffix_exe_z l ->
  sublist (Zlength l - 4) (Zlength l) l = [46; 101; 120; 101].
Proof.
  intros l Hlen [H0 [H1 [H2 H3]]].
  rewrite (sublist_split (Zlength l - 4) (Zlength l) (Zlength l - 3) l) by
    (rewrite Zlength_correct in *; lia).
  rewrite (sublist_split (Zlength l - 3) (Zlength l) (Zlength l - 2) l) by
    (rewrite Zlength_correct in *; lia).
  rewrite (sublist_split (Zlength l - 2) (Zlength l) (Zlength l - 1) l) by
    (rewrite Zlength_correct in *; lia).
  replace (sublist (Zlength l - 4) (Zlength l - 3) l)
    with [Znth (Zlength l - 4) l 0].
  2:{ replace (Zlength l - 3) with (Zlength l - 4 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 3) (Zlength l - 2) l)
    with [Znth (Zlength l - 3) l 0].
  2:{ replace (Zlength l - 2) with (Zlength l - 3 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 2) (Zlength l - 1) l)
    with [Znth (Zlength l - 2) l 0].
  2:{ replace (Zlength l - 1) with (Zlength l - 2 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 1) (Zlength l) l)
    with [Znth (Zlength l - 1) l 0].
  2:{ replace (Zlength l) with (Zlength l - 1 + 1) by lia.
      replace (Zlength l - 1 + 1 - 1) with (Zlength l - 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  rewrite H0, H1, H2, H3.
  reflexivity.
Qed.

Lemma suffix_dll_sublist_for_valid_141 : forall l,
  5 <= Zlength l ->
  suffix_dll_z l ->
  sublist (Zlength l - 4) (Zlength l) l = [46; 100; 108; 108].
Proof.
  intros l Hlen [H0 [H1 [H2 H3]]].
  rewrite (sublist_split (Zlength l - 4) (Zlength l) (Zlength l - 3) l) by
    (rewrite Zlength_correct in *; lia).
  rewrite (sublist_split (Zlength l - 3) (Zlength l) (Zlength l - 2) l) by
    (rewrite Zlength_correct in *; lia).
  rewrite (sublist_split (Zlength l - 2) (Zlength l) (Zlength l - 1) l) by
    (rewrite Zlength_correct in *; lia).
  replace (sublist (Zlength l - 4) (Zlength l - 3) l)
    with [Znth (Zlength l - 4) l 0].
  2:{ replace (Zlength l - 3) with (Zlength l - 4 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 3) (Zlength l - 2) l)
    with [Znth (Zlength l - 3) l 0].
  2:{ replace (Zlength l - 2) with (Zlength l - 3 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 2) (Zlength l - 1) l)
    with [Znth (Zlength l - 2) l 0].
  2:{ replace (Zlength l - 1) with (Zlength l - 2 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 1) (Zlength l) l)
    with [Znth (Zlength l - 1) l 0].
  2:{ replace (Zlength l) with (Zlength l - 1 + 1) by lia.
      replace (Zlength l - 1 + 1 - 1) with (Zlength l - 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  rewrite H0, H1, H2, H3.
  reflexivity.
Qed.

Lemma file_name_checks_valid_ascii_suffix_txt_141 : forall l,
  ascii_range_z l ->
  file_name_checks_z l ->
  suffix_txt_z l ->
  file_name_valid_ascii_141 (map ascii_of_z l).
Proof.
  intros l Hrange [Hlen [Halpha [_ [Hdigits Hdot]]]] Hsuffix.
  set (prefix := map ascii_of_z (sublist 0 (Zlength l - 4) l)).
  assert (Htail : sublist (Zlength l - 4) (Zlength l) l = [46; 116; 120; 116])
    by (apply suffix_txt_sublist_for_valid_141; assumption).
  assert (Hsplit_l :
    l = (sublist 0 (Zlength l - 4) l ++ sublist (Zlength l - 4) (Zlength l) l)%list).
  {
    rewrite <- (sublist_split 0 (Zlength l) (Zlength l - 4) l) by
      (rewrite Zlength_correct in *; lia).
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  assert (Hfile :
    map ascii_of_z l = (prefix ++ "."%char :: ["t"; "x"; "t"]%char)%list).
  {
    rewrite Hsplit_l at 1.
    rewrite map_app, Htail.
    simpl.
    rewrite ascii_of_z_46_141, ascii_of_z_116_141, ascii_of_z_120_141.
    subst prefix.
    reflexivity.
  }
  split.
  - apply Nat2Z.inj_le.
    rewrite count_by_zb_digits_filter_141 by exact Hrange.
    rewrite <- digit_count_full_141.
    exact Hdigits.
  - exists prefix, ["t"; "x"; "t"]%char.
    split; [exact Hfile |].
    split.
    + apply filter_dot_middle_no_other_141.
      rewrite <- Hfile.
      apply dot_filter_length_full_141; assumption.
    + split.
      * apply prefix_alpha_decomp_141; assumption.
      * left. reflexivity.
Qed.

Lemma file_name_checks_valid_ascii_suffix_exe_141 : forall l,
  ascii_range_z l ->
  file_name_checks_z l ->
  suffix_exe_z l ->
  file_name_valid_ascii_141 (map ascii_of_z l).
Proof.
  intros l Hrange [Hlen [Halpha [_ [Hdigits Hdot]]]] Hsuffix.
  set (prefix := map ascii_of_z (sublist 0 (Zlength l - 4) l)).
  assert (Htail : sublist (Zlength l - 4) (Zlength l) l = [46; 101; 120; 101])
    by (apply suffix_exe_sublist_for_valid_141; assumption).
  assert (Hsplit_l :
    l = (sublist 0 (Zlength l - 4) l ++ sublist (Zlength l - 4) (Zlength l) l)%list).
  {
    rewrite <- (sublist_split 0 (Zlength l) (Zlength l - 4) l) by
      (rewrite Zlength_correct in *; lia).
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  assert (Hfile :
    map ascii_of_z l = (prefix ++ "."%char :: ["e"; "x"; "e"]%char)%list).
  {
    rewrite Hsplit_l at 1.
    rewrite map_app, Htail.
    simpl.
    rewrite ascii_of_z_46_141, ascii_of_z_101_141, ascii_of_z_120_141.
    subst prefix.
    reflexivity.
  }
  split.
  - apply Nat2Z.inj_le.
    rewrite count_by_zb_digits_filter_141 by exact Hrange.
    rewrite <- digit_count_full_141.
    exact Hdigits.
  - exists prefix, ["e"; "x"; "e"]%char.
    split; [exact Hfile |].
    split.
    + apply filter_dot_middle_no_other_141.
      rewrite <- Hfile.
      apply dot_filter_length_full_141; assumption.
    + split.
      * apply prefix_alpha_decomp_141; assumption.
      * right. left. reflexivity.
Qed.

Lemma file_name_checks_valid_ascii_suffix_dll_141 : forall l,
  ascii_range_z l ->
  file_name_checks_z l ->
  suffix_dll_z l ->
  file_name_valid_ascii_141 (map ascii_of_z l).
Proof.
  intros l Hrange [Hlen [Halpha [_ [Hdigits Hdot]]]] Hsuffix.
  set (prefix := map ascii_of_z (sublist 0 (Zlength l - 4) l)).
  assert (Htail : sublist (Zlength l - 4) (Zlength l) l = [46; 100; 108; 108])
    by (apply suffix_dll_sublist_for_valid_141; assumption).
  assert (Hsplit_l :
    l = (sublist 0 (Zlength l - 4) l ++ sublist (Zlength l - 4) (Zlength l) l)%list).
  {
    rewrite <- (sublist_split 0 (Zlength l) (Zlength l - 4) l) by
      (rewrite Zlength_correct in *; lia).
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  assert (Hfile :
    map ascii_of_z l = (prefix ++ "."%char :: ["d"; "l"; "l"]%char)%list).
  {
    rewrite Hsplit_l at 1.
    rewrite map_app, Htail.
    simpl.
    rewrite ascii_of_z_46_141, ascii_of_z_100_141, ascii_of_z_108_141.
    subst prefix.
    reflexivity.
  }
  split.
  - apply Nat2Z.inj_le.
    rewrite count_by_zb_digits_filter_141 by exact Hrange.
    rewrite <- digit_count_full_141.
    exact Hdigits.
  - exists prefix, ["d"; "l"; "l"]%char.
    split; [exact Hfile |].
    split.
    + apply filter_dot_middle_no_other_141.
      rewrite <- Hfile.
      apply dot_filter_length_full_141; assumption.
    + split.
      * apply prefix_alpha_decomp_141; assumption.
      * right. right. reflexivity.
Qed.

Lemma file_name_checks_valid_ascii_141 : forall l,
  ascii_range_z l ->
  file_name_checks_z l ->
  file_name_valid_ascii_141 (map ascii_of_z l).
Proof.
  intros l Hrange Hchecks.
  destruct Hchecks as [Hlen [Halpha [Hsuffix [Hdigits Hdot]]]].
  destruct Hsuffix as [Htxt | [Hexe | Hdll]].
  - apply file_name_checks_valid_ascii_suffix_txt_141; try assumption.
    repeat split; try assumption.
    left. assumption.
  - apply file_name_checks_valid_ascii_suffix_exe_141; try assumption.
    repeat split; try assumption.
    right. left. assumption.
  - apply file_name_checks_valid_ascii_suffix_dll_141; try assumption.
    repeat split; try assumption.
    right. right. assumption.
Qed.

Lemma ascii_of_z_inj_141 : forall x y,
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

Lemma Znth_map_141 : forall {A B : Type} (f : A -> B) l k da db,
  0 <= k < Zlength l ->
  Znth k (map f l) db = f (Znth k l da).
Proof.
  induction l as [| x xs IH]; intros k da db Hk.
  - rewrite Zlength_correct in Hk. simpl in Hk. lia.
  - destruct (Z.eq_dec k 0) as [-> | Hnz].
    + simpl. repeat rewrite Znth0_cons. reflexivity.
    + simpl.
      rewrite Znth_cons by lia.
      rewrite Znth_cons by lia.
      apply IH.
      rewrite Zlength_cons in Hk.
      lia.
Qed.

Lemma sublist_app_tail_141 : forall {A : Type} (prefix tail : list A),
  sublist (Zlength prefix) (Zlength prefix + Zlength tail) (prefix ++ tail) = tail.
Proof.
  intros A prefix tail.
  unfold sublist.
  rewrite firstn_all2.
  2:{ rewrite List.app_length, !Zlength_correct. lia. }
  replace (Z.to_nat (Zlength prefix)) with (List.length prefix) by
    (rewrite Zlength_correct; lia).
  rewrite skipn_app.
  rewrite Nat.sub_diag.
  rewrite skipn_all.
  simpl.
  reflexivity.
Qed.

Lemma valid_split_tail_ascii_141 : forall l prefix suffix,
  map ascii_of_z l = (prefix ++ "."%char :: suffix)%list ->
  Zlength suffix = 3 ->
  sublist (Zlength l - 4) (Zlength l) (map ascii_of_z l) =
    ("."%char :: suffix)%list.
Proof.
  intros l prefix suffix Hfile Hsuffix_len.
  assert (Hlenmap : Zlength (map ascii_of_z l) = Zlength l).
  { rewrite !Zlength_correct, map_length. reflexivity. }
  assert (Hlen : Zlength l = Zlength prefix + Zlength ("."%char :: suffix)).
  {
    rewrite <- Hlenmap, Hfile.
    rewrite Zlength_app.
    lia.
  }
  rewrite Hfile.
  replace (Zlength l - 4) with (Zlength prefix) by
    (rewrite Zlength_cons in Hlen; lia).
  replace (Zlength l) with (Zlength prefix + Zlength ("."%char :: suffix)) by
    lia.
  apply sublist_app_tail_141.
Qed.

Lemma ascii_range_z_sublist_141 : forall l lo hi,
  ascii_range_z l ->
  0 <= lo /\ lo <= hi /\ hi <= Zlength l ->
  ascii_range_z (sublist lo hi l).
Proof.
  unfold ascii_range_z.
  intros l lo hi Hrange Hbounds k Hk.
  destruct Hbounds as [Hlo [Hlohi Hhi]].
  rewrite Zlength_sublist in Hk by lia.
  rewrite Znth_sublist by lia.
  apply Hrange.
  lia.
Qed.

Lemma suffix_txt_z_from_ascii_tail_141 : forall l,
  ascii_range_z l ->
  5 <= Zlength l ->
  map ascii_of_z (sublist (Zlength l - 4) (Zlength l) l) =
    ["."%char; "t"%char; "x"%char; "t"%char] ->
  suffix_txt_z l.
Proof.
  intros l Hrange Hlen Hmap.
  set (tail := sublist (Zlength l - 4) (Zlength l) l) in *.
  assert (Htail_len : Zlength tail = 4).
  { subst tail. rewrite Zlength_sublist by lia. lia. }
  assert (Htail_range : ascii_range_z tail).
  { subst tail. apply ascii_range_z_sublist_141; [exact Hrange | lia]. }
  assert (H0 : ascii_of_z (Znth 0 tail 0) = "."%char).
  { rewrite <- (Znth_map_141 ascii_of_z tail 0 0 "."%char) by lia.
    rewrite Hmap. reflexivity. }
  assert (H1 : ascii_of_z (Znth 1 tail 0) = "t"%char).
  { rewrite <- (Znth_map_141 ascii_of_z tail 1 0 "."%char) by lia.
    rewrite Hmap. reflexivity. }
  assert (H2 : ascii_of_z (Znth 2 tail 0) = "x"%char).
  { rewrite <- (Znth_map_141 ascii_of_z tail 2 0 "."%char) by lia.
    rewrite Hmap. reflexivity. }
  assert (H3 : ascii_of_z (Znth 3 tail 0) = "t"%char).
  { rewrite <- (Znth_map_141 ascii_of_z tail 3 0 "."%char) by lia.
    rewrite Hmap. reflexivity. }
  assert (E0 : Znth 0 tail 0 = 46).
  { apply ascii_of_z_inj_141; [apply Htail_range; lia | lia |].
    rewrite ascii_of_z_46_141. exact H0. }
  assert (E1 : Znth 1 tail 0 = 116).
  { apply ascii_of_z_inj_141; [apply Htail_range; lia | lia |].
    rewrite ascii_of_z_116_141. exact H1. }
  assert (E2 : Znth 2 tail 0 = 120).
  { apply ascii_of_z_inj_141; [apply Htail_range; lia | lia |].
    rewrite ascii_of_z_120_141. exact H2. }
  assert (E3 : Znth 3 tail 0 = 116).
  { apply ascii_of_z_inj_141; [apply Htail_range; lia | lia |].
    rewrite ascii_of_z_116_141. exact H3. }
  subst tail.
  unfold suffix_txt_z.
  repeat split.
  - replace (Zlength l - 4) with (0 + (Zlength l - 4)) by lia.
    rewrite <- (Znth_sublist (Zlength l - 4) 0 (Zlength l) l) by lia. exact E0.
  - replace (Zlength l - 3) with (1 + (Zlength l - 4)) by lia.
    rewrite <- (Znth_sublist (Zlength l - 4) 1 (Zlength l) l) by lia. exact E1.
  - replace (Zlength l - 2) with (2 + (Zlength l - 4)) by lia.
    rewrite <- (Znth_sublist (Zlength l - 4) 2 (Zlength l) l) by lia. exact E2.
  - replace (Zlength l - 1) with (3 + (Zlength l - 4)) by lia.
    rewrite <- (Znth_sublist (Zlength l - 4) 3 (Zlength l) l) by lia. exact E3.
Qed.

Lemma suffix_exe_z_from_ascii_tail_141 : forall l,
  ascii_range_z l ->
  5 <= Zlength l ->
  map ascii_of_z (sublist (Zlength l - 4) (Zlength l) l) =
    ["."%char; "e"%char; "x"%char; "e"%char] ->
  suffix_exe_z l.
Proof.
  intros l Hrange Hlen Hmap.
  set (tail := sublist (Zlength l - 4) (Zlength l) l) in *.
  assert (Htail_len : Zlength tail = 4).
  { subst tail. rewrite Zlength_sublist by lia. lia. }
  assert (Htail_range : ascii_range_z tail).
  { subst tail. apply ascii_range_z_sublist_141; [exact Hrange | lia]. }
  assert (H0 : ascii_of_z (Znth 0 tail 0) = "."%char).
  { rewrite <- (Znth_map_141 ascii_of_z tail 0 0 "."%char) by lia.
    rewrite Hmap. reflexivity. }
  assert (H1 : ascii_of_z (Znth 1 tail 0) = "e"%char).
  { rewrite <- (Znth_map_141 ascii_of_z tail 1 0 "."%char) by lia.
    rewrite Hmap. reflexivity. }
  assert (H2 : ascii_of_z (Znth 2 tail 0) = "x"%char).
  { rewrite <- (Znth_map_141 ascii_of_z tail 2 0 "."%char) by lia.
    rewrite Hmap. reflexivity. }
  assert (H3 : ascii_of_z (Znth 3 tail 0) = "e"%char).
  { rewrite <- (Znth_map_141 ascii_of_z tail 3 0 "."%char) by lia.
    rewrite Hmap. reflexivity. }
  assert (E0 : Znth 0 tail 0 = 46).
  { apply ascii_of_z_inj_141; [apply Htail_range; lia | lia |].
    rewrite ascii_of_z_46_141. exact H0. }
  assert (E1 : Znth 1 tail 0 = 101).
  { apply ascii_of_z_inj_141; [apply Htail_range; lia | lia |].
    rewrite ascii_of_z_101_141. exact H1. }
  assert (E2 : Znth 2 tail 0 = 120).
  { apply ascii_of_z_inj_141; [apply Htail_range; lia | lia |].
    rewrite ascii_of_z_120_141. exact H2. }
  assert (E3 : Znth 3 tail 0 = 101).
  { apply ascii_of_z_inj_141; [apply Htail_range; lia | lia |].
    rewrite ascii_of_z_101_141. exact H3. }
  subst tail.
  unfold suffix_exe_z.
  repeat split.
  - replace (Zlength l - 4) with (0 + (Zlength l - 4)) by lia.
    rewrite <- (Znth_sublist (Zlength l - 4) 0 (Zlength l) l) by lia. exact E0.
  - replace (Zlength l - 3) with (1 + (Zlength l - 4)) by lia.
    rewrite <- (Znth_sublist (Zlength l - 4) 1 (Zlength l) l) by lia. exact E1.
  - replace (Zlength l - 2) with (2 + (Zlength l - 4)) by lia.
    rewrite <- (Znth_sublist (Zlength l - 4) 2 (Zlength l) l) by lia. exact E2.
  - replace (Zlength l - 1) with (3 + (Zlength l - 4)) by lia.
    rewrite <- (Znth_sublist (Zlength l - 4) 3 (Zlength l) l) by lia. exact E3.
Qed.

Lemma suffix_dll_z_from_ascii_tail_141 : forall l,
  ascii_range_z l ->
  5 <= Zlength l ->
  map ascii_of_z (sublist (Zlength l - 4) (Zlength l) l) =
    ["."%char; "d"%char; "l"%char; "l"%char] ->
  suffix_dll_z l.
Proof.
  intros l Hrange Hlen Hmap.
  set (tail := sublist (Zlength l - 4) (Zlength l) l) in *.
  assert (Htail_len : Zlength tail = 4).
  { subst tail. rewrite Zlength_sublist by lia. lia. }
  assert (Htail_range : ascii_range_z tail).
  { subst tail. apply ascii_range_z_sublist_141; [exact Hrange | lia]. }
  assert (H0 : ascii_of_z (Znth 0 tail 0) = "."%char).
  { rewrite <- (Znth_map_141 ascii_of_z tail 0 0 "."%char) by lia.
    rewrite Hmap. reflexivity. }
  assert (H1 : ascii_of_z (Znth 1 tail 0) = "d"%char).
  { rewrite <- (Znth_map_141 ascii_of_z tail 1 0 "."%char) by lia.
    rewrite Hmap. reflexivity. }
  assert (H2 : ascii_of_z (Znth 2 tail 0) = "l"%char).
  { rewrite <- (Znth_map_141 ascii_of_z tail 2 0 "."%char) by lia.
    rewrite Hmap. reflexivity. }
  assert (H3 : ascii_of_z (Znth 3 tail 0) = "l"%char).
  { rewrite <- (Znth_map_141 ascii_of_z tail 3 0 "."%char) by lia.
    rewrite Hmap. reflexivity. }
  assert (E0 : Znth 0 tail 0 = 46).
  { apply ascii_of_z_inj_141; [apply Htail_range; lia | lia |].
    rewrite ascii_of_z_46_141. exact H0. }
  assert (E1 : Znth 1 tail 0 = 100).
  { apply ascii_of_z_inj_141; [apply Htail_range; lia | lia |].
    rewrite ascii_of_z_100_141. exact H1. }
  assert (E2 : Znth 2 tail 0 = 108).
  { apply ascii_of_z_inj_141; [apply Htail_range; lia | lia |].
    rewrite ascii_of_z_108_141. exact H2. }
  assert (E3 : Znth 3 tail 0 = 108).
  { apply ascii_of_z_inj_141; [apply Htail_range; lia | lia |].
    rewrite ascii_of_z_108_141. exact H3. }
  subst tail.
  unfold suffix_dll_z.
  repeat split.
  - replace (Zlength l - 4) with (0 + (Zlength l - 4)) by lia.
    rewrite <- (Znth_sublist (Zlength l - 4) 0 (Zlength l) l) by lia. exact E0.
  - replace (Zlength l - 3) with (1 + (Zlength l - 4)) by lia.
    rewrite <- (Znth_sublist (Zlength l - 4) 1 (Zlength l) l) by lia. exact E1.
  - replace (Zlength l - 2) with (2 + (Zlength l - 4)) by lia.
    rewrite <- (Znth_sublist (Zlength l - 4) 2 (Zlength l) l) by lia. exact E2.
  - replace (Zlength l - 1) with (3 + (Zlength l - 4)) by lia.
    rewrite <- (Znth_sublist (Zlength l - 4) 3 (Zlength l) l) by lia. exact E3.
Qed.

Lemma file_name_valid_ascii_suffix_ok_z_141 : forall l,
  ascii_range_z l ->
  file_name_valid_ascii_141 (map ascii_of_z l) ->
  suffix_ok_z l.
Proof.
  intros l Hrange Hvalid.
  pose proof (file_name_valid_ascii_len_ge_5_141 _ Hvalid) as Hlen_nat.
  assert (Hlen : 5 <= Zlength l).
  { rewrite map_length in Hlen_nat.
    rewrite Zlength_correct.
    lia. }
  destruct Hvalid as [_ [prefix [suffix [Hfile [_ [_ Hsuffix]]]]]].
  assert (Hsuffix_len : Zlength suffix = 3).
  {
    destruct Hsuffix as [-> | [-> | ->]];
      rewrite Zlength_correct; simpl; reflexivity.
  }
  pose proof (valid_split_tail_ascii_141 l prefix suffix Hfile Hsuffix_len) as Htail_ascii.
  rewrite <- map_sublist_141 in Htail_ascii.
  destruct Hsuffix as [-> | [-> | ->]].
  - left.
    apply suffix_txt_z_from_ascii_tail_141; assumption.
  - right. left.
    apply suffix_exe_z_from_ascii_tail_141; assumption.
  - right. right.
    apply suffix_dll_z_from_ascii_tail_141; assumption.
Qed.

Lemma problem_141_spec_z_no_not_suffix : forall l,
  ascii_range_z l ->
  ~ suffix_ok_z l ->
  problem_141_spec_z l 0.
Proof.
  intros l Hrange Hnot.
  apply problem_141_spec_z_no_from_not_valid_ascii.
  intro Hvalid.
  apply Hnot.
  apply file_name_valid_ascii_suffix_ok_z_141; assumption.
Qed.

Lemma suffix_txt_sublist_141 : forall l,
  5 <= Zlength l ->
  suffix_txt_z l ->
  sublist (Zlength l - 4) (Zlength l) l = [46; 116; 120; 116].
Proof.
  intros l Hlen [H0 [H1 [H2 H3]]].
  rewrite (sublist_split (Zlength l - 4) (Zlength l) (Zlength l - 3) l) by
    (rewrite Zlength_correct in *; lia).
  rewrite (sublist_split (Zlength l - 3) (Zlength l) (Zlength l - 2) l) by
    (rewrite Zlength_correct in *; lia).
  rewrite (sublist_split (Zlength l - 2) (Zlength l) (Zlength l - 1) l) by
    (rewrite Zlength_correct in *; lia).
  replace (sublist (Zlength l - 4) (Zlength l - 3) l)
    with [Znth (Zlength l - 4) l 0].
  2:{ replace (Zlength l - 3) with (Zlength l - 4 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 3) (Zlength l - 2) l)
    with [Znth (Zlength l - 3) l 0].
  2:{ replace (Zlength l - 2) with (Zlength l - 3 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 2) (Zlength l - 1) l)
    with [Znth (Zlength l - 2) l 0].
  2:{ replace (Zlength l - 1) with (Zlength l - 2 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 1) (Zlength l) l)
    with [Znth (Zlength l - 1) l 0].
  2:{ replace (Zlength l) with (Zlength l - 1 + 1) by lia.
      replace (Zlength l - 1 + 1 - 1) with (Zlength l - 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  rewrite H0, H1, H2, H3.
  reflexivity.
Qed.

Lemma suffix_exe_sublist_141 : forall l,
  5 <= Zlength l ->
  suffix_exe_z l ->
  sublist (Zlength l - 4) (Zlength l) l = [46; 101; 120; 101].
Proof.
  intros l Hlen [H0 [H1 [H2 H3]]].
  rewrite (sublist_split (Zlength l - 4) (Zlength l) (Zlength l - 3) l) by
    (rewrite Zlength_correct in *; lia).
  rewrite (sublist_split (Zlength l - 3) (Zlength l) (Zlength l - 2) l) by
    (rewrite Zlength_correct in *; lia).
  rewrite (sublist_split (Zlength l - 2) (Zlength l) (Zlength l - 1) l) by
    (rewrite Zlength_correct in *; lia).
  replace (sublist (Zlength l - 4) (Zlength l - 3) l)
    with [Znth (Zlength l - 4) l 0].
  2:{ replace (Zlength l - 3) with (Zlength l - 4 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 3) (Zlength l - 2) l)
    with [Znth (Zlength l - 3) l 0].
  2:{ replace (Zlength l - 2) with (Zlength l - 3 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 2) (Zlength l - 1) l)
    with [Znth (Zlength l - 2) l 0].
  2:{ replace (Zlength l - 1) with (Zlength l - 2 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 1) (Zlength l) l)
    with [Znth (Zlength l - 1) l 0].
  2:{ replace (Zlength l) with (Zlength l - 1 + 1) by lia.
      replace (Zlength l - 1 + 1 - 1) with (Zlength l - 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  rewrite H0, H1, H2, H3.
  reflexivity.
Qed.

Lemma suffix_dll_sublist_141 : forall l,
  5 <= Zlength l ->
  suffix_dll_z l ->
  sublist (Zlength l - 4) (Zlength l) l = [46; 100; 108; 108].
Proof.
  intros l Hlen [H0 [H1 [H2 H3]]].
  rewrite (sublist_split (Zlength l - 4) (Zlength l) (Zlength l - 3) l) by
    (rewrite Zlength_correct in *; lia).
  rewrite (sublist_split (Zlength l - 3) (Zlength l) (Zlength l - 2) l) by
    (rewrite Zlength_correct in *; lia).
  rewrite (sublist_split (Zlength l - 2) (Zlength l) (Zlength l - 1) l) by
    (rewrite Zlength_correct in *; lia).
  replace (sublist (Zlength l - 4) (Zlength l - 3) l)
    with [Znth (Zlength l - 4) l 0].
  2:{ replace (Zlength l - 3) with (Zlength l - 4 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 3) (Zlength l - 2) l)
    with [Znth (Zlength l - 3) l 0].
  2:{ replace (Zlength l - 2) with (Zlength l - 3 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 2) (Zlength l - 1) l)
    with [Znth (Zlength l - 2) l 0].
  2:{ replace (Zlength l - 1) with (Zlength l - 2 + 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  replace (sublist (Zlength l - 1) (Zlength l) l)
    with [Znth (Zlength l - 1) l 0].
  2:{ replace (Zlength l) with (Zlength l - 1 + 1) by lia.
      replace (Zlength l - 1 + 1 - 1) with (Zlength l - 1) by lia.
      symmetry. apply sublist_single. rewrite Zlength_correct in *; lia. }
  rewrite H0, H1, H2, H3.
  reflexivity.
Qed.

Lemma count_by_zb_nonneg : forall f l,
  0 <= count_by_zb f l.
Proof.
  intros f l.
  induction l; simpl; try lia.
  destruct (f a); lia.
Qed.

Lemma count_by_zb_le_len : forall f l,
  count_by_zb f l <= Zlength l.
Proof.
  intros f l.
  induction l; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons.
    destruct (f a); lia.
Qed.

Lemma count_by_zb_app_single : forall f l x,
  count_by_zb f (l ++ [x]) =
  count_by_zb f l + if f x then 1 else 0.
Proof.
  intros f l x.
  induction l; simpl.
  - lia.
  - rewrite IHl.
    destruct (f a); destruct (f x); lia.
Qed.

Lemma digit_count_upto_bounds : forall i l,
  0 <= i <= Zlength l ->
  0 <= digit_count_upto i l <= i.
Proof.
  intros i l Hi.
  unfold digit_count_upto.
  split.
  - apply count_by_zb_nonneg.
  - pose proof (count_by_zb_le_len is_digit_zb (sublist 0 i l)).
    rewrite Zlength_sublist in H by lia.
    lia.
Qed.

Lemma dot_count_upto_bounds : forall i l,
  0 <= i <= Zlength l ->
  0 <= dot_count_upto i l <= i.
Proof.
  intros i l Hi.
  unfold dot_count_upto.
  split.
  - apply count_by_zb_nonneg.
  - pose proof (count_by_zb_le_len is_dot_zb (sublist 0 i l)).
    rewrite Zlength_sublist in H by lia.
    lia.
Qed.

Lemma digit_count_upto_0 : forall l,
  digit_count_upto 0 l = 0.
Proof.
  intros l.
  unfold digit_count_upto.
  rewrite sublist_nil by lia.
  reflexivity.
Qed.

Lemma dot_count_upto_0 : forall l,
  dot_count_upto 0 l = 0.
Proof.
  intros l.
  unfold dot_count_upto.
  rewrite sublist_nil by lia.
  reflexivity.
Qed.

Lemma digit_count_upto_step_hit : forall i l,
  0 <= i < Zlength l ->
  is_digit_z (Znth i l 0) ->
  digit_count_upto (i + 1) l = digit_count_upto i l + 1.
Proof.
  intros i l Hi Hd.
  unfold digit_count_upto.
  rewrite (sublist_split 0 (i + 1) i l) by
    (rewrite Zlength_correct in Hi; lia).
  rewrite (sublist_single i l 0) by (rewrite Zlength_correct in Hi; lia).
  rewrite count_by_zb_app_single.
  unfold is_digit_z, is_digit_zb in *.
  replace (Z.leb 48 (Znth i l 0)) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Znth i l 0) 57) with true by (symmetry; apply Z.leb_le; lia).
  simpl.
  lia.
Qed.

Lemma digit_count_upto_step_miss : forall i l,
  0 <= i < Zlength l ->
  ~ is_digit_z (Znth i l 0) ->
  digit_count_upto (i + 1) l = digit_count_upto i l.
Proof.
  intros i l Hi Hd.
  unfold digit_count_upto.
  rewrite (sublist_split 0 (i + 1) i l) by
    (rewrite Zlength_correct in Hi; lia).
  rewrite (sublist_single i l 0) by (rewrite Zlength_correct in Hi; lia).
  rewrite count_by_zb_app_single.
  unfold is_digit_z, is_digit_zb in *.
  destruct (Z.leb_spec 48 (Znth i l 0));
    destruct (Z.leb_spec (Znth i l 0) 57); simpl; lia.
Qed.

Lemma dot_count_upto_step_hit : forall i l,
  0 <= i < Zlength l ->
  Znth i l 0 = 46 ->
  dot_count_upto (i + 1) l = dot_count_upto i l + 1.
Proof.
  intros i l Hi Hdot.
  unfold dot_count_upto.
  rewrite (sublist_split 0 (i + 1) i l) by
    (rewrite Zlength_correct in Hi; lia).
  rewrite (sublist_single i l 0) by (rewrite Zlength_correct in Hi; lia).
  rewrite count_by_zb_app_single.
  unfold is_dot_zb.
  rewrite Hdot, Z.eqb_refl.
  simpl.
  lia.
Qed.

Lemma dot_count_upto_step_miss : forall i l,
  0 <= i < Zlength l ->
  Znth i l 0 <> 46 ->
  dot_count_upto (i + 1) l = dot_count_upto i l.
Proof.
  intros i l Hi Hdot.
  unfold dot_count_upto.
  rewrite (sublist_split 0 (i + 1) i l) by
    (rewrite Zlength_correct in Hi; lia).
  rewrite (sublist_single i l 0) by (rewrite Zlength_correct in Hi; lia).
  rewrite count_by_zb_app_single.
  unfold is_dot_zb.
  replace (Z.eqb (Znth i l 0) 46) with false by
    (symmetry; apply Z.eqb_neq; lia).
  lia.
Qed.
