Load "../spec/54".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition problem_54_pre_z (s0 s1 : list Z) : Prop :=
  problem_54_pre (string_of_list_z s0) (string_of_list_z s1).

Definition no_zero_z (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> Znth i s 0 <> 0.

Definition char_in_z (c : Z) (s : list Z) : Prop :=
  In c s.

Definition same_chars_prefix_z (i : Z) (s0 s1 : list Z) : Prop :=
  forall k, 0 <= k < i -> char_in_z (Znth k s0 0) s1.

Definition same_chars_all_z (s0 s1 : list Z) : Prop :=
  same_chars_prefix_z (Zlength s0) s0 s1.

Definition same_chars_set_z (s0 s1 : list Z) : Prop :=
  same_chars_all_z s0 s1 /\ same_chars_all_z s1 s0.

Definition problem_54_spec_z (s0 s1 : list Z) (output : Z) : Prop :=
  problem_54_spec (string_of_list_z s0) (string_of_list_z s1) (bool_of_z output).

Lemma Znth_In_range : forall (l : list Z) k d,
  0 <= k < Zlength l ->
  In (Znth k l d) l.
Proof.
  intros l k d Hk.
  unfold Znth.
  apply nth_In.
  rewrite <- z_to_nat_Zlength.
  lia.
Qed.

Lemma ascii_of_z_inj_range_54 : forall a b,
  0 <= a < 256 ->
  0 <= b < 256 ->
  ascii_of_z a = ascii_of_z b ->
  a = b.
Proof.
  intros a b Ha Hb Heq.
  apply (f_equal nat_of_ascii) in Heq.
  repeat rewrite nat_of_ascii_ascii_of_z in Heq by lia.
  lia.
Qed.

Lemma same_chars_set_z_to_ascii_set : forall s0 s1,
  same_chars_set_z s0 s1 ->
  forall c : ascii,
    In c (list_ascii_of_string (string_of_list_z s0)) <->
    In c (list_ascii_of_string (string_of_list_z s1)).
Proof.
  intros s0 s1 [Hall01 Hall10] c.
  repeat rewrite list_ascii_of_string_string_of_list_z.
  split; intros Hin.
  - apply in_map_iff in Hin.
    destruct Hin as [z [Hzc HzIn]].
    apply in_map_iff.
    exists z.
    split; [assumption |].
    destruct (In_nth s0 z 0 HzIn) as [n [Hn Hnth]].
    subst z.
    unfold same_chars_all_z, same_chars_prefix_z, char_in_z in Hall01.
    specialize (Hall01 (Z.of_nat n)).
    unfold Znth in Hall01.
    rewrite Nat2Z.id in Hall01.
    apply Hall01.
    rewrite Zlength_correct; lia.
  - apply in_map_iff in Hin.
    destruct Hin as [z [Hzc HzIn]].
    apply in_map_iff.
    exists z.
    split; [assumption |].
    destruct (In_nth s1 z 0 HzIn) as [n [Hn Hnth]].
    subst z.
    unfold same_chars_all_z, same_chars_prefix_z, char_in_z in Hall10.
    specialize (Hall10 (Z.of_nat n)).
    unfold Znth in Hall10.
    rewrite Nat2Z.id in Hall10.
    apply Hall10.
    rewrite Zlength_correct; lia.
Qed.

Lemma ascii_set_missing_left_false : forall s0 s1 i,
  ascii_range_z s0 ->
  ascii_range_z s1 ->
  0 <= i < Zlength s0 ->
  ~ char_in_z (Znth i s0 0) s1 ->
  ~ (forall c : ascii,
      In c (list_ascii_of_string (string_of_list_z s0)) <->
      In c (list_ascii_of_string (string_of_list_z s1))).
Proof.
  intros s0 s1 i Hr0 Hr1 Hi Hnot Hall.
  specialize (Hall (ascii_of_z (Znth i s0 0))) as [Hin01 _].
  repeat rewrite list_ascii_of_string_string_of_list_z in Hin01.
  assert (Hin0 : In (ascii_of_z (Znth i s0 0)) (map ascii_of_z s0)).
  {
    apply in_map.
    apply Znth_In_range. lia.
  }
  specialize (Hin01 Hin0).
  apply in_map_iff in Hin01.
  destruct Hin01 as [z [Hz Hzin]].
  apply Hnot.
  assert (Hzrange : 0 <= z < 256).
  {
    destruct (In_nth s1 z 0 Hzin) as [k [Hk Hznth]].
    rewrite <- Hznth.
    unfold ascii_range_z in Hr1.
    specialize (Hr1 (Z.of_nat k)).
    unfold Znth in Hr1.
    rewrite Nat2Z.id in Hr1.
    apply Hr1.
    rewrite Zlength_correct; lia.
  }
  replace (Znth i s0 0) with z.
  - exact Hzin.
  - pose proof (ascii_of_z_inj_range_54 z (Znth i s0 0)
      Hzrange (Hr0 i Hi) Hz) as Heq.
    exact Heq.
Qed.

Lemma ascii_set_missing_right_false : forall s0 s1 i,
  ascii_range_z s0 ->
  ascii_range_z s1 ->
  0 <= i < Zlength s1 ->
  ~ char_in_z (Znth i s1 0) s0 ->
  ~ (forall c : ascii,
      In c (list_ascii_of_string (string_of_list_z s0)) <->
      In c (list_ascii_of_string (string_of_list_z s1))).
Proof.
  intros s0 s1 i Hr0 Hr1 Hi Hnot Hall.
  specialize (Hall (ascii_of_z (Znth i s1 0))) as [_ Hin10].
  repeat rewrite list_ascii_of_string_string_of_list_z in Hin10.
  assert (Hin1 : In (ascii_of_z (Znth i s1 0)) (map ascii_of_z s1)).
  {
    apply in_map.
    apply Znth_In_range. lia.
  }
  specialize (Hin10 Hin1).
  apply in_map_iff in Hin10.
  destruct Hin10 as [z [Hz Hzin]].
  apply Hnot.
  assert (Hzrange : 0 <= z < 256).
  {
    destruct (In_nth s0 z 0 Hzin) as [k [Hk Hznth]].
    rewrite <- Hznth.
    unfold ascii_range_z in Hr0.
    specialize (Hr0 (Z.of_nat k)).
    unfold Znth in Hr0.
    rewrite Nat2Z.id in Hr0.
    apply Hr0.
    rewrite Zlength_correct; lia.
  }
  replace (Znth i s1 0) with z.
  - exact Hzin.
  - pose proof (ascii_of_z_inj_range_54 z (Znth i s1 0)
      Hzrange (Hr1 i Hi) Hz) as Heq.
    exact Heq.
Qed.

Lemma same_chars_prefix_zero : forall s0 s1,
  same_chars_prefix_z 0 s0 s1.
Proof.
  unfold same_chars_prefix_z.
  intros; lia.
Qed.

Lemma same_chars_prefix_step : forall i s0 s1,
  0 <= i ->
  same_chars_prefix_z i s0 s1 ->
  char_in_z (Znth i s0 0) s1 ->
  same_chars_prefix_z (i + 1) s0 s1.
Proof.
  unfold same_chars_prefix_z.
  intros i s0 s1 Hi Hprefix Hin k Hk.
  destruct (Z.eq_dec k i) as [-> | Hne].
  - exact Hin.
  - apply Hprefix; lia.
Qed.

Lemma same_chars_all_intro : forall s0 s1,
  same_chars_prefix_z (Zlength s0) s0 s1 ->
  same_chars_all_z s0 s1.
Proof.
  intros; exact H.
Qed.

Lemma problem_54_spec_z_true : forall s0 s1,
  same_chars_all_z s0 s1 ->
  same_chars_all_z s1 s0 ->
  problem_54_spec_z s0 s1 1.
Proof.
  intros s0 s1 Hall01 Hall10.
  unfold problem_54_spec_z, problem_54_spec, bool_of_z.
  simpl.
  split.
  - intros _. apply same_chars_set_z_to_ascii_set.
    split; assumption.
  - intros _. reflexivity.
Qed.

Lemma problem_54_spec_z_false_left : forall i s0 s1,
  ascii_range_z s0 ->
  ascii_range_z s1 ->
  0 <= i < Zlength s0 ->
  ~ char_in_z (Znth i s0 0) s1 ->
  problem_54_spec_z s0 s1 0.
Proof.
  unfold problem_54_spec_z, same_chars_set_z, same_chars_all_z,
         same_chars_prefix_z.
  intros i s0 s1 Hr0 Hr1 Hi Hnot.
  unfold problem_54_spec, bool_of_z.
  simpl.
  split; intros H.
  - discriminate.
  - exfalso.
    eapply ascii_set_missing_left_false.
    + exact Hr0.
    + exact Hr1.
    + exact Hi.
    + exact Hnot.
    + exact H.
Qed.

Lemma problem_54_spec_z_false_right : forall i s0 s1,
  ascii_range_z s0 ->
  ascii_range_z s1 ->
  0 <= i < Zlength s1 ->
  ~ char_in_z (Znth i s1 0) s0 ->
  problem_54_spec_z s0 s1 0.
Proof.
  unfold problem_54_spec_z, same_chars_set_z, same_chars_all_z,
         same_chars_prefix_z.
  intros i s0 s1 Hr0 Hr1 Hi Hnot.
  unfold problem_54_spec, bool_of_z.
  simpl.
  split; intros H.
  - discriminate.
  - exfalso.
    eapply ascii_set_missing_right_false.
    + exact Hr0.
    + exact Hr1.
    + exact Hi.
    + exact Hnot.
    + exact H.
Qed.
