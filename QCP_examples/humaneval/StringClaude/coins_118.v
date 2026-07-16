Load "../spec/118".

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

Definition is_vowel_z (x : Z) : Prop :=
  x = 65 \/ x = 69 \/ x = 73 \/ x = 79 \/ x = 85 \/
  x = 97 \/ x = 101 \/ x = 105 \/ x = 111 \/ x = 117.

Definition is_alpha_z (x : Z) : Prop :=
  65 <= x <= 90 \/ 97 <= x <= 122.

Definition is_consonant_z (x : Z) : Prop :=
  is_alpha_z x /\ ~ is_vowel_z x.

Definition alpha_range_z (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> is_alpha_z (Znth i l 0).

Definition closest_vowel_candidate_z (l : list Z) (i : Z) : Prop :=
  1 <= i < Zlength l - 1 /\
  is_consonant_z (Znth (i - 1) l 0) /\
  is_vowel_z (Znth i l 0) /\
  is_consonant_z (Znth (i + 1) l 0).

Definition no_candidate_after_z (i : Z) (l : list Z) : Prop :=
  forall j, i < j < Zlength l - 1 -> ~ closest_vowel_candidate_z l j.

Definition problem_118_pre_z (word : list Z) : Prop :=
  problem_118_pre (string_of_list_z word).

Definition problem_118_spec_z (word output : list Z) : Prop :=
  problem_118_spec (string_of_list_z word) (string_of_list_z output).

Lemma is_vowel_z_to_is_vowel : forall x,
  is_vowel_z x ->
  is_vowel (ascii_of_z x).
Proof.
  intros x H.
  unfold is_vowel_z in H.
  repeat (destruct H as [-> | H]; [simpl; exact I |]).
  subst; simpl; exact I.
Qed.

Lemma is_alpha_z_to_is_alpha : forall x,
  0 <= x < 256 ->
  is_alpha_z x ->
  is_alpha (ascii_of_z x).
Proof.
  intros x Hrange Halpha.
  unfold is_alpha_z in Halpha.
  unfold is_alpha.
  rewrite nat_of_ascii_ascii_of_z by exact Hrange.
  lia.
Qed.

Lemma is_vowel_to_is_vowel_z : forall x,
  0 <= x < 256 ->
  is_vowel (ascii_of_z x) ->
  is_vowel_z x.
Proof.
  intros x Hrange Hv.
  unfold ascii_of_z in Hv.
  remember (ascii_of_nat (Z.to_nat x)) as a eqn:Ha.
  destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7; simpl in Hv; try contradiction;
    apply (f_equal nat_of_ascii) in Ha;
    rewrite nat_ascii_embedding in Ha by lia;
    cbn in Ha;
    unfold is_vowel_z; lia.
Qed.

Lemma is_consonant_z_to_is_consonant : forall x,
  0 <= x < 256 ->
  is_consonant_z x ->
  is_consonant (ascii_of_z x).
Proof.
  intros x Hrange [Halpha Hnot_vowel].
  unfold is_consonant.
  split.
  - apply is_alpha_z_to_is_alpha; assumption.
  - intro Hv.
    apply Hnot_vowel.
    apply is_vowel_to_is_vowel_z; assumption.
Qed.

Lemma candidate_z_to_spec_candidate : forall l i,
  ascii_range_z l ->
  closest_vowel_candidate_z l i ->
  exists c_prev c_curr c_next,
    String.get (Z.to_nat (i - 1)) (string_of_list_z l) = Some c_prev /\
    String.get (Z.to_nat i) (string_of_list_z l) = Some c_curr /\
    String.get (Z.to_nat (i + 1)) (string_of_list_z l) = Some c_next /\
    is_consonant c_prev /\ is_vowel c_curr /\ is_consonant c_next /\
    c_curr = ascii_of_z (Znth i l 0).
Proof.
  intros l i Hrange Hcand.
  unfold closest_vowel_candidate_z in Hcand.
  destruct Hcand as [Hi [Hprev [Hcur Hnext]]].
  exists (ascii_of_z (Znth (i - 1) l 0)).
  exists (ascii_of_z (Znth i l 0)).
  exists (ascii_of_z (Znth (i + 1) l 0)).
  split.
  - rewrite string_get_string_of_list_z_z; [reflexivity | lia].
  - split.
    + rewrite string_get_string_of_list_z_z; [reflexivity | lia].
    + split.
      * rewrite string_get_string_of_list_z_z; [reflexivity | lia].
      * split.
        -- apply is_consonant_z_to_is_consonant.
           ++ apply Hrange. lia.
           ++ exact Hprev.
        -- split.
           ++ apply is_vowel_z_to_is_vowel. exact Hcur.
           ++ split.
              ** apply is_consonant_z_to_is_consonant.
                 --- apply Hrange. lia.
                 --- exact Hnext.
              ** reflexivity.
Qed.

Lemma spec_candidate_to_candidate_z : forall l i c_prev c_curr c_next,
  ascii_range_z l ->
  alpha_range_z l ->
  1 <= Z.of_nat i < Zlength l - 1 ->
  String.get (i - 1) (string_of_list_z l) = Some c_prev ->
  String.get i (string_of_list_z l) = Some c_curr ->
  String.get (i + 1) (string_of_list_z l) = Some c_next ->
  is_consonant c_prev ->
  is_vowel c_curr ->
  is_consonant c_next ->
  closest_vowel_candidate_z l (Z.of_nat i).
Proof.
  intros l i c_prev c_curr c_next Hrange Halpha Hi Hprev_get Hcur_get Hnext_get
         Hprev Hcur Hnext.
  unfold closest_vowel_candidate_z.
  split; [lia |].
  split.
  - unfold is_consonant_z.
    split.
    + apply Halpha. lia.
    + intro Hvz.
      destruct Hprev as [_ Hnot].
      apply Hnot.
      assert (Hget :
        String.get (Z.to_nat (Z.of_nat i - 1)) (string_of_list_z l) =
        Some (ascii_of_z (Znth (Z.of_nat i - 1) l 0))).
      { apply string_get_string_of_list_z_z. lia. }
      replace (Z.to_nat (Z.of_nat i - 1)) with (i - 1)%nat in Hget by lia.
      rewrite Hprev_get in Hget. inversion Hget; subst.
      apply is_vowel_z_to_is_vowel. exact Hvz.
  - split.
    + assert (Hget :
        String.get (Z.to_nat (Z.of_nat i)) (string_of_list_z l) =
        Some (ascii_of_z (Znth (Z.of_nat i) l 0))).
      { apply string_get_string_of_list_z_z. lia. }
      rewrite Nat2Z.id in Hget.
      rewrite Hcur_get in Hget. inversion Hget; subst.
      apply is_vowel_to_is_vowel_z.
      * apply Hrange. lia.
      * exact Hcur.
    + unfold is_consonant_z.
      split.
      * apply Halpha. lia.
      * intro Hvz.
        destruct Hnext as [_ Hnot].
        apply Hnot.
        assert (Hget :
          String.get (Z.to_nat (Z.of_nat i + 1)) (string_of_list_z l) =
          Some (ascii_of_z (Znth (Z.of_nat i + 1) l 0))).
        { apply string_get_string_of_list_z_z. lia. }
        replace (Z.to_nat (Z.of_nat i + 1)) with (i + 1)%nat in Hget by lia.
        rewrite Hnext_get in Hget. inversion Hget; subst.
        apply is_vowel_z_to_is_vowel. exact Hvz.
Qed.

Lemma no_candidate_after_step : forall i l,
  ~ closest_vowel_candidate_z l i ->
  no_candidate_after_z i l ->
  no_candidate_after_z (i - 1) l.
Proof.
  unfold no_candidate_after_z.
  intros i l Hnot Hafter j Hj.
  destruct (Z.eq_dec j i) as [-> | Hne].
  - exact Hnot.
  - apply Hafter. lia.
Qed.

Lemma no_candidate_after_start : forall l,
  no_candidate_after_z (Zlength l - 2) l.
Proof.
  unfold no_candidate_after_z.
  intros l j Hj.
  lia.
Qed.

Lemma problem_118_spec_z_found : forall l i,
  ascii_range_z l ->
  alpha_range_z l ->
  closest_vowel_candidate_z l i ->
  no_candidate_after_z i l ->
  problem_118_spec_z l [Znth i l 0].
Proof.
  intros l i Hrange Halpha Hcand Hafter.
  unfold problem_118_spec_z, problem_118_spec.
  left.
  exists (Z.to_nat i).
  exists (ascii_of_z (Znth i l 0)).
  unfold closest_vowel_candidate_z in Hcand.
  destruct Hcand as [Hi Hrest].
  split.
  - unfold vowel_between_consonants.
    split.
    + rewrite string_of_list_z_length.
      rewrite <- z_to_nat_Zlength.
      lia.
    + destruct Hrest as [Hprev [Hcur Hnext]].
      pose proof (candidate_z_to_spec_candidate l i Hrange
        (conj Hi (conj Hprev (conj Hcur Hnext)))) as Hspec.
      destruct Hspec as [c_prev [c_curr [c_next Hspec]]].
      exists c_prev, c_next.
      destruct Hspec as [H1 [H2 [H3 [H4 [H5 [H6 Hcurr]]]]]].
      split; [replace (Z.to_nat i - 1)%nat with (Z.to_nat (i - 1)) by lia; exact H1 |].
      split; [rewrite <- Hcurr; exact H2 |].
      split; [replace (Z.to_nat i + 1)%nat with (Z.to_nat (i + 1)) by lia; exact H3 |].
      split; [exact H4 |].
      split; [rewrite <- Hcurr; exact H5 |].
      exact H6.
  - split.
    + intros j other Hij Hbad.
      unfold vowel_between_consonants in Hbad.
      destruct Hbad as [Hj [j_prev [j_next [Hprev [Hcur [Hnext Hcons]]]]]].
      destruct Hcons as [Hcprev [Hvother Hcnext]].
      apply (Hafter (Z.of_nat j)).
      * rewrite string_of_list_z_length in Hj.
        rewrite <- z_to_nat_Zlength in Hj.
        lia.
      * eapply spec_candidate_to_candidate_z with
          (c_prev := j_prev) (c_curr := other) (c_next := j_next);
          try eassumption.
        rewrite string_of_list_z_length in Hj.
        rewrite <- z_to_nat_Zlength in Hj.
        lia.
    + simpl. reflexivity.
Qed.

Lemma problem_118_spec_z_not_found : forall l,
  ascii_range_z l ->
  alpha_range_z l ->
  no_candidate_after_z 0 l ->
  problem_118_spec_z l [].
Proof.
  intros l Hrange Halpha Hnone.
  unfold problem_118_spec_z, problem_118_spec.
  right.
  split.
  - intros i vowel Hbad.
    unfold vowel_between_consonants in Hbad.
    destruct Hbad as [Hi [c_prev [c_next [Hprev [Hcur [Hnext Hcons]]]]]].
    destruct Hcons as [Hcprev [Hvvowel Hcnext]].
    apply (Hnone (Z.of_nat i)).
    + rewrite string_of_list_z_length in Hi.
      rewrite <- z_to_nat_Zlength in Hi.
      lia.
    + apply spec_candidate_to_candidate_z with
        (c_prev := c_prev) (c_curr := vowel) (c_next := c_next);
        try assumption.
      rewrite string_of_list_z_length in Hi.
      rewrite <- z_to_nat_Zlength in Hi.
      lia.
  - reflexivity.
Qed.
