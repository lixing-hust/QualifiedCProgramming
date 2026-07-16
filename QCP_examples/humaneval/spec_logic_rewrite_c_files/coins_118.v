Load "../spec/118".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.
Require Import SimpleC.StdLib.string_lib.
Load "../StringClaude/string_bridge".
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition problem_118_pre_z (input : list Z) : Prop :=
  problem_118_pre (string_of_list_z input).

Definition problem_118_spec_z (input output : list Z) : Prop :=
  problem_118_spec (string_of_list_z input) (string_of_list_z output).

Definition is_vowel_z_118 (c : Z) : Prop :=
  c = 65 \/ c = 69 \/ c = 73 \/ c = 79 \/ c = 85 \/
  c = 97 \/ c = 101 \/ c = 105 \/ c = 111 \/ c = 117.

Definition is_alpha_z_118 (c : Z) : Prop :=
  65 <= c <= 90 \/ 97 <= c <= 122.

Definition is_consonant_z_118 (c : Z) : Prop :=
  is_alpha_z_118 c /\ ~ is_vowel_z_118 c.

Definition alpha_codes_z_118 (input : list Z) : Prop :=
  forall i, 0 <= i < Zlength input ->
    is_alpha_z_118 (Znth i input 0).

Definition closest_vowel_candidate_z_118
    (input : list Z) (i : Z) : Prop :=
  1 <= i < Zlength input - 1 /\
  is_consonant_z_118 (Znth (i - 1) input 0) /\
  is_vowel_z_118 (Znth i input 0) /\
  is_consonant_z_118 (Znth (i + 1) input 0).

Definition no_candidate_after_z_118
    (input : list Z) (i : Z) : Prop :=
  forall j, i < j < Zlength input - 1 ->
    ~ closest_vowel_candidate_z_118 input j.

Lemma problem_118_pre_z_alpha_codes : forall input,
  problem_118_pre_z input ->
  ascii_range_z input ->
  alpha_codes_z_118 input.
Proof.
  intros input Hpre Hrange i Hi.
  unfold problem_118_pre_z, problem_118_pre in Hpre.
  rewrite list_ascii_of_string_string_of_list_z in Hpre.
  apply Forall_forall with (x := ascii_of_z (Znth i input 0)) in Hpre.
  - unfold is_alpha in Hpre.
    rewrite nat_of_ascii_ascii_of_z in Hpre by (apply Hrange; lia).
    unfold is_alpha_z_118.
    lia.
  - apply in_map.
    unfold Znth.
    apply nth_In.
    rewrite <- z_to_nat_Zlength.
    lia.
Qed.

Lemma is_vowel_z_118_range : forall c,
  is_vowel_z_118 c -> 0 <= c <= 127.
Proof.
  intros c H.
  unfold is_vowel_z_118 in H.
  lia.
Qed.

Lemma alpha_codes_z_118_range : forall input i,
  alpha_codes_z_118 input ->
  0 <= i < Zlength input ->
  0 <= Znth i input 0 <= 127.
Proof.
  intros input i Halpha Hi.
  specialize (Halpha i Hi).
  unfold is_alpha_z_118 in Halpha.
  lia.
Qed.

Lemma no_candidate_after_z_118_start : forall input,
  no_candidate_after_z_118 input (Zlength input - 2).
Proof.
  unfold no_candidate_after_z_118.
  intros input j Hj.
  lia.
Qed.

Lemma no_candidate_after_z_118_step : forall input i,
  ~ closest_vowel_candidate_z_118 input i ->
  no_candidate_after_z_118 input i ->
  no_candidate_after_z_118 input (i - 1).
Proof.
  unfold no_candidate_after_z_118.
  intros input i Hnot Hafter j Hj.
  destruct (Z.eq_dec j i) as [-> | Hne].
  - exact Hnot.
  - apply Hafter.
    lia.
Qed.

Lemma c_string_inside_eq_118 : forall input i,
  0 <= i < Zlength input ->
  Znth i (c_string input) 0 = Znth i input 0.
Proof.
  intros input i Hi.
  apply c_string_Znth_inside.
  exact Hi.
Qed.

Lemma alpha_codes_c_string_range_118 : forall input i,
  alpha_codes_z_118 input ->
  0 <= i < Zlength input ->
  0 <= Znth i (c_string input) 0 <= 127.
Proof.
  intros input i Halpha Hi.
  rewrite c_string_inside_eq_118 by exact Hi.
  apply alpha_codes_z_118_range; assumption.
Qed.

Lemma candidate_z_118_from_c_string : forall input i,
  alpha_codes_z_118 input ->
  1 <= i < Zlength input - 1 ->
  ~ is_vowel_z_118 (Znth (i - 1) (c_string input) 0) ->
  is_vowel_z_118 (Znth i (c_string input) 0) ->
  ~ is_vowel_z_118 (Znth (i + 1) (c_string input) 0) ->
  closest_vowel_candidate_z_118 input i.
Proof.
  intros input i Halpha Hi Hleft Hcur Hright.
  unfold closest_vowel_candidate_z_118, is_consonant_z_118.
  split; [exact Hi |].
  rewrite !c_string_inside_eq_118 in * by lia.
  repeat split; try assumption.
  - apply Halpha. lia.
  - apply Halpha. lia.
Qed.

Lemma candidate_z_118_not_cur : forall input i,
  1 <= i < Zlength input - 1 ->
  ~ is_vowel_z_118 (Znth i (c_string input) 0) ->
  ~ closest_vowel_candidate_z_118 input i.
Proof.
  intros input i Hi Hnot Hcandidate.
  destruct Hcandidate as [_ [_ [Hcur _]]].
  rewrite c_string_inside_eq_118 in Hnot by lia.
  contradiction.
Qed.

Lemma candidate_z_118_not_right : forall input i,
  1 <= i < Zlength input - 1 ->
  is_vowel_z_118 (Znth (i + 1) (c_string input) 0) ->
  ~ closest_vowel_candidate_z_118 input i.
Proof.
  intros input i Hi Hvowel Hcandidate.
  destruct Hcandidate as [_ [_ [_ [_ Hnot]]]].
  rewrite c_string_inside_eq_118 in Hvowel by lia.
  contradiction.
Qed.

Lemma candidate_z_118_not_left : forall input i,
  1 <= i < Zlength input - 1 ->
  is_vowel_z_118 (Znth (i - 1) (c_string input) 0) ->
  ~ closest_vowel_candidate_z_118 input i.
Proof.
  intros input i Hi Hvowel Hcandidate.
  destruct Hcandidate as [_ [[_ Hnot] _]].
  rewrite c_string_inside_eq_118 in Hvowel by lia.
  contradiction.
Qed.

Lemma is_vowel_z_118_to_spec : forall c,
  is_vowel_z_118 c -> is_vowel (ascii_of_z c).
Proof.
  intros c H.
  unfold is_vowel_z_118 in H.
  repeat (destruct H as [-> | H]; [simpl; exact I |]).
  subst; simpl; exact I.
Qed.

Lemma spec_vowel_to_is_vowel_z_118 : forall c,
  0 <= c < 256 ->
  is_vowel (ascii_of_z c) ->
  is_vowel_z_118 c.
Proof.
  intros c Hrange Hvowel.
  unfold ascii_of_z in Hvowel.
  remember (ascii_of_nat (Z.to_nat c)) as a eqn:Ha.
  destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    simpl in Hvowel; try contradiction;
    apply (f_equal nat_of_ascii) in Ha;
    rewrite nat_ascii_embedding in Ha by lia;
    cbn in Ha;
    unfold is_vowel_z_118; lia.
Qed.

Lemma is_alpha_z_118_to_spec : forall c,
  0 <= c < 256 ->
  is_alpha_z_118 c ->
  is_alpha (ascii_of_z c).
Proof.
  intros c Hrange Halpha.
  unfold is_alpha.
  rewrite nat_of_ascii_ascii_of_z by exact Hrange.
  unfold is_alpha_z_118 in Halpha.
  lia.
Qed.

Lemma spec_alpha_to_is_alpha_z_118 : forall c,
  0 <= c < 256 ->
  is_alpha (ascii_of_z c) ->
  is_alpha_z_118 c.
Proof.
  intros c Hrange Halpha.
  unfold is_alpha in Halpha.
  rewrite nat_of_ascii_ascii_of_z in Halpha by exact Hrange.
  unfold is_alpha_z_118.
  lia.
Qed.

Lemma is_consonant_z_118_to_spec : forall c,
  0 <= c < 256 ->
  is_consonant_z_118 c ->
  is_consonant (ascii_of_z c).
Proof.
  intros c Hrange [Halpha Hnot].
  split.
  - apply is_alpha_z_118_to_spec; assumption.
  - intro Hvowel.
    apply Hnot.
    apply spec_vowel_to_is_vowel_z_118; assumption.
Qed.

Lemma spec_consonant_to_is_consonant_z_118 : forall c,
  0 <= c < 256 ->
  is_consonant (ascii_of_z c) ->
  is_consonant_z_118 c.
Proof.
  intros c Hrange [Halpha Hnot].
  split.
  - apply spec_alpha_to_is_alpha_z_118; assumption.
  - intro Hvowel.
    apply Hnot.
    apply is_vowel_z_118_to_spec.
    exact Hvowel.
Qed.

Lemma candidate_z_118_to_spec : forall input i,
  ascii_range_z input ->
  closest_vowel_candidate_z_118 input i ->
  vowel_between_consonants
    (string_of_list_z input) (Z.to_nat i)
    (ascii_of_z (Znth i input 0)).
Proof.
  intros input i Hrange [Hi [Hleft [Hcur Hright]]].
  unfold vowel_between_consonants.
  split.
  - rewrite string_of_list_z_length.
    rewrite <- z_to_nat_Zlength.
    lia.
  - exists (ascii_of_z (Znth (i - 1) input 0)).
    exists (ascii_of_z (Znth (i + 1) input 0)).
    split.
    + replace (Z.to_nat i - 1)%nat with (Z.to_nat (i - 1)) by lia.
      apply string_get_string_of_list_z_z.
      lia.
    + split.
      * apply string_get_string_of_list_z_z.
        lia.
      * split.
        -- replace (Z.to_nat i + 1)%nat with (Z.to_nat (i + 1)) by lia.
           apply string_get_string_of_list_z_z.
           lia.
        -- split.
           ++ apply is_consonant_z_118_to_spec.
              ** apply Hrange. lia.
              ** exact Hleft.
           ++ split.
              ** apply is_vowel_z_118_to_spec.
                 exact Hcur.
              ** apply is_consonant_z_118_to_spec.
                 --- apply Hrange. lia.
                 --- exact Hright.
Qed.

Lemma spec_candidate_to_candidate_z_118 : forall input i vowel,
  ascii_range_z input ->
  vowel_between_consonants (string_of_list_z input) i vowel ->
  closest_vowel_candidate_z_118 input (Z.of_nat i).
Proof.
  intros input i vowel Hrange [Hi [left [right Hcandidate]]].
  destruct Hcandidate as [Hleft_get [Hvowel_get [Hright_get Hprops]]].
  destruct Hprops as [Hleft [Hvowel Hright]].
  unfold closest_vowel_candidate_z_118.
  split.
  - rewrite string_of_list_z_length in Hi.
    rewrite <- z_to_nat_Zlength in Hi.
    lia.
  - assert (Hzi : 1 <= Z.of_nat i < Zlength input - 1).
    { rewrite string_of_list_z_length in Hi.
      rewrite <- z_to_nat_Zlength in Hi.
      lia. }
    assert (Hget_left :
      String.get (i - 1)%nat (string_of_list_z input) =
      Some (ascii_of_z (Znth (Z.of_nat i - 1) input 0))).
    { replace (i - 1)%nat with (Z.to_nat (Z.of_nat i - 1)) by lia.
      apply string_get_string_of_list_z_z. lia. }
    pose proof
      (string_get_string_of_list_z_z input (Z.of_nat i) ltac:(lia))
      as Hget_cur.
    rewrite Nat2Z.id in Hget_cur.
    assert (Hget_right :
      String.get (i + 1)%nat (string_of_list_z input) =
      Some (ascii_of_z (Znth (Z.of_nat i + 1) input 0))).
    { replace (i + 1)%nat with (Z.to_nat (Z.of_nat i + 1)) by lia.
      apply string_get_string_of_list_z_z. lia. }
    rewrite Hleft_get in Hget_left.
    rewrite Hvowel_get in Hget_cur.
    rewrite Hright_get in Hget_right.
    inversion Hget_left; inversion Hget_cur; inversion Hget_right; subst.
    split.
    + apply spec_consonant_to_is_consonant_z_118.
      * apply Hrange. lia.
      * exact Hleft.
    + split.
      * apply spec_vowel_to_is_vowel_z_118.
        -- apply Hrange. lia.
        -- exact Hvowel.
      * apply spec_consonant_to_is_consonant_z_118.
        -- apply Hrange. lia.
        -- exact Hright.
Qed.

Lemma problem_118_spec_z_found : forall input i,
  ascii_range_z input ->
  closest_vowel_candidate_z_118 input i ->
  no_candidate_after_z_118 input i ->
  problem_118_spec_z input [Znth i input 0].
Proof.
  intros input i Hrange Hcandidate Hafter.
  unfold problem_118_spec_z, problem_118_spec.
  left.
  exists (Z.to_nat i), (ascii_of_z (Znth i input 0)).
  split.
  - apply candidate_z_118_to_spec; assumption.
  - split.
    + intros j other Hij Hbad.
      apply (Hafter (Z.of_nat j)).
      * destruct Hbad as [Hj _].
        rewrite string_of_list_z_length in Hj.
        rewrite <- z_to_nat_Zlength in Hj.
        destruct Hcandidate as [Hi _].
        lia.
      * apply spec_candidate_to_candidate_z_118 with (vowel := other);
          assumption.
    + reflexivity.
Qed.

Lemma problem_118_spec_z_not_found : forall input,
  ascii_range_z input ->
  no_candidate_after_z_118 input 0 ->
  problem_118_spec_z input [].
Proof.
  intros input Hrange Hnone.
  unfold problem_118_spec_z, problem_118_spec.
  right.
  split.
  - intros i vowel Hbad.
    apply (Hnone (Z.of_nat i)).
    + destruct Hbad as [Hi _].
      rewrite string_of_list_z_length in Hi.
      rewrite <- z_to_nat_Zlength in Hi.
      lia.
    + apply spec_candidate_to_candidate_z_118 with (vowel := vowel);
        assumption.
  - reflexivity.
Qed.

Lemma problem_118_spec_z_short : forall input,
  ascii_range_z input ->
  Zlength input < 3 ->
  problem_118_spec_z input [].
Proof.
  intros input Hrange Hshort.
  apply problem_118_spec_z_not_found; [exact Hrange |].
  unfold no_candidate_after_z_118.
  intros j Hj Hcandidate.
  destruct Hcandidate as [Hbounds _].
  lia.
Qed.
