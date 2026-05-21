Load "../spec/27".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition is_lower_z (c : Z) : Prop :=
  97 <= c <= 122.

Definition is_upper_z (c : Z) : Prop :=
  65 <= c <= 90.

Definition flip_char_z (c : Z) : Z :=
  if (Z.leb 97 c) && (Z.leb c 122) then c - 32
  else if (Z.leb 65 c) && (Z.leb c 90) then c + 32
  else c.

Definition char_range_z (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition problem_27_pre_z (s : list Z) : Prop :=
  problem_27_pre (string_of_list_z s).

Definition problem_27_spec_z (input output : list Z) : Prop :=
  problem_27_spec (string_of_list_z input) (string_of_list_z output).

Lemma flip_char_range_z : forall c,
  0 <= c <= 127 ->
  0 <= flip_char_z c <= 127.
Proof.
  unfold flip_char_z.
  intros c Hrange.
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      destruct (Z.leb_spec x y); simpl
  end; lia.
Qed.

Lemma IsLow_ascii_of_z_to_is_lower_z : forall c,
  0 <= c <= 127 ->
  IsLow (ascii_of_z c) ->
  is_lower_z c.
Proof.
  unfold IsLow, is_lower_z, ascii_of_z.
  intros c Hrange H.
  rewrite nat_ascii_embedding in H by lia.
  cbn in H.
  lia.
Qed.

Lemma IsUp_ascii_of_z_to_is_upper_z : forall c,
  0 <= c <= 127 ->
  IsUp (ascii_of_z c) ->
  is_upper_z c.
Proof.
  unfold IsUp, is_upper_z, ascii_of_z.
  intros c Hrange H.
  rewrite nat_ascii_embedding in H by lia.
  cbn in H.
  lia.
Qed.

Lemma Upper_ascii_of_z_lower : forall c,
  is_lower_z c ->
  Upper (ascii_of_z c) = ascii_of_z (flip_char_z c).
Proof.
  unfold is_lower_z, flip_char_z.
  intros c Hc.
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
  end.
  simpl.
  unfold Upper, ascii_of_z.
  rewrite nat_ascii_embedding by lia.
  destruct ((nat_of_ascii "a" <=? Z.to_nat c)%nat &&
            (Z.to_nat c <=? nat_of_ascii "z")%nat) eqn:Hcase.
  - replace (Z.to_nat (c - 32)) with (Z.to_nat c - 32)%nat by lia.
    reflexivity.
  - apply andb_false_iff in Hcase.
    destruct Hcase as [Hcase | Hcase];
      apply Nat.leb_gt in Hcase; cbn in Hcase; lia.
Qed.

Lemma Lower_ascii_of_z_upper : forall c,
  is_upper_z c ->
  Lower (ascii_of_z c) = ascii_of_z (flip_char_z c).
Proof.
  unfold is_upper_z, flip_char_z.
  intros c Hc.
  replace (Z.leb 97 c) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb 65 c) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb c 90) with true by (symmetry; apply Z.leb_le; lia).
  simpl.
  unfold Lower, ascii_of_z.
  rewrite nat_ascii_embedding by lia.
  destruct ((nat_of_ascii "A" <=? Z.to_nat c)%nat &&
            (Z.to_nat c <=? nat_of_ascii "Z")%nat) eqn:Hcase.
  - replace (Z.to_nat (c + 32)) with (Z.to_nat c + 32)%nat by lia.
    reflexivity.
  - apply andb_false_iff in Hcase.
    destruct Hcase as [Hcase | Hcase];
      apply Nat.leb_gt in Hcase; cbn in Hcase; lia.
Qed.

Lemma flip_char_z_other : forall c,
  0 <= c <= 127 ->
  ~ IsLow (ascii_of_z c) ->
  ~ IsUp (ascii_of_z c) ->
  flip_char_z c = c.
Proof.
  intros c Hrange Hnotlow Hnotup.
  unfold flip_char_z.
  destruct (Z.leb_spec 97 c); simpl.
  - destruct (Z.leb_spec c 122); simpl.
    + exfalso. apply Hnotlow.
      unfold IsLow, ascii_of_z.
      rewrite nat_ascii_embedding by lia.
      cbn. lia.
    + destruct (Z.leb_spec 65 c); simpl.
      * destruct (Z.leb_spec c 90); simpl; [lia | reflexivity].
      * reflexivity.
  - destruct (Z.leb_spec 65 c); simpl.
    + destruct (Z.leb_spec c 90); simpl.
      * exfalso. apply Hnotup.
        unfold IsUp, ascii_of_z.
        rewrite nat_ascii_embedding by lia.
        cbn. lia.
      * reflexivity.
    + reflexivity.
Qed.

Lemma problem_27_spec_z_intro : forall input output n,
  char_range_z input ->
  Zlength input = n ->
  Zlength output = n ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = flip_char_z (Znth k input 0)) ->
  problem_27_spec_z input output.
Proof.
  intros input output n Hrange Hin Hout Hpoint.
  unfold problem_27_spec_z.
  unfold problem_27_spec.
    split.
    + apply Nat2Z.inj.
      repeat rewrite string_of_list_z_length.
      repeat rewrite <- Zlength_correct.
      lia.
    + intros i c Hi Hget.
      assert (Hiz : 0 <= Z.of_nat i < Zlength input).
      {
        split; [lia |].
        apply Nat2Z.inj_lt in Hi.
        rewrite string_of_list_z_length in Hi.
        rewrite <- Zlength_correct in Hi.
        lia.
      }
      pose proof (string_get_string_of_list_z_z input (Z.of_nat i) Hiz) as Hin_get.
      rewrite Nat2Z.id in Hin_get.
      rewrite Hget in Hin_get.
      inversion Hin_get; subst c; clear Hin_get.
      pose proof (Hrange (Z.of_nat i) Hiz) as Hchar.
      assert (Houtz : 0 <= Z.of_nat i < Zlength output) by lia.
      replace (String.get i (string_of_list_z output)) with
        (String.get (Z.to_nat (Z.of_nat i)) (string_of_list_z output))
        by now rewrite Nat2Z.id.
      rewrite (string_get_string_of_list_z_z output (Z.of_nat i) Houtz).
      rewrite Hpoint by lia.
      split.
      * intro Hlow.
        pose proof (IsLow_ascii_of_z_to_is_lower_z _ Hchar Hlow) as Hzlow.
        rewrite <- Upper_ascii_of_z_lower by exact Hzlow.
        reflexivity.
      * split.
        -- intro Hup.
           pose proof (IsUp_ascii_of_z_to_is_upper_z _ Hchar Hup) as Hzup.
           rewrite <- Lower_ascii_of_z_upper by exact Hzup.
           reflexivity.
        -- intros [Hnotlow Hnotup].
           rewrite (flip_char_z_other _ Hchar Hnotlow Hnotup).
           reflexivity.
Qed.
