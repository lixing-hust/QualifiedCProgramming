Load "../spec/50".

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

Definition lower_char_z (c : Z) : Prop := 97 <= c <= 122.

Definition problem_50_pre_z (s : list Z) : Prop :=
  problem_50_pre (string_of_list_z s).

Definition encode_shift_char_z (c : Z) : Z :=
  Z.rem (c + 5 - 97) 26 + 97.

Definition decode_shift_char_z (c : Z) : Z :=
  Z.rem (c + 21 - 97) 26 + 97.

Definition problem_50_encode_spec_z (input output : list Z) : Prop :=
  Zlength output = Zlength input /\
  forall k, 0 <= k < Zlength input ->
    Znth k output 0 = encode_shift_char_z (Znth k input 0).

Definition problem_50_spec_z (input output : list Z) : Prop :=
  problem_50_spec (string_of_list_z input) (string_of_list_z output).

Definition problem_50_decode_spec_z (input output : list Z) : Prop :=
  problem_50_spec_z input output.

Lemma shift_output_range : forall x shift,
  0 <= x + shift - 97 ->
  0 <= shift ->
  shift <= 25 ->
  lower_char_z x ->
  0 <= Z.rem (x + shift - 97) 26 + 97 <= 127.
Proof.
  intros x shift Hnonneg Hshift_lo Hshift_hi Hlower.
  unfold lower_char_z in Hlower.
  pose proof (Z.rem_bound_pos (x + shift - 97) 26 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma encode_shift_output_range : forall x,
  lower_char_z x ->
  0 <= encode_shift_char_z x <= 127.
Proof.
  intros x Hlower.
  unfold encode_shift_char_z.
  apply shift_output_range; unfold lower_char_z in *; lia.
Qed.

Lemma decode_shift_output_range : forall x,
  lower_char_z x ->
  0 <= decode_shift_char_z x <= 127.
Proof.
  intros x Hlower.
  unfold decode_shift_char_z.
  apply shift_output_range; unfold lower_char_z in *; lia.
Qed.

Lemma decode_shift_char_z_correct : forall x,
  lower_char_z x ->
  ascii_of_z (decode_shift_char_z x) = decode_char (ascii_of_z x).
Proof.
  intros x Hx.
  unfold decode_shift_char_z, decode_char, ascii_of_z, lower_char_z in *.
  rewrite nat_ascii_embedding by lia.
  rewrite Z.rem_mod_nonneg by lia.
  replace (Z.to_nat ((x + 21 - 97) mod 26 + 97))
    with (((Z.to_nat x - 97 + 21) mod 26) + 97)%nat.
  - change (nat_of_ascii "a") with 97%nat.
    rewrite Nat.add_comm.
    reflexivity.
  - rewrite Z2Nat.inj_add.
    + rewrite Z2Nat.inj_mod by lia.
      replace (Z.to_nat (x + 21 - 97)) with (Z.to_nat x - 97 + 21)%nat by lia.
      reflexivity.
    + pose proof (Z.mod_pos_bound (x + 21 - 97) 26 ltac:(lia)); lia.
    + lia.
Qed.

Lemma all_lowercase_ascii_get_50 : forall s i c,
  all_lowercase_ascii s ->
  String.get i s = Some c ->
  is_lowercase_ascii c.
Proof.
  induction s as [| ch rest IH]; intros i c Hlower Hget.
  - destruct i; simpl in Hget; discriminate.
  - destruct Hlower as [Hch Hrest].
    destruct i as [| i].
    + simpl in Hget. inversion Hget. subst. exact Hch.
    + simpl in Hget. eapply IH; eauto.
Qed.

Lemma lower_char_z_from_problem_50_pre : forall s k,
  problem_50_pre_z s ->
  ascii_range_z s ->
  0 <= k < Zlength s ->
  lower_char_z (Znth k s 0).
Proof.
  intros s k Hpre Hrange Hk.
  unfold problem_50_pre_z, problem_50_pre in Hpre.
  pose proof (all_lowercase_ascii_get_50
    (string_of_list_z s) (Z.to_nat k) (ascii_of_z (Znth k s 0))
    Hpre) as Hlower.
  rewrite (string_get_string_of_list_z_z s k Hk) in Hlower.
  specialize (Hlower eq_refl).
  unfold is_lowercase_ascii, lower_char_z in *.
  rewrite nat_of_ascii_ascii_of_z in Hlower by (apply Hrange; lia).
  cbn in Hlower.
  lia.
Qed.

Lemma problem_50_encode_spec_z_intro : forall input output n,
  Zlength input = n ->
  Zlength output = n ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = encode_shift_char_z (Znth k input 0)) ->
  problem_50_encode_spec_z input output.
Proof.
  intros input output n Hin Hout Hpoint.
  unfold problem_50_encode_spec_z.
  split; [lia |].
  intros k Hk.
  apply Hpoint.
  lia.
Qed.

Lemma problem_50_spec_z_intro : forall input output n,
  Zlength input = n ->
  Zlength output = n ->
  problem_50_pre_z input ->
  ascii_range_z input ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = decode_shift_char_z (Znth k input 0)) ->
  problem_50_spec_z input output.
Proof.
  intros input output n Hin Hout Hpre Hrange Hpoint.
  unfold problem_50_spec_z, problem_50_spec.
    repeat rewrite list_ascii_of_string_string_of_list_z.
    apply nth_error_ext.
    intros idx.
    repeat rewrite nth_error_map.
    destruct (lt_dec idx (List.length input)) as [Hidx | Hidx].
    + assert (Hidx_out : (idx < List.length output)%nat).
      { rewrite <- (Nat2Z.id idx).
        rewrite Zlength_correct in Hout.
        rewrite Zlength_correct in Hin.
        lia. }
      rewrite (@nth_error_nth' Z output idx 0 Hidx_out).
      rewrite (@nth_error_nth' Z input idx 0 Hidx).
      simpl.
      f_equal.
      specialize (Hpoint (Z.of_nat idx)).
      rewrite <- Hin in Hpoint.
      specialize (Hpoint ltac:(rewrite Zlength_correct; lia)).
      replace (nth idx output 0) with (Znth (Z.of_nat idx) output 0)
        by (unfold Znth; rewrite Nat2Z.id; reflexivity).
      replace (nth idx input 0) with (Znth (Z.of_nat idx) input 0)
        by (unfold Znth; rewrite Nat2Z.id; reflexivity).
      rewrite Hpoint.
      apply decode_shift_char_z_correct.
      eapply lower_char_z_from_problem_50_pre; eauto.
      rewrite Zlength_correct.
      lia.
    + assert (Hidx_in_none : nth_error input idx = None).
      { apply nth_error_None. lia. }
      assert (Hidx_out_none : nth_error output idx = None).
      { apply nth_error_None.
        assert (List.length output = List.length input) by
          (apply Nat2Z.inj; rewrite <- !Zlength_correct; lia).
        lia. }
      rewrite Hidx_in_none, Hidx_out_none.
      reflexivity.
Qed.

Lemma problem_50_decode_spec_z_intro : forall input output n,
  Zlength input = n ->
  Zlength output = n ->
  problem_50_pre_z input ->
  ascii_range_z input ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = decode_shift_char_z (Znth k input 0)) ->
  problem_50_decode_spec_z input output.
Proof.
  intros input output n Hin Hout Hpre Hrange Hpoint.
  unfold problem_50_decode_spec_z.
  eapply problem_50_spec_z_intro with (n := n); eauto.
Qed.
