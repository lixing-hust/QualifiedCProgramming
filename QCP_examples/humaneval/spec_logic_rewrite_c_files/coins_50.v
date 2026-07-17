Load "../spec/50".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.
From SimpleC.StdLib Require Import string_lib.
Import ListNotations.

Local Open Scope Z_scope.

Definition ascii_of_z_50 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_50 (l : list Z) : string :=
  match l with
  | nil => EmptyString
  | c :: rest => String (ascii_of_z_50 c) (string_of_list_z_50 rest)
  end.

Definition problem_50_pre_z (input : list Z) : Prop :=
  problem_50_pre (string_of_list_z_50 input).

Definition problem_50_spec_z (input output : list Z) : Prop :=
  problem_50_spec (string_of_list_z_50 input) (string_of_list_z_50 output).

Definition encode_shift_char_z_50 (c : Z) : Z :=
  Z.rem (c + 5 - 97) 26 + 97.

Definition decode_shift_char_z_50 (c : Z) : Z :=
  Z.rem (c + 21 - 97) 26 + 97.

Definition encode_prefix_50 (input output : list Z) : Prop :=
  Zlength output <= Zlength input /\
  forall k, 0 <= k < Zlength output ->
    Znth k output 0 = encode_shift_char_z_50 (Znth k input 0).

Definition decode_prefix_50 (input output : list Z) : Prop :=
  Zlength output <= Zlength input /\
  forall k, 0 <= k < Zlength output ->
    Znth k output 0 = decode_shift_char_z_50 (Znth k input 0).

Lemma list_ascii_of_string_of_list_z_50 : forall l,
  list_ascii_of_string (string_of_list_z_50 l) = map ascii_of_z_50 l.
Proof.
  induction l as [| c rest IH]; simpl; congruence.
Qed.

Lemma string_length_nonnegative_50 : forall l,
  0 <= string_length l.
Proof.
  intros l. unfold string_length. apply Zlength_nonneg.
Qed.

Lemma lower_input_at_50 : forall input k,
  problem_50_pre_z input ->
  valid_string input ->
  0 <= k < Zlength input ->
  97 <= Znth k input 0 <= 122.
Proof.
  intros input k Hpre Hvalid Hk.
  unfold problem_50_pre_z, problem_50_pre, all_lowercase_ascii in Hpre.
  rewrite list_ascii_of_string_of_list_z_50 in Hpre.
  change (Forall is_lowercase_ascii (map ascii_of_z_50 input)) in Hpre.
  rewrite Forall_map in Hpre.
  destruct Hvalid as [Hascii _].
  pose proof (Hascii k Hk) as Hrange.
  pose proof (proj1 (Forall_nth
    (fun x : Z => is_lowercase_ascii (ascii_of_z_50 x)) input) Hpre) as Hnth.
  assert (Hkn : (Z.to_nat k < List.length input)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  specialize (Hnth (Z.to_nat k) 0%Z Hkn).
  change (is_lowercase_ascii (ascii_of_z_50 (Znth k input 0))) in Hnth.
  unfold is_lowercase_ascii, ascii_of_z_50 in Hnth.
  rewrite nat_ascii_embedding in Hnth by lia.
  destruct Hnth as [Hlo Hhi].
  apply Nat2Z.inj_le in Hlo. apply Nat2Z.inj_le in Hhi.
  simpl in Hlo, Hhi.
  rewrite Z2Nat.id in Hlo, Hhi by lia.
  lia.
Qed.

Lemma Znth_c_string_50 : forall input k,
  0 <= k < Zlength input ->
  Znth k (c_string input) 0 = Znth k input 0.
Proof.
  intros input k Hk. unfold c_string. apply app_Znth1. exact Hk.
Qed.

Lemma encode_shift_char_range_50 : forall c,
  97 <= c <= 122 ->
  97 <= encode_shift_char_z_50 c <= 122.
Proof.
  intros c Hc. unfold encode_shift_char_z_50.
  pose proof (Z.rem_bound_pos (c + 5 - 97) 26 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma decode_shift_char_range_50 : forall c,
  97 <= c <= 122 ->
  97 <= decode_shift_char_z_50 c <= 122.
Proof.
  intros c Hc. unfold decode_shift_char_z_50.
  pose proof (Z.rem_bound_pos (c + 21 - 97) 26 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma encode_prefix_nil_50 : forall input,
  encode_prefix_50 input nil.
Proof.
  intros input. split; [apply Zlength_nonneg |].
  intros k Hk. unfold Zlength in Hk. simpl in Hk. lia.
Qed.

Lemma decode_prefix_nil_50 : forall input,
  decode_prefix_50 input nil.
Proof.
  intros input. split; [apply Zlength_nonneg |].
  intros k Hk. unfold Zlength in Hk. simpl in Hk. lia.
Qed.

Lemma encode_prefix_snoc_50 : forall input output i,
  problem_50_pre_z input ->
  valid_string input ->
  encode_prefix_50 input output ->
  Zlength output = i ->
  0 <= i < Zlength input ->
  encode_prefix_50 input
    (output ++ [IntLib.signed_last_nbits
      (Z.rem (Znth i (c_string input) 0 + 5 - 97) 26 + 97) 8]).
Proof.
  intros input output i Hpre Hvalid [Hlen Hpoint] Hout Hi.
  pose proof (lower_input_at_50 input i Hpre Hvalid Hi) as Hlower.
  pose proof (encode_shift_char_range_50 (Znth i input 0) Hlower) as Hshift.
  split.
  - rewrite Zlength_app_cons. lia.
  - intros k Hk.
    rewrite Zlength_app_cons in Hk.
    destruct (Z_lt_dec k (Zlength output)) as [Hlt | Hge].
    + rewrite app_Znth1 by lia. apply Hpoint. lia.
    + assert (k = Zlength output) by lia. subst k.
      rewrite app_Znth2 by lia. rewrite Z.sub_diag. simpl.
      rewrite Znth_c_string_50 by lia.
      rewrite Hout.
      unfold encode_shift_char_z_50 in Hshift.
      rewrite IntLib.signed_last_nbits_eq; unfold encode_shift_char_z_50; cbn; lia.
Qed.

Lemma decode_prefix_snoc_50 : forall input output i,
  problem_50_pre_z input ->
  valid_string input ->
  decode_prefix_50 input output ->
  Zlength output = i ->
  0 <= i < Zlength input ->
  decode_prefix_50 input
    (output ++ [IntLib.signed_last_nbits
      (Z.rem (Znth i (c_string input) 0 + 21 - 97) 26 + 97) 8]).
Proof.
  intros input output i Hpre Hvalid [Hlen Hpoint] Hout Hi.
  pose proof (lower_input_at_50 input i Hpre Hvalid Hi) as Hlower.
  pose proof (decode_shift_char_range_50 (Znth i input 0) Hlower) as Hshift.
  split.
  - rewrite Zlength_app_cons. lia.
  - intros k Hk.
    rewrite Zlength_app_cons in Hk.
    destruct (Z_lt_dec k (Zlength output)) as [Hlt | Hge].
    + rewrite app_Znth1 by lia. apply Hpoint. lia.
    + assert (k = Zlength output) by lia. subst k.
      rewrite app_Znth2 by lia. rewrite Z.sub_diag. simpl.
      rewrite Znth_c_string_50 by lia.
      rewrite Hout.
      unfold decode_shift_char_z_50 in Hshift.
      rewrite IntLib.signed_last_nbits_eq; unfold decode_shift_char_z_50; cbn; lia.
Qed.

Lemma decode_shift_char_correct_50 : forall c,
  97 <= c <= 122 ->
  ascii_of_z_50 (decode_shift_char_z_50 c) =
  decode_char (ascii_of_z_50 c).
Proof.
  intros c Hc.
  unfold decode_shift_char_z_50, decode_char, ascii_of_z_50.
  rewrite nat_ascii_embedding by lia.
  change (ascii_of_nat (Z.to_nat (Z.rem (c + 21 - 97) 26 + 97)) =
          ascii_of_nat (97 + (Z.to_nat c - 97 + 21) mod 26)).
  f_equal.
  rewrite Z.rem_mod_nonneg by lia.
  rewrite Z2Nat.inj_add by (pose proof (Z.mod_pos_bound (c + 21 - 97) 26 ltac:(lia)); lia).
  rewrite Z2Nat.inj_mod by lia.
  replace (Z.to_nat (c + 21 - 97)) with (Z.to_nat c - 97 + 21)%nat by lia.
  rewrite Nat.add_comm. reflexivity.
Qed.

Lemma decode_prefix_full_spec_50 : forall input output,
  problem_50_pre_z input ->
  valid_string input ->
  decode_prefix_50 input output ->
  Zlength output = Zlength input ->
  problem_50_spec_z input output.
Proof.
  intros input output Hpre Hvalid [_ Hpoint] Hlen.
  assert (Houtput : output = map decode_shift_char_z_50 input).
  { apply list_eq_nth with (d := 0%Z).
    - rewrite map_length. apply Nat2Z.inj.
      rewrite <- !Zlength_correct. exact Hlen.
    - intros n Hn.
      assert (Hnin : (n < List.length input)%nat).
      { assert (List.length input = List.length output).
        { apply Nat2Z.inj. rewrite <- !Zlength_correct. lia. }
        lia. }
      rewrite (map_nth_len Z Z decode_shift_char_z_50 input n 0%Z 0%Z)
        by exact Hnin.
      unfold Znth in Hpoint.
      specialize (Hpoint (Z.of_nat n)).
      rewrite Nat2Z.id in Hpoint.
      apply Hpoint.
      rewrite Zlength_correct. split; [lia |].
      apply Nat2Z.inj_lt. exact Hn. }
  subst output.
  unfold problem_50_spec_z, problem_50_spec.
  rewrite !list_ascii_of_string_of_list_z_50.
  rewrite !map_map.
  apply map_ext_in.
  intros c Hc.
  apply decode_shift_char_correct_50.
  apply In_nth with (d := 0%Z) in Hc.
  destruct Hc as [n [Hn Hnth]].
  rewrite <- Hnth.
  replace (nth n input 0) with (Znth (Z.of_nat n) input 0)
    by (unfold Znth; rewrite Nat2Z.id; reflexivity).
  eapply lower_input_at_50; eauto.
  rewrite Zlength_correct. split; [lia |].
  apply Nat2Z.inj_lt. exact Hn.
Qed.
