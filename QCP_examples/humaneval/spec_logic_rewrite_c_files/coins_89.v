Load "../spec/89".

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

Definition problem_89_pre_z (input : list Z) : Prop :=
  problem_89_pre (string_of_list_z input).

Definition problem_89_spec_z (input output : list Z) : Prop :=
  problem_89_spec (string_of_list_z input) (string_of_list_z output).

Definition lowercase_codes_z_89 (input : list Z) : Prop :=
  forall k, 0 <= k < Zlength input ->
    97 <= Znth k input 0 <= 122.

Definition shift_four_z_89 (c : Z) : Z :=
  (c + 4 - 97) mod 26 + 97.

Definition rotate_prefix_z_89
    (input output : list Z) (n : Z) : Prop :=
  Zlength output = n /\
  forall k, 0 <= k < n ->
    Znth k output 0 = shift_four_z_89 (Znth k input 0).

Lemma problem_89_pre_z_lowercase : forall input,
  problem_89_pre_z input ->
  ascii_range_z input ->
  lowercase_codes_z_89 input.
Proof.
  intros input Hpre Hrange k Hk.
  unfold problem_89_pre_z, problem_89_pre,
    all_lowercase_ascii in Hpre.
  rewrite list_ascii_of_string_string_of_list_z in Hpre.
  apply Forall_forall with (x := ascii_of_z (Znth k input 0)) in Hpre.
  - unfold is_lowercase_ascii in Hpre.
    specialize (Hrange k Hk).
    rewrite nat_of_ascii_ascii_of_z in Hpre by lia.
    change (97%nat <= Z.to_nat (Znth k input 0%Z) <= 122%nat)%nat in Hpre.
    lia.
  - apply in_map.
    unfold Znth.
    apply nth_In.
    rewrite <- z_to_nat_Zlength.
    lia.
Qed.

Lemma shift_four_z_89_range : forall c,
  97 <= c <= 122 ->
  97 <= shift_four_z_89 c <= 122.
Proof.
  intros c Hc.
  unfold shift_four_z_89.
  pose proof (Z.mod_pos_bound (c + 4 - 97) 26 ltac:(lia)).
  lia.
Qed.

Lemma shift_four_z_89_correct : forall c,
  97 <= c <= 122 ->
  shifted_by_four (ascii_of_z c) (ascii_of_z (shift_four_z_89 c)).
Proof.
  intros c Hc.
  assert (
    c = 97 \/ c = 98 \/ c = 99 \/ c = 100 \/ c = 101 \/ c = 102 \/
    c = 103 \/ c = 104 \/ c = 105 \/ c = 106 \/ c = 107 \/ c = 108 \/
    c = 109 \/ c = 110 \/ c = 111 \/ c = 112 \/ c = 113 \/ c = 114 \/
    c = 115 \/ c = 116 \/ c = 117 \/ c = 118 \/ c = 119 \/ c = 120 \/
    c = 121 \/ c = 122) as Hcases by lia.
  repeat
    match type of Hcases with
    | _ \/ _ => destruct Hcases as [-> | Hcases]; [reflexivity |]
    | _ => subst c; reflexivity
    end.
Qed.

Lemma rotate_prefix_z_89_nil : forall input,
  rotate_prefix_z_89 input [] 0.
Proof.
  intros input.
  split; [reflexivity | lia].
Qed.

Lemma rotate_prefix_z_89_snoc : forall input output i c,
  0 <= i < Zlength input ->
  rotate_prefix_z_89 input output i ->
  c = shift_four_z_89 (Znth i input 0) ->
  rotate_prefix_z_89 input (output ++ [c]) (i + 1).
Proof.
  intros input output i c Hi [Hlen Hpoint] ->.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + unfold Znth.
      rewrite app_nth1.
      2: { apply Nat2Z.inj_lt.
           rewrite Z2Nat.id by lia.
           rewrite <- Zlength_correct.
           lia. }
      apply Hpoint. lia.
    + assert (k = i) by lia. subst k.
      unfold Znth.
      rewrite app_nth2.
      2: { apply Nat2Z.inj_le.
           rewrite Z2Nat.id by lia.
           rewrite <- Zlength_correct.
           lia. }
      replace (Z.to_nat i - List.length output)%nat with 0%nat.
      2: { assert (Z.to_nat i = List.length output) as Heq.
           { apply Nat2Z.inj.
             rewrite Z2Nat.id by lia.
             rewrite <- Zlength_correct.
             lia. }
           rewrite Heq, Nat.sub_diag.
           reflexivity. }
      reflexivity.
Qed.

Lemma lowercase_c_string_code_89 : forall input i,
  lowercase_codes_z_89 input ->
  0 <= i < string_length input ->
  97 <= Znth i (c_string input) 0 <= 122.
Proof.
  intros input i Hlower Hi.
  rewrite c_string_Znth_inside by exact Hi.
  apply Hlower.
  exact Hi.
Qed.

Lemma c_shift_expr_eq_89 : forall input i,
  lowercase_codes_z_89 input ->
  0 <= i < string_length input ->
  (Z.rem (Znth i (c_string input) 0 + 4 - 97) 26 + 97) =
    shift_four_z_89 (Znth i input 0).
Proof.
  intros input i Hlower Hi.
  pose proof (lowercase_c_string_code_89 input i Hlower Hi) as Hcode.
  rewrite c_string_Znth_inside in Hcode |- * by exact Hi.
  unfold shift_four_z_89.
  rewrite Z.rem_mod_nonneg by lia.
  reflexivity.
Qed.

Lemma c_shift_byte_eq_89 : forall input i,
  lowercase_codes_z_89 input ->
  0 <= i < string_length input ->
  signed_last_nbits
    (Z.rem (Znth i (c_string input) 0 + 4 - 97) 26 + 97) 8 =
  shift_four_z_89 (Znth i input 0).
Proof.
  intros input i Hlower Hi.
  rewrite c_shift_expr_eq_89 by assumption.
  rewrite signed_last_nbits_eq.
  - reflexivity.
  - lia.
  - pose proof (lowercase_c_string_code_89 input i Hlower Hi) as Hcode.
    pose proof (shift_four_z_89_range
      (Znth i (c_string input) 0) Hcode) as Hshift.
    rewrite c_string_Znth_inside in Hshift by exact Hi.
    lia.
Qed.

Lemma problem_89_spec_z_intro : forall input output,
  problem_89_pre_z input ->
  ascii_range_z input ->
  rotate_prefix_z_89 input output (Zlength input) ->
  problem_89_spec_z input output.
Proof.
  intros input.
  induction input as [| x xs IH]; intros output Hpre Hrange Hrot.
  - destruct Hrot as [Hlen _].
    destruct output; [constructor |].
    rewrite Zlength_cons, Zlength_nil in Hlen.
    pose proof (Zlength_nonneg output). lia.
  - destruct output as [| y ys].
    + destruct Hrot as [Hlen _].
      rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg xs). lia.
    + destruct Hrot as [Hlen Hpoint].
      assert (y = shift_four_z_89 x) as Hy.
      { specialize (Hpoint 0).
        change (Znth 0 (y :: ys) 0) with y in Hpoint.
        change (Znth 0 (x :: xs) 0) with x in Hpoint.
        apply Hpoint.
        rewrite Zlength_cons.
        pose proof (Zlength_nonneg xs). lia. }
      unfold problem_89_spec_z, problem_89_spec.
      rewrite !list_ascii_of_string_string_of_list_z.
      constructor.
      * rewrite Hy.
        apply shift_four_z_89_correct.
        pose proof (problem_89_pre_z_lowercase
          (x :: xs) Hpre Hrange) as Hlower.
        apply Hlower with (k := 0).
        rewrite Zlength_cons.
        pose proof (Zlength_nonneg xs). lia.
      * assert (problem_89_pre_z xs) as Hpre_tail.
        { unfold problem_89_pre_z, problem_89_pre,
            all_lowercase_ascii in *.
          rewrite !list_ascii_of_string_string_of_list_z in *.
          inversion Hpre; assumption. }
        assert (ascii_range_z xs) as Hrange_tail.
        { unfold ascii_range_z in *.
          intros k Hk.
          specialize (Hrange (k + 1)).
          replace (Znth k xs 0) with
            (Znth (k + 1) (x :: xs) 0).
          - apply Hrange. rewrite Zlength_cons. lia.
          - unfold Znth.
            replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
            reflexivity. }
        assert (rotate_prefix_z_89 xs ys (Zlength xs)) as Hrot_tail.
        { split.
          - rewrite !Zlength_cons in Hlen. lia.
          - intros k Hk.
            specialize (Hpoint (k + 1)).
            replace (Znth k ys 0) with
              (Znth (k + 1) (y :: ys) 0).
            2: { unfold Znth.
                 replace (Z.to_nat (k + 1)) with
                   (S (Z.to_nat k)) by lia.
                 reflexivity. }
            replace (Znth k xs 0) with
              (Znth (k + 1) (x :: xs) 0).
            2: { unfold Znth.
                 replace (Z.to_nat (k + 1)) with
                   (S (Z.to_nat k)) by lia.
                 reflexivity. }
            apply Hpoint.
            rewrite Zlength_cons. lia. }
        specialize (IH ys Hpre_tail Hrange_tail Hrot_tail).
        unfold problem_89_spec_z, problem_89_spec in IH.
        rewrite !list_ascii_of_string_string_of_list_z in IH.
        exact IH.
Qed.
