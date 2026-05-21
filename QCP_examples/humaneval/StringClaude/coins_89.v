Load "../spec/89".

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

Definition problem_89_pre_z (s : list Z) : Prop :=
  problem_89_pre (string_of_list_z s).

Definition encrypt_char_z (c : Z) : Z :=
  Z.rem (c + 4 - 97) 26 + 97.

Definition problem_89_spec_z (input output : list Z) : Prop :=
  problem_89_spec (string_of_list_z input) (string_of_list_z output).

Lemma encrypt_output_range : forall x,
  lower_char_z x ->
  0 <= encrypt_char_z x <= 127.
Proof.
  intros x Hlower.
  unfold encrypt_char_z, lower_char_z in *.
  pose proof (Z.rem_bound_pos (x + 4 - 97) 26 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma lower_char_z_cases : forall x,
  lower_char_z x ->
  x = 97 \/ x = 98 \/ x = 99 \/ x = 100 \/ x = 101 \/ x = 102 \/
  x = 103 \/ x = 104 \/ x = 105 \/ x = 106 \/ x = 107 \/ x = 108 \/
  x = 109 \/ x = 110 \/ x = 111 \/ x = 112 \/ x = 113 \/ x = 114 \/
  x = 115 \/ x = 116 \/ x = 117 \/ x = 118 \/ x = 119 \/ x = 120 \/
  x = 121 \/ x = 122.
Proof.
  unfold lower_char_z.
  intros; lia.
Qed.

Lemma encrypt_char_z_relation : forall x,
  lower_char_z x ->
  char_relation (ascii_of_z x) (ascii_of_z (encrypt_char_z x)).
Proof.
  intros x Hlower.
  pose proof (lower_char_z_cases x Hlower) as Hcases.
  repeat
    match type of Hcases with
    | _ \/ _ => destruct Hcases as [-> | Hcases]; [vm_compute; reflexivity |]
    | _ => subst x; vm_compute; reflexivity
    end.
Qed.

Lemma all_lowercase_ascii_get_89 : forall s i c,
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

Lemma lower_char_z_from_problem_89_pre : forall s k,
  problem_89_pre_z s ->
  ascii_range_z s ->
  0 <= k < Zlength s ->
  lower_char_z (Znth k s 0).
Proof.
  intros s k Hpre Hrange Hk.
  unfold problem_89_pre_z, problem_89_pre in Hpre.
  pose proof (all_lowercase_ascii_get_89
    (string_of_list_z s) (Z.to_nat k) (ascii_of_z (Znth k s 0))
    Hpre) as Hlower.
  rewrite (string_get_string_of_list_z_z s k Hk) in Hlower.
  specialize (Hlower eq_refl).
  unfold is_lowercase_ascii, lower_char_z in *.
  rewrite nat_of_ascii_ascii_of_z in Hlower by (apply Hrange; lia).
  cbn in Hlower.
  lia.
Qed.

Lemma problem_89_spec_z_intro : forall input output n,
  Zlength input = n ->
  Zlength output = n ->
  problem_89_pre_z input ->
  ascii_range_z input ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = encrypt_char_z (Znth k input 0)) ->
  problem_89_spec_z input output.
Proof.
  intros input output n Hin Hout Hpre Hrange Hpoint.
  unfold problem_89_spec_z, problem_89_spec.
    split.
    + repeat rewrite string_of_list_z_length.
      apply Nat2Z.inj.
      rewrite <- !Zlength_correct.
      lia.
    + intros i Hi.
      rewrite string_get_string_of_list_z by
        (rewrite <- string_of_list_z_length; exact Hi).
      assert (Hi_out : (i < List.length output)%nat).
      { assert (List.length output = List.length input) by
          (apply Nat2Z.inj; rewrite <- !Zlength_correct; lia).
        rewrite string_of_list_z_length in Hi.
        lia. }
      rewrite string_get_string_of_list_z by exact Hi_out.
      specialize (Hpoint (Z.of_nat i)).
      rewrite <- Hin in Hpoint.
      specialize (Hpoint ltac:(rewrite Zlength_correct; rewrite string_of_list_z_length in Hi; lia)).
      replace (nth i output 0) with (Znth (Z.of_nat i) output 0)
        by (unfold Znth; rewrite Nat2Z.id; reflexivity).
      replace (nth i input 0) with (Znth (Z.of_nat i) input 0)
        by (unfold Znth; rewrite Nat2Z.id; reflexivity).
      rewrite Hpoint.
      apply encrypt_char_z_relation.
      eapply lower_char_z_from_problem_89_pre; eauto.
      rewrite Zlength_correct.
      rewrite string_of_list_z_length in Hi.
      lia.
Qed.
