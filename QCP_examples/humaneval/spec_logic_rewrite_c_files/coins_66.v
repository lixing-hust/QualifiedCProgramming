Load "../spec/66".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
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

Definition problem_66_pre_z (input : list Z) : Prop :=
  problem_66_pre (string_of_list_z input).

Definition problem_66_spec_z (input : list Z) (output : Z) : Prop :=
  problem_66_spec (string_of_list_z input) (Z.to_nat output).

Definition upper_contribution_z_66 (c : Z) : Z :=
  if (Z.leb 65 c && Z.leb c 90)%bool then c else 0.

Definition upper_sum_list_z_66 (input : list Z) : Z :=
  fold_right Z.add 0 (map upper_contribution_z_66 input).

Definition upper_sum_prefix_66 (i : Z) (input : list Z) : Z :=
  upper_sum_list_z_66 (firstn (Z.to_nat i) input).

Definition upper_sum_safe_66 (input : list Z) : Prop :=
  forall i,
    0 <= i <= Zlength input ->
    0 <= upper_sum_prefix_66 i input <= INT_MAX.

Lemma firstn_succ_snoc_66 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n as [| n IH]; intros l d Hn.
  - destruct l; simpl in *; [lia | reflexivity].
  - destruct l as [| x xs]; simpl in *; try lia.
    rewrite (IH xs d) by lia.
    reflexivity.
Qed.

Lemma firstn_succ_Znth_66 : forall (input : list Z) i,
  0 <= i < Zlength input ->
  firstn (Z.to_nat (i + 1)) input =
  List.app (firstn (Z.to_nat i) input) [Znth i input 0].
Proof.
  intros input i Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_66 with (d := 0).
  - reflexivity.
  - rewrite <- z_to_nat_Zlength.
    lia.
Qed.

Lemma upper_sum_list_z_app_66 : forall l1 l2,
  upper_sum_list_z_66 (List.app l1 l2) =
  upper_sum_list_z_66 l1 + upper_sum_list_z_66 l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - unfold upper_sum_list_z_66; simpl; lia.
  - unfold upper_sum_list_z_66 in *; simpl in *.
    rewrite IH.
    lia.
Qed.

Lemma upper_sum_prefix_step_upper_66 : forall i input,
  0 <= i < Zlength input ->
  65 <= Znth i input 0 <= 90 ->
  upper_sum_prefix_66 (i + 1) input =
  upper_sum_prefix_66 i input + Znth i input 0.
Proof.
  intros i input Hi Hupper.
  unfold upper_sum_prefix_66.
  rewrite firstn_succ_Znth_66 by exact Hi.
  rewrite upper_sum_list_z_app_66.
  unfold upper_sum_list_z_66 at 2.
  simpl.
  unfold upper_contribution_z_66.
  replace (Z.leb 65 (Znth i input 0)) with true
    by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Znth i input 0) 90) with true
    by (symmetry; apply Z.leb_le; lia).
  simpl.
  lia.
Qed.

Lemma upper_sum_prefix_step_other_66 : forall i input,
  0 <= i < Zlength input ->
  (Znth i input 0 < 65 \/ 90 < Znth i input 0) ->
  upper_sum_prefix_66 (i + 1) input =
  upper_sum_prefix_66 i input.
Proof.
  intros i input Hi Hother.
  unfold upper_sum_prefix_66.
  rewrite firstn_succ_Znth_66 by exact Hi.
  rewrite upper_sum_list_z_app_66.
  unfold upper_sum_list_z_66 at 2.
  simpl.
  unfold upper_contribution_z_66.
  destruct Hother as [Hlo | Hhi].
  - replace (Z.leb 65 (Znth i input 0)) with false
      by (symmetry; apply Z.leb_gt; lia).
    simpl.
    lia.
  - destruct (Z.leb 65 (Znth i input 0)) eqn:Hlo.
    + replace (Z.leb (Znth i input 0) 90) with false
        by (symmetry; apply Z.leb_gt; lia).
      simpl.
      lia.
    + simpl.
      lia.
Qed.

Lemma upper_contribution_z_nonneg_66 : forall c,
  0 <= c ->
  0 <= upper_contribution_z_66 c.
Proof.
  intros c Hc.
  unfold upper_contribution_z_66.
  destruct (Z.leb 65 c && Z.leb c 90)%bool; lia.
Qed.

Lemma upper_sum_list_z_nonneg_66 : forall input,
  (forall c, In c input -> 0 <= c) ->
  0 <= upper_sum_list_z_66 input.
Proof.
  induction input as [| c input IH]; intros Hnonneg.
  - unfold upper_sum_list_z_66; simpl; lia.
  - unfold upper_sum_list_z_66 in *; simpl in *.
    pose proof (upper_contribution_z_nonneg_66 c (Hnonneg c (or_introl eq_refl))).
    assert (0 <= fold_right Z.add 0
      (map upper_contribution_z_66 input)).
    { apply IH. intros x Hx. apply Hnonneg. right. exact Hx. }
    lia.
Qed.

Lemma ascii_range_z_tail_66 : forall c input,
  ascii_range_z (c :: input) ->
  ascii_range_z input.
Proof.
  intros c input Hrange i Hi.
  specialize (Hrange (i + 1)).
  rewrite Zlength_cons in Hrange.
  replace (Znth (i + 1) (c :: input) 0) with (Znth i input 0) in Hrange.
  - apply Hrange. lia.
  - unfold Znth.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    reflexivity.
Qed.

Lemma ascii_range_z_head_66 : forall c input,
  ascii_range_z (c :: input) ->
  0 <= c < 256.
Proof.
  intros c input Hrange.
  specialize (Hrange 0).
  rewrite Zlength_cons in Hrange.
  change (Znth 0 (c :: input) 0) with c in Hrange.
  apply Hrange.
  pose proof (Zlength_nonneg input).
  lia.
Qed.

Lemma upper_sum_list_z_nonneg_ascii_66 : forall input,
  ascii_range_z input ->
  0 <= upper_sum_list_z_66 input.
Proof.
  induction input as [| c input IH]; intros Hrange.
  - unfold upper_sum_list_z_66; simpl; lia.
  - unfold upper_sum_list_z_66 in *; simpl in *.
    pose proof (ascii_range_z_head_66 c input Hrange) as Hc.
    pose proof (upper_contribution_z_nonneg_66 c ltac:(lia)) as Hcontrib.
    assert (Htail : ascii_range_z input).
    { apply ascii_range_z_tail_66 with (c := c). exact Hrange. }
    specialize (IH Htail).
    lia.
Qed.

Lemma upper_contribution_relation_66 : forall c,
  0 <= c < 256 ->
  uppercase_contribution (ascii_of_z c)
    (Z.to_nat (upper_contribution_z_66 c)).
Proof.
  intros c Hrange.
  unfold uppercase_contribution, uppercase_ascii, upper_contribution_z_66.
  rewrite nat_of_ascii_ascii_of_z by exact Hrange.
  destruct (Z.leb 65 c) eqn:Hlo;
  destruct (Z.leb c 90) eqn:Hhi; simpl.
  - left.
    apply Z.leb_le in Hlo.
    apply Z.leb_le in Hhi.
    split; lia.
  - right.
    apply Z.leb_gt in Hhi.
    split; [lia | reflexivity].
  - right.
    apply Z.leb_gt in Hlo.
    split; [lia | reflexivity].
  - right.
    apply Z.leb_gt in Hlo.
    split; [lia | reflexivity].
Qed.

Lemma upper_contributions_Forall2_66 : forall input,
  ascii_range_z input ->
  Forall2 uppercase_contribution
    (map ascii_of_z input)
    (map (fun c => Z.to_nat (upper_contribution_z_66 c)) input).
Proof.
  induction input as [| c input IH]; intros Hrange; simpl.
  - constructor.
  - constructor.
    + apply upper_contribution_relation_66.
      apply ascii_range_z_head_66 with (input := input).
      exact Hrange.
    + apply IH.
      apply ascii_range_z_tail_66 with (c := c).
      exact Hrange.
Qed.

Lemma upper_sum_list_z_nat_66 : forall input,
  ascii_range_z input ->
  Z.to_nat (upper_sum_list_z_66 input) =
  fold_right Nat.add 0%nat
    (map (fun c => Z.to_nat (upper_contribution_z_66 c)) input).
Proof.
  induction input as [| c input IH]; intros Hrange; simpl.
  - reflexivity.
  - unfold upper_sum_list_z_66 in *; simpl in *.
    rewrite Z2Nat.inj_add.
    + rewrite IH.
      * reflexivity.
      * apply ascii_range_z_tail_66 with (c := c). exact Hrange.
    + apply upper_contribution_z_nonneg_66.
      pose proof (ascii_range_z_head_66 c input Hrange).
      lia.
    + apply upper_sum_list_z_nonneg_ascii_66.
      apply ascii_range_z_tail_66 with (c := c).
      exact Hrange.
Qed.

Lemma valid_string_ascii_range_66 : forall input,
  valid_string input ->
  ascii_range_z input.
Proof.
  intros input [Hascii _] i Hi.
  specialize (Hascii i Hi).
  lia.
Qed.

Lemma upper_sum_prefix_full_66 : forall input,
  upper_sum_prefix_66 (Zlength input) input =
  upper_sum_list_z_66 input.
Proof.
  intros input.
  unfold upper_sum_prefix_66.
  rewrite z_to_nat_Zlength.
  rewrite firstn_all.
  reflexivity.
Qed.

Lemma problem_66_spec_z_of_sum_66 : forall input output,
  valid_string input ->
  output = upper_sum_prefix_66 (string_length input) input ->
  problem_66_spec_z input output.
Proof.
  intros input output Hvalid Houtput.
  unfold problem_66_spec_z, problem_66_spec.
  exists (map (fun c => Z.to_nat (upper_contribution_z_66 c)) input).
  split.
  - rewrite list_ascii_of_string_string_of_list_z.
    apply upper_contributions_Forall2_66.
    apply valid_string_ascii_range_66.
    exact Hvalid.
  - rewrite Houtput.
    unfold string_length.
    rewrite upper_sum_prefix_full_66.
    apply upper_sum_list_z_nat_66.
    apply valid_string_ascii_range_66.
    exact Hvalid.
Qed.
