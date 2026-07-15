Load "../spec/108".

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition Zabs (x : Z) : Z := Z.abs x.

Definition problem_108_pre_z (l : list Z) : Prop :=
  problem_108_pre l.

Definition problem_108_spec_z (input : list Z) (output : Z) : Prop :=
  problem_108_spec input output.

Definition count_nums_prefix_108 (input : list Z) (i num : Z) : Prop :=
  0 <= i <= Zlength input /\
  num = count_nums_impl (sublist 0 i input).

Definition signed_digit_sum_positive_108 (current sum : Z) : Prop :=
  sum = sum_digits current.

Fixpoint signed_digit_sum_state_fuel_108
  (fuel : nat) (current w sum : Z) : Prop :=
  current <= 0 /\
  0 <= w /\
  w <= INT_MAX /\
  INT_MIN < sum /\
  sum < INT_MAX /\
  match fuel with
  | O =>
      w < 10 /\
      INT_MIN < sum - w /\
      sum - w <= INT_MAX /\
      signed_digit_sum_positive_108 current (sum - w)
  | S fuel' =>
      if 10 <=? w
      then
        INT_MIN < sum + Z.rem w 10 /\
        sum + Z.rem w 10 < INT_MAX /\
        signed_digit_sum_state_fuel_108 fuel' current
          (Z.quot w 10) (sum + Z.rem w 10)
      else
        INT_MIN < sum - w /\
        sum - w <= INT_MAX /\
        signed_digit_sum_positive_108 current (sum - w)
  end.

Definition signed_digit_sum_state_108 (current w sum : Z) : Prop :=
  exists fuel,
    signed_digit_sum_state_fuel_108 fuel current w sum.

Definition count_nums_safe_108 (l : list Z) : Prop :=
  Forall
    (fun x =>
       INT_MIN < x <= INT_MAX /\
       (0 < x -> sum_digits x > 0) /\
       (x <= 0 -> signed_digit_sum_state_108 x (Z.abs x) 0))
    l.

Lemma count_nums_safe_108_Znth : forall l i,
  count_nums_safe_108 l ->
  0 <= i < Zlength l ->
  INT_MIN < Znth i l 0 <= INT_MAX.
Proof.
  intros l i Hsafe Hi.
  unfold count_nums_safe_108 in Hsafe.
  rewrite Forall_forall in Hsafe.
  specialize (Hsafe (Znth i l 0)).
  assert (In (Znth i l 0) l).
  { unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia. }
  specialize (Hsafe H).
  tauto.
Qed.

Lemma count_nums_safe_108_Znth_pos_sum : forall l i,
  count_nums_safe_108 l ->
  0 <= i < Zlength l ->
  0 < Znth i l 0 ->
  sum_digits (Znth i l 0) > 0.
Proof.
  intros l i Hsafe Hi Hpos.
  unfold count_nums_safe_108 in Hsafe.
  rewrite Forall_forall in Hsafe.
  specialize (Hsafe (Znth i l 0)).
  assert (In (Znth i l 0) l).
  { unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia. }
  specialize (Hsafe H).
  tauto.
Qed.

Lemma count_nums_safe_108_Znth_nonpos_state : forall l i,
  count_nums_safe_108 l ->
  0 <= i < Zlength l ->
  Znth i l 0 <= 0 ->
  signed_digit_sum_state_108 (Znth i l 0) (Z.abs (Znth i l 0)) 0.
Proof.
  intros l i Hsafe Hi Hnonpos.
  unfold count_nums_safe_108 in Hsafe.
  rewrite Forall_forall in Hsafe.
  specialize (Hsafe (Znth i l 0)).
  assert (In (Znth i l 0) l).
  { unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia. }
  specialize (Hsafe H).
  tauto.
Qed.

Lemma count_nums_prefix_108_init : forall input,
  count_nums_prefix_108 input 0 0.
Proof.
  intro input.
  unfold count_nums_prefix_108.
  replace (sublist 0 0 input) with (@nil Z) by (symmetry; apply sublist_nil; lia).
  simpl.
  split; [pose proof (Zlength_nonneg input); lia | reflexivity].
Qed.

Lemma count_nums_impl_snoc_true_108 : forall l x,
  sum_digits x > 0 ->
  count_nums_impl (l ++ [x]) = count_nums_impl l + 1.
Proof.
  intros l x Hx.
  unfold count_nums_impl.
  rewrite filter_app.
  simpl.
  replace (sum_digits x >? 0) with true by (symmetry; apply Z.gtb_lt; lia).
  rewrite app_length.
  simpl.
  lia.
Qed.

Lemma count_nums_impl_snoc_false_108 : forall l x,
  sum_digits x <= 0 ->
  count_nums_impl (l ++ [x]) = count_nums_impl l.
Proof.
  intros l x Hx.
  unfold count_nums_impl.
  rewrite filter_app.
  simpl.
  replace (sum_digits x >? 0) with false
    by (symmetry; destruct (Z.gtb_spec (sum_digits x) 0); lia).
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma count_nums_prefix_108_step_positive : forall input i num,
  0 <= i < Zlength input ->
  count_nums_safe_108 input ->
  count_nums_prefix_108 input i num ->
  0 < Znth i input 0 ->
  count_nums_prefix_108 input (i + 1) (num + 1).
Proof.
  intros input i num Hi Hsafe Hprefix Hpos.
  unfold count_nums_prefix_108 in *.
  destruct Hprefix as [Hbounds Hnum].
  split; [lia |].
  rewrite Hnum.
  rewrite (sublist_split 0 (i + 1) i input)
    by (try rewrite <- Zlength_correct; lia).
  rewrite (sublist_single 0 i input) by lia.
  rewrite count_nums_impl_snoc_true_108
    by (eapply count_nums_safe_108_Znth_pos_sum; eauto).
  reflexivity.
Qed.

Lemma count_nums_prefix_108_step_nonpos_true : forall input i num current sum,
  0 <= i < Zlength input ->
  current = Znth i input 0 ->
  count_nums_prefix_108 input i num ->
  signed_digit_sum_positive_108 current sum ->
  sum > 0 ->
  count_nums_prefix_108 input (i + 1) (num + 1).
Proof.
  intros input i num current sum Hi Hcur Hprefix Hsum Hpos.
  subst current.
  unfold signed_digit_sum_positive_108 in Hsum.
  unfold count_nums_prefix_108 in *.
  destruct Hprefix as [Hbounds Hnum].
  split; [lia |].
  rewrite Hnum.
  rewrite (sublist_split 0 (i + 1) i input)
    by (try rewrite <- Zlength_correct; lia).
  rewrite (sublist_single 0 i input) by lia.
  rewrite count_nums_impl_snoc_true_108 by lia.
  reflexivity.
Qed.

Lemma count_nums_prefix_108_step_nonpos_false : forall input i num current sum,
  0 <= i < Zlength input ->
  current = Znth i input 0 ->
  count_nums_prefix_108 input i num ->
  signed_digit_sum_positive_108 current sum ->
  sum <= 0 ->
  count_nums_prefix_108 input (i + 1) num.
Proof.
  intros input i num current sum Hi Hcur Hprefix Hsum Hnonpos.
  subst current.
  unfold signed_digit_sum_positive_108 in Hsum.
  unfold count_nums_prefix_108 in *.
  destruct Hprefix as [Hbounds Hnum].
  split; [lia |].
  rewrite Hnum.
  rewrite (sublist_split 0 (i + 1) i input)
    by (try rewrite <- Zlength_correct; lia).
  rewrite (sublist_single 0 i input) by lia.
  rewrite count_nums_impl_snoc_false_108 by lia.
  reflexivity.
Qed.

Lemma count_nums_prefix_108_final : forall input num,
  count_nums_prefix_108 input (Zlength input) num ->
  problem_108_spec_z input num.
Proof.
  intros input num Hprefix.
  unfold count_nums_prefix_108 in Hprefix.
  destruct Hprefix as [_ Hnum].
  unfold problem_108_spec_z, problem_108_spec.
  rewrite sublist_self in Hnum by reflexivity.
  exact Hnum.
Qed.

Lemma signed_digit_sum_state_108_step : forall current w sum,
  signed_digit_sum_state_108 current w sum ->
  10 <= w ->
  signed_digit_sum_state_108 current (Z.quot w 10) (sum + Z.rem w 10).
Proof.
  intros current w sum Hstate Hw.
  unfold signed_digit_sum_state_108 in *.
  destruct Hstate as [fuel Hfuel].
  destruct fuel as [|fuel']; simpl in Hfuel.
  - lia.
  - destruct Hfuel as [Hcur [Hw0 [Hwmax [Hsumlo [Hsumhi Hcase]]]]].
    replace (10 <=? w) with true in Hcase by (symmetry; apply Z.leb_le; lia).
    destruct Hcase as [_ [_ Hnext]].
    exists fuel'. exact Hnext.
Qed.

Lemma signed_digit_sum_state_108_final : forall current w sum,
  signed_digit_sum_state_108 current w sum ->
  w < 10 ->
  signed_digit_sum_positive_108 current (sum - w).
Proof.
  intros current w sum Hstate Hwlt.
  unfold signed_digit_sum_state_108 in Hstate.
  destruct Hstate as [fuel Hfuel].
  destruct fuel as [|fuel']; simpl in Hfuel.
  - tauto.
  - destruct Hfuel as [Hcur [Hw0 [Hwmax [Hsumlo [Hsumhi Hcase]]]]].
    replace (10 <=? w) with false in Hcase by (symmetry; apply Z.leb_gt; lia).
    tauto.
Qed.

Lemma signed_digit_sum_state_fuel_108_bounds : forall fuel current w sum,
  signed_digit_sum_state_fuel_108 fuel current w sum ->
  current <= 0 /\ 0 <= w /\ w <= INT_MAX /\ INT_MIN < sum /\ sum < INT_MAX.
Proof.
  intros fuel current w sum Hstate.
  destruct fuel; simpl in Hstate; tauto.
Qed.

Lemma signed_digit_sum_state_108_step_bounds : forall current w sum,
  signed_digit_sum_state_108 current w sum ->
  10 <= w ->
  INT_MIN < sum + Z.rem w 10 /\ sum + Z.rem w 10 < INT_MAX /\
  0 <= Z.quot w 10 /\ Z.quot w 10 <= INT_MAX.
Proof.
  intros current w sum Hstate Hw.
  unfold signed_digit_sum_state_108 in Hstate.
  destruct Hstate as [fuel Hfuel].
  destruct fuel as [|fuel']; simpl in Hfuel; [lia|].
  destruct Hfuel as [Hcur [Hw0 [Hwmax [Hsumlo [Hsumhi Hcase]]]]].
  replace (10 <=? w) with true in Hcase by (symmetry; apply Z.leb_le; lia).
  destruct Hcase as [Hlo [Hhi Hnext]].
  pose proof (signed_digit_sum_state_fuel_108_bounds _ _ _ _ Hnext)
    as [_ [Hqlo [Hqhi _]]].
  repeat split; lia.
Qed.

Lemma signed_digit_sum_state_108_final_bounds : forall current w sum,
  signed_digit_sum_state_108 current w sum ->
  w < 10 ->
  INT_MIN < sum - w /\ sum - w <= INT_MAX.
Proof.
  intros current w sum Hstate Hwlt.
  unfold signed_digit_sum_state_108 in Hstate.
  destruct Hstate as [fuel Hfuel].
  destruct fuel as [|fuel']; simpl in Hfuel.
  - tauto.
  - destruct Hfuel as [Hcur [Hw0 [Hwmax [Hsumlo [Hsumhi Hcase]]]]].
    replace (10 <=? w) with false in Hcase by (symmetry; apply Z.leb_gt; lia).
    tauto.
Qed.
