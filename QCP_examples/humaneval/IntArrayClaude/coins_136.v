Load "../spec/136".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import List_lemma.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition neg_option_of_value (x : Z) : option Z :=
  if x =? 0 then None else Some x.

Definition pos_option_of_value (x : Z) : option Z :=
  if x =? 0 then None else Some x.

Definition largest_negative_state (l : list Z) (maxneg : Z) : Prop :=
  (maxneg = 0 /\ forall x, In x l -> ~ x < 0) \/
  (maxneg < 0 /\ In maxneg l /\ forall x, In x l -> x < 0 -> x <= maxneg).

Definition smallest_positive_state (l : list Z) (minpos : Z) : Prop :=
  (minpos = 0 /\ forall x, In x l -> ~ x > 0) \/
  (minpos > 0 /\ In minpos l /\ forall x, In x l -> x > 0 -> minpos <= x).

Definition largest_smallest_prefix (i : Z) (l : list Z) (maxneg minpos : Z) : Prop :=
  0 <= i <= Zlength l /\
  largest_negative_state (sublist 0 i l) maxneg /\
  smallest_positive_state (sublist 0 i l) minpos.

Definition problem_136_pre_z (l : list Z) : Prop :=
  problem_136_pre l.

Definition problem_136_spec_z (l out : list Z) : Prop :=
  exists maxneg minpos,
    out = maxneg :: minpos :: nil /\
    largest_smallest_prefix (Zlength l) l maxneg minpos /\
    problem_136_spec l (neg_option_of_value maxneg, pos_option_of_value minpos).

Lemma sublist_snoc_Znth_136 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ Znth i l 0 :: nil.
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i) by
    (try lia; rewrite <- Zlength_correct; lia).
  replace (sublist i (i + 1) l) with (Znth i l 0 :: nil).
  - reflexivity.
  - rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
    reflexivity.
Qed.

Lemma largest_negative_state_nil :
  largest_negative_state nil 0.
Proof.
  left.
  split; [reflexivity|].
  intros x H.
  contradiction.
Qed.

Lemma smallest_positive_state_nil :
  smallest_positive_state nil 0.
Proof.
  left.
  split; [reflexivity|].
  intros x H.
  contradiction.
Qed.

Lemma largest_smallest_prefix_init : forall l,
  0 <= Zlength l ->
  largest_smallest_prefix 0 l 0 0.
Proof.
  intros l Hlen.
  unfold largest_smallest_prefix.
  rewrite sublist_nil by lia.
  repeat split; try lia.
  - apply largest_negative_state_nil.
  - apply smallest_positive_state_nil.
Qed.

Lemma largest_negative_update_zero : forall s maxneg x,
  largest_negative_state s maxneg ->
  x < 0 ->
  maxneg = 0 ->
  largest_negative_state (s ++ x :: nil) x.
Proof.
  intros s maxneg x Hstate Hx Hmax.
  destruct Hstate as [[Hz Hnone] | [Hneg [Hin Hmaximal]]]; subst maxneg; try lia.
  right.
  repeat split; try lia.
  - apply in_or_app.
    right; simpl; auto.
  - intros y Hy Hyneg.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    specialize (Hnone y Hy).
    contradiction.
Qed.

Lemma largest_negative_update_bigger : forall s maxneg x,
  largest_negative_state s maxneg ->
  x < 0 ->
  maxneg <> 0 ->
  maxneg < x ->
  largest_negative_state (s ++ x :: nil) x.
Proof.
  intros s maxneg x Hstate Hx Hnonzero Hgt.
  destruct Hstate as [[Hz _] | [Hneg [Hin Hmaximal]]]; [contradiction|].
  right.
  repeat split; try lia.
  - apply in_or_app.
    right; simpl; auto.
  - intros y Hy Hyneg.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    specialize (Hmaximal y Hy Hyneg).
    lia.
Qed.

Lemma largest_negative_keep_nonneg : forall s maxneg x,
  largest_negative_state s maxneg ->
  x >= 0 ->
  largest_negative_state (s ++ x :: nil) maxneg.
Proof.
  intros s maxneg x Hstate Hx.
  destruct Hstate as [[Hz Hnone] | [Hneg [Hin Hmaximal]]].
  - left.
    split; [assumption|].
    intros y Hy Hyneg.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    apply (Hnone y Hy Hyneg).
  - right.
    repeat split; try assumption.
    + apply in_or_app; left; assumption.
    + intros y Hy Hyneg.
      apply in_app_or in Hy.
      destruct Hy as [Hy | [Hy | []]]; subst; try lia.
      apply Hmaximal; assumption.
Qed.

Lemma largest_negative_keep_not_bigger : forall s maxneg x,
  largest_negative_state s maxneg ->
  x < 0 ->
  maxneg <> 0 ->
  x <= maxneg ->
  largest_negative_state (s ++ x :: nil) maxneg.
Proof.
  intros s maxneg x Hstate Hx Hnonzero Hle.
  destruct Hstate as [[Hz _] | [Hneg [Hin Hmaximal]]]; [contradiction|].
  right.
  repeat split; try assumption.
  - apply in_or_app; left; assumption.
  - intros y Hy Hyneg.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    apply Hmaximal; assumption.
Qed.

Lemma smallest_positive_update_zero : forall s minpos x,
  smallest_positive_state s minpos ->
  x > 0 ->
  minpos = 0 ->
  smallest_positive_state (s ++ x :: nil) x.
Proof.
  intros s minpos x Hstate Hx Hmin.
  destruct Hstate as [[Hz Hnone] | [Hpos [Hin Hminimal]]]; subst minpos; try lia.
  right.
  repeat split; try lia.
  - apply in_or_app.
    right; simpl; auto.
  - intros y Hy Hypos.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    specialize (Hnone y Hy).
    contradiction.
Qed.

Lemma smallest_positive_update_smaller : forall s minpos x,
  smallest_positive_state s minpos ->
  x > 0 ->
  minpos <> 0 ->
  x < minpos ->
  smallest_positive_state (s ++ x :: nil) x.
Proof.
  intros s minpos x Hstate Hx Hnonzero Hlt.
  destruct Hstate as [[Hz _] | [Hpos [Hin Hminimal]]]; [contradiction|].
  right.
  repeat split; try lia.
  - apply in_or_app.
    right; simpl; auto.
  - intros y Hy Hypos.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    specialize (Hminimal y Hy Hypos).
    lia.
Qed.

Lemma smallest_positive_keep_nonpos : forall s minpos x,
  smallest_positive_state s minpos ->
  x <= 0 ->
  smallest_positive_state (s ++ x :: nil) minpos.
Proof.
  intros s minpos x Hstate Hx.
  destruct Hstate as [[Hz Hnone] | [Hpos [Hin Hminimal]]].
  - left.
    split; [assumption|].
    intros y Hy Hypos.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    apply (Hnone y Hy Hypos).
  - right.
    repeat split; try assumption.
    + apply in_or_app; left; assumption.
    + intros y Hy Hypos.
      apply in_app_or in Hy.
      destruct Hy as [Hy | [Hy | []]]; subst; try lia.
      apply Hminimal; assumption.
Qed.

Lemma smallest_positive_keep_not_smaller : forall s minpos x,
  smallest_positive_state s minpos ->
  x > 0 ->
  minpos <> 0 ->
  minpos <= x ->
  smallest_positive_state (s ++ x :: nil) minpos.
Proof.
  intros s minpos x Hstate Hx Hnonzero Hle.
  destruct Hstate as [[Hz _] | [Hpos [Hin Hminimal]]]; [contradiction|].
  right.
  repeat split; try assumption.
  - apply in_or_app; left; assumption.
  - intros y Hy Hypos.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    apply Hminimal; assumption.
Qed.

Lemma largest_smallest_prefix_step : forall i l maxneg minpos maxneg' minpos',
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  largest_negative_state (sublist 0 (i + 1) l) maxneg' ->
  smallest_positive_state (sublist 0 (i + 1) l) minpos' ->
  largest_smallest_prefix (i + 1) l maxneg' minpos'.
Proof.
  intros i l maxneg minpos maxneg' minpos' Hi Hpre Hneg Hpos.
  unfold largest_smallest_prefix in *.
  repeat split; try lia; assumption.
Qed.

Lemma largest_smallest_prefix_min_zero : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 > 0 ->
  minpos = 0 ->
  largest_smallest_prefix (i + 1) l maxneg (Znth i l 0).
Proof.
  intros i l maxneg minpos Hi Hpre Hx Hmin.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
    rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_keep_nonneg; [assumption|lia].
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_update_zero with (minpos := minpos); assumption.
Qed.

Lemma largest_smallest_prefix_min_smaller : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 > 0 ->
  minpos <> 0 ->
  Znth i l 0 < minpos ->
  largest_smallest_prefix (i + 1) l maxneg (Znth i l 0).
Proof.
  intros i l maxneg minpos Hi Hpre Hx Hnonzero Hlt.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
    rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_keep_nonneg; [assumption|lia].
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_update_smaller with (minpos := minpos); assumption.
Qed.

Lemma largest_smallest_prefix_max_zero : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 < 0 ->
  maxneg = 0 ->
  largest_smallest_prefix (i + 1) l (Znth i l 0) minpos.
Proof.
  intros i l maxneg minpos Hi Hpre Hx Hmax.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_update_zero with (maxneg := maxneg); assumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_keep_nonpos; [assumption|lia].
Qed.

Lemma largest_smallest_prefix_max_bigger : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 < 0 ->
  maxneg <> 0 ->
  maxneg < Znth i l 0 ->
  largest_smallest_prefix (i + 1) l (Znth i l 0) minpos.
Proof.
  intros i l maxneg minpos Hi Hpre Hx Hnonzero Hgt.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_update_bigger with (maxneg := maxneg); assumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_keep_nonpos; [assumption|lia].
Qed.

Lemma largest_smallest_prefix_keep_zero : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 = 0 ->
  largest_smallest_prefix (i + 1) l maxneg minpos.
Proof.
  intros i l maxneg minpos Hi Hpre Hx.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_keep_nonneg; [assumption|lia].
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_keep_nonpos; [assumption|lia].
Qed.

Lemma largest_smallest_prefix_keep_negative : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 < 0 ->
  maxneg <> 0 ->
  Znth i l 0 <= maxneg ->
  largest_smallest_prefix (i + 1) l maxneg minpos.
Proof.
  intros i l maxneg minpos Hi Hpre Hx Hnonzero Hle.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_keep_not_bigger; assumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_keep_nonpos; [assumption|lia].
Qed.

Lemma largest_smallest_prefix_keep_positive : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 > 0 ->
  minpos <> 0 ->
  minpos <= Znth i l 0 ->
  largest_smallest_prefix (i + 1) l maxneg minpos.
Proof.
  intros i l maxneg minpos Hi Hpre Hx Hnonzero Hle.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_keep_nonneg; [assumption|lia].
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_keep_not_smaller; assumption.
Qed.

Lemma largest_smallest_prefix_full_spec : forall l maxneg minpos,
  largest_smallest_prefix (Zlength l) l maxneg minpos ->
  problem_136_spec l (neg_option_of_value maxneg, pos_option_of_value minpos).
Proof.
  intros l maxneg minpos Hpre.
  unfold largest_smallest_prefix in Hpre.
  destruct Hpre as [_ [Hneg Hpos]].
  rewrite sublist_self in Hneg by lia.
  rewrite sublist_self in Hpos by lia.
  unfold problem_136_spec.
  split.
  - unfold neg_option_of_value.
    destruct (maxneg =? 0) eqn:Heq.
    + apply Z.eqb_eq in Heq.
      subst maxneg.
      destruct Hneg as [[_ Hnone] | [Hlt _]]; try lia.
      exact Hnone.
    + apply Z.eqb_neq in Heq.
      destruct Hneg as [[Hz _] | Hsome]; try contradiction.
      exact Hsome.
  - unfold pos_option_of_value.
    destruct (minpos =? 0) eqn:Heq.
    + apply Z.eqb_eq in Heq.
      subst minpos.
      destruct Hpos as [[_ Hnone] | [Hgt _]]; try lia.
      exact Hnone.
    + apply Z.eqb_neq in Heq.
      destruct Hpos as [[Hz _] | Hsome]; try contradiction.
      exact Hsome.
Qed.
