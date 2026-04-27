Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition problem_126_pre_z (l : list Z) : Prop := True.

Definition sorted_no_triple_prefix (i : Z) (l : list Z) : Prop :=
  (forall j, 1 <= j < i -> Znth (j - 1) l 0 <= Znth j l 0) /\
  (forall j, 2 <= j < i ->
    ~ (Znth j l 0 = Znth (j - 1) l 0 /\ Znth j l 0 = Znth (j - 2) l 0)).

Definition problem_126_spec_z (l : list Z) (b : bool) : Prop :=
  if b then sorted_no_triple_prefix (Zlength l) l
  else ~ sorted_no_triple_prefix (Zlength l) l.

Lemma sorted_no_triple_prefix_1 : forall l,
  sorted_no_triple_prefix 1 l.
Proof.
  intros l.
  unfold sorted_no_triple_prefix.
  split; intros j Hj; lia.
Qed.

Lemma sorted_no_triple_prefix_step : forall l i,
  1 <= i ->
  sorted_no_triple_prefix i l ->
  Znth (i - 1) l 0 <= Znth i l 0 ->
  ~ (2 <= i /\ Znth i l 0 = Znth (i - 1) l 0 /\ Znth i l 0 = Znth (i - 2) l 0) ->
  sorted_no_triple_prefix (i + 1) l.
Proof.
  intros l i Hi [Hsorted Htriple] Hle Hnot.
  unfold sorted_no_triple_prefix.
  split.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hne].
    + exact Hle.
    + apply Hsorted. lia.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hne].
    + intro Hbad. apply Hnot. tauto.
    + apply Htriple. lia.
Qed.

Lemma problem_126_spec_false_of_desc : forall l i,
  1 <= i ->
  i < Zlength l ->
  Znth i l 0 < Znth (i - 1) l 0 ->
  problem_126_spec_z l false.
Proof.
  intros l i Hi Hlen Hlt.
  unfold problem_126_spec_z.
  intro Hprefix.
  destruct Hprefix as [Hsorted _].
  pose proof (Hsorted i ltac:(lia)).
  lia.
Qed.

Lemma problem_126_spec_false_of_triple : forall l i,
  2 <= i ->
  i < Zlength l ->
  Znth i l 0 = Znth (i - 1) l 0 ->
  Znth i l 0 = Znth (i - 2) l 0 ->
  problem_126_spec_z l false.
Proof.
  intros l i Hi Hlen Heq1 Heq2.
  unfold problem_126_spec_z.
  intro Hprefix.
  destruct Hprefix as [_ Htriple].
  pose proof (Htriple i ltac:(lia)) as Hnot.
  apply Hnot.
  split; assumption.
Qed.

Lemma problem_126_spec_true_of_exit : forall l i,
  i >= Zlength l ->
  i <= Zlength l ->
  sorted_no_triple_prefix i l ->
  problem_126_spec_z l true.
Proof.
  intros l i Hge Hle Hprefix.
  unfold problem_126_spec_z.
  replace i with (Zlength l) in Hprefix by lia.
  exact Hprefix.
Qed.
