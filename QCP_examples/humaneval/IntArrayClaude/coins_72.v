Load "../spec/72".

From AUXLib Require Import List_lemma ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.

Import naive_C_Rules.
Local Open Scope Z_scope.

Definition problem_72_pre_z (q : list Z) (w : Z) : Prop :=
  problem_72_pre q w.

Definition mirror_all (q : list Z) : Prop :=
  forall k,
    0 <= k < Zlength q ->
    Znth k q 0 = Znth (Zlength q - 1 - k) q 0.

Definition problem_72_spec_z (q : list Z) (w out : Z) : Prop :=
  (out <> 0 <-> mirror_all q /\ sum q <= w).

Definition will_it_fly_int_range (q : list Z) : Prop :=
  forall i,
    0 <= i <= Zlength q ->
    INT_MIN <= sum (sublist 0 i q) <= INT_MAX.

Lemma fold_left_Zadd_sum : forall l acc,
  fold_left Z.add l acc = acc + sum l.
Proof.
  induction l; intros; simpl.
  - lia.
  - rewrite IHl. simpl. lia.
Qed.

Lemma fold_left_Zadd_0_sum : forall l,
  fold_left Z.add l 0 = sum l.
Proof.
  intros. rewrite fold_left_Zadd_sum. lia.
Qed.

Lemma sum_sublist_0 : forall l,
  sum (sublist 0 0 l) = 0.
Proof.
  intros. rewrite sublist_nil by lia. reflexivity.
Qed.

Lemma sum_sublist_snoc : forall l i,
  0 <= i < Zlength l ->
  sum (sublist 0 i l) + Znth i l 0 = sum (sublist 0 (i + 1) l).
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l)
    by (try rewrite <- Zlength_correct; lia).
  rewrite (sublist_single i l 0) by (rewrite Zlength_correct in Hi; lia).
  rewrite sum_app. simpl. lia.
Qed.

Lemma mirror_prefix_extend : forall q n i,
  n = Zlength q ->
  0 <= i < n ->
  (forall k, 0 <= k < i -> Znth k q 0 = Znth (n - 1 - k) q 0) ->
  Znth i q 0 = Znth (n - 1 - i) q 0 ->
  forall k, 0 <= k < i + 1 -> Znth k q 0 = Znth (n - 1 - k) q 0.
Proof.
  intros q n i Hn Hi Hprefix Hi_eq k Hk.
  destruct (Z.eq_dec k i) as [-> | Hneq].
  - exact Hi_eq.
  - apply Hprefix. lia.
Qed.

Lemma mirror_prefix_mismatch_spec_false : forall q w n i,
  n = Zlength q ->
  0 <= i < n ->
  (forall k, 0 <= k < i -> Znth k q 0 = Znth (n - 1 - k) q 0) ->
  Znth i q 0 <> Znth (n - 1 - i) q 0 ->
  problem_72_spec_z q w 0.
Proof.
  intros q w n i Hn Hi _ Hneq.
  unfold problem_72_spec_z, mirror_all.
  split; intro H.
  - lia.
  - destruct H as [Hmirror _].
    specialize (Hmirror i).
    rewrite <- Hn in Hmirror.
    exfalso.
    apply Hneq. apply Hmirror. lia.
Qed.

Lemma mirror_prefix_full : forall q n i,
  n = Zlength q ->
  i >= n ->
  (forall k, 0 <= k < i -> Znth k q 0 = Znth (n - 1 - k) q 0) ->
  mirror_all q.
Proof.
  intros q n i Hn Hi Hprefix k Hk.
  unfold mirror_all.
  rewrite <- Hn in Hk.
  rewrite <- Hn.
  apply Hprefix. lia.
Qed.

Lemma problem_72_spec_z_weight_false : forall q w,
  mirror_all q ->
  sum q > w ->
  problem_72_spec_z q w 0.
Proof.
  intros q w Hmirror Hgt.
  unfold problem_72_spec_z.
  split; intro H.
  - lia.
  - destruct H as [_ Hsum]. lia.
Qed.

Lemma problem_72_spec_z_true : forall q w,
  mirror_all q ->
  sum q <= w ->
  problem_72_spec_z q w 1.
Proof.
  intros q w Hmirror Hsum.
  unfold problem_72_spec_z.
  split; intro H.
  - split; auto.
  - lia.
Qed.
