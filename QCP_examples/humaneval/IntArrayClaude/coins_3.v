Load "../spec/3".

From AUXLib Require Import List_lemma ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Coq.micromega.Lia.

Import naive_C_Rules.
Local Open Scope Z_scope.

Definition list_int_range (l: list Z) (n: Z) : Prop :=
  forall i, 0 <= i < n -> INT_MIN <= Znth i l 0 <= INT_MAX.

Definition prefix_sums_int_range (l: list Z) (n: Z) : Prop :=
  forall k, 0 <= k <= n -> INT_MIN <= sum (sublist 0 k l) <= INT_MAX.

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

Lemma problem_3_spec_true_of_negative_prefix : forall l k,
  0 <= k < Zlength l ->
  sum (sublist 0 (k + 1) l) < 0 ->
  problem_3_spec l true.
Proof.
  intros l k Hk Hneg.
  unfold problem_3_spec.
  split; intro H; auto.
  exists (sublist 0 (k + 1) l), (sublist (k + 1) (Zlength l) l).
  split.
  - rewrite <- (sublist_split 0 (Zlength l) (k + 1) l)
      by (try rewrite <- Zlength_correct; lia).
    rewrite sublist_self by reflexivity.
    reflexivity.
  - rewrite fold_left_Zadd_0_sum.
    exact Hneg.
Qed.

Lemma problem_3_spec_false_of_all_prefix_nonneg : forall l,
  (forall k, 0 <= k < Zlength l ->
     0 <= sum (sublist 0 (k + 1) l)) ->
  problem_3_spec l false.
Proof.
  intros l Hall.
  unfold problem_3_spec.
  split; intro H.
  - destruct H as [prefix [suffix [Happ Hneg]]].
    destruct prefix as [ | z xs ].
    + simpl in Hneg. lia.
    + rewrite fold_left_Zadd_0_sum in Hneg.
      subst l.
      assert (Hlen_pos: 0 < Zlength (z :: xs)).
      { rewrite Zlength_correct. simpl. lia. }
      assert (Hlen_le: Zlength (z :: xs) <= Zlength ((z :: xs) ++ suffix)).
      {
        rewrite !Zlength_correct.
        rewrite length_app.
        simpl.
        lia.
      }
      assert (Hprefix: sublist 0 (Zlength (z :: xs)) ((z :: xs) ++ suffix) = z :: xs).
      {
        rewrite sublist_app_exact1.
        reflexivity.
      }
      specialize (Hall (Zlength (z :: xs) - 1)).
      assert (0 <= Zlength (z :: xs) - 1 < Zlength ((z :: xs) ++ suffix)) by lia.
      specialize (Hall H).
      replace (Zlength (z :: xs) - 1 + 1) with (Zlength (z :: xs)) in Hall by lia.
      rewrite Hprefix in Hall.
      lia.
  - discriminate H.
Qed.
