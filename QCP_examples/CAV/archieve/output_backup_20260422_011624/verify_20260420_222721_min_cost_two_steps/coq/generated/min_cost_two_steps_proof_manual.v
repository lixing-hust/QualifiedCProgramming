Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260420_222721_min_cost_two_steps Require Import min_cost_two_steps_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import min_cost_two_steps.
Local Open Scope sac.
Local Close Scope sac.

Fixpoint min_cost_two_steps_prev_acc (prev2 prev1 : Z) (l : list Z) : Z :=
  match l with
  | nil => prev2
  | x :: xs => min_cost_two_steps_prev_acc prev1 (Z.min prev1 prev2 + x) xs
  end.

Lemma min_cost_acc_snoc : forall xs x prev2 prev1,
  min_cost_two_steps_acc prev2 prev1 (xs ++ x :: nil) =
  Z.min (min_cost_two_steps_acc prev2 prev1 xs)
        (min_cost_two_steps_prev_acc prev2 prev1 xs) + x.
Proof.
  induction xs; intros; simpl.
  - lia.
  - rewrite IHxs. reflexivity.
Qed.

Lemma min_cost_acc_prefix_prev : forall xs prev2 prev1,
  1 <= Zlength xs ->
  min_cost_two_steps_acc prev2 prev1 (sublist 0 (Zlength xs - 1) xs) =
  min_cost_two_steps_prev_acc prev2 prev1 xs.
Proof.
  induction xs; intros prev2 prev1 Hlen.
  - rewrite Zlength_nil in Hlen. lia.
  - destruct xs.
    + simpl.
      replace (Zlength (a :: nil) - 1) with 0 by
        (rewrite Zlength_cons, Zlength_nil; lia).
      simpl. reflexivity.
    + rewrite sublist_cons1 by
        (rewrite Zlength_cons, Zlength_cons; pose proof Zlength_nonneg xs; lia).
      simpl.
      rewrite !Zlength_cons.
      replace (Z.succ (Z.succ (Zlength xs)) - 1 - 1)
        with (Z.succ (Zlength xs) - 1) by lia.
      replace (Z.succ (Zlength xs) - 1) with (Zlength (z :: xs) - 1) by
        (rewrite Zlength_cons; lia).
      rewrite IHxs by
        (rewrite Zlength_cons; pose proof Zlength_nonneg xs; lia).
      reflexivity.
Qed.

Lemma min_cost_prev_acc_prefix : forall rest a b,
  min_cost_two_steps_z (sublist 0 (Zlength (a :: b :: rest) - 1) (a :: b :: rest)) =
  min_cost_two_steps_prev_acc a (a + b) rest.
Proof.
  intros rest a b. destruct rest.
  - simpl.
    replace (Zlength (a :: b :: nil) - 1) with 1 by
      (rewrite Zlength_cons, Zlength_cons, Zlength_nil; lia).
    simpl. reflexivity.
  - rewrite sublist_cons1 by
      (repeat rewrite Zlength_cons; pose proof Zlength_nonneg rest; lia).
    rewrite sublist_cons1 by
      (repeat rewrite Zlength_cons; pose proof Zlength_nonneg rest; lia).
    simpl.
    rewrite !Zlength_cons.
    replace (Z.succ (Z.succ (Z.succ (Zlength rest))) - 1 - 1 - 1)
      with (Z.succ (Zlength rest) - 1) by lia.
    replace (Z.succ (Zlength rest) - 1) with (Zlength (z :: rest) - 1) by
      (rewrite Zlength_cons; lia).
    rewrite min_cost_acc_prefix_prev by
      (rewrite Zlength_cons; pose proof Zlength_nonneg rest; lia).
    reflexivity.
Qed.

Lemma min_cost_two_steps_z_snoc : forall xs x,
  2 <= Zlength xs ->
  min_cost_two_steps_z (xs ++ x :: nil) =
  Z.min (min_cost_two_steps_z xs)
        (min_cost_two_steps_z (sublist 0 (Zlength xs - 1) xs)) + x.
Proof.
  intros xs x Hlen. destruct xs.
  - rewrite Zlength_nil in Hlen. lia.
  - destruct xs.
    + rewrite Zlength_cons, Zlength_nil in Hlen. lia.
    + simpl. rewrite min_cost_acc_snoc. rewrite min_cost_prev_acc_prefix. reflexivity.
Qed.

Lemma min_cost_two_steps_z_prefix_snoc : forall l i,
  2 <= i < Zlength l ->
  min_cost_two_steps_z (sublist 0 (i + 1) l) =
  Z.min (min_cost_two_steps_z (sublist 0 i l))
        (min_cost_two_steps_z (sublist 0 (i - 1) l)) + Znth i l 0.
Proof.
  intros l i Hi.
  pose proof (Zlength_correct l).
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single i l 0) by lia.
  rewrite min_cost_two_steps_z_snoc.
  - replace (Zlength (sublist 0 i l) - 1) with (i - 1) by
      (rewrite Zlength_sublist by lia; lia).
    rewrite sublist_sublist00 by lia.
    reflexivity.
  - rewrite Zlength_sublist by lia. lia.
Qed.

Lemma sum_nonneg_by_Znth : forall l,
  (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0) ->
  0 <= sum l.
Proof.
  induction l; intros Hall.
  - simpl. lia.
  - simpl.
    assert (Ha : 0 <= a).
    { specialize (Hall 0). rewrite Zlength_cons in Hall.
      pose proof Zlength_nonneg l. simpl in Hall. apply Hall. lia. }
    assert (Htail : 0 <= sum l).
    {
      apply IHl. intros i Hi.
      specialize (Hall (i + 1)).
      rewrite Zlength_cons in Hall.
      rewrite Znth_cons in Hall by lia.
      replace (i + 1 - 1) with i in Hall by lia.
      apply Hall. lia.
    }
    lia.
Qed.

Lemma sum_prefix_le_full_nonneg : forall l k,
  0 <= k <= Zlength l ->
  (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0) ->
  sum (sublist 0 k l) <= sum l.
Proof.
  intros l k Hk Hall.
  pose proof (Zlength_correct l) as Hzlen.
  rewrite <- (sublist_self l (Zlength l)) at 2 by reflexivity.
  rewrite (sublist_split 0 (Zlength l) k l) by
    lia.
  rewrite sum_app.
  assert (0 <= sum (sublist k (Zlength l) l)).
  {
    apply sum_nonneg_by_Znth. intros i Hi.
    rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist by lia.
    apply Hall. lia.
  }
  lia.
Qed.

Lemma sum_prefix_snoc : forall l i,
  0 <= i < Zlength l ->
  sum (sublist 0 (i + 1) l) = sum (sublist 0 i l) + Znth i l 0.
Proof.
  intros l i Hi.
  pose proof (Zlength_correct l) as Hzlen.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite sum_app.
  rewrite (sublist_single i l 0) by lia.
  simpl. lia.
Qed.

Lemma sublist_0_1_by_Znth : forall l,
  1 <= Zlength l ->
  sublist 0 1 l = Znth 0 l 0 :: nil.
Proof.
  intros l Hlen.
  change 1 with (0 + 1).
  pose proof (Zlength_correct l).
  apply (sublist_single 0 l 0). lia.
Qed.

Lemma sublist_0_2_by_Znth : forall l,
  2 <= Zlength l ->
  sublist 0 2 l = Znth 0 l 0 :: Znth 1 l 0 :: nil.
Proof.
  intros l Hlen.
  pose proof (Zlength_correct l).
  rewrite (sublist_split 0 2 1 l) by lia.
  rewrite sublist_0_1_by_Znth by lia.
  replace (sublist 1 2 l) with (sublist 1 (1 + 1) l) by
    (replace (1 + 1) with 2 by lia; reflexivity).
  rewrite (sublist_single 1 l 0) by lia.
  reflexivity.
Qed.

Lemma proof_of_min_cost_two_steps_safety_wit_4 : min_cost_two_steps_safety_wit_4.
Proof.
  pre_process; entailer!; try lia.
  - assert (0 <= Znth 0 l 0) by (apply H3; lia).
    assert (0 <= Znth 1 l 0) by (apply H3; lia).
    lia.
  - assert (2 <= n_pre) by lia.
    assert (Hpref : sum (sublist 0 2 l) <= sum l).
    { apply sum_prefix_le_full_nonneg.
      - lia.
      - intros j Hj. apply H3. rewrite <- H2. exact Hj. }
    assert (Hsum2 : sum (sublist 0 2 l) = Znth 0 l 0 + Znth 1 l 0).
    {
      remember l as ll.
      destruct ll.
      - simpl. reflexivity.
      - destruct ll.
        + unfold Znth. simpl. lia.
        + unfold Znth. simpl. lia.
    }
    lia.
Qed.

Lemma proof_of_min_cost_two_steps_safety_wit_8 : min_cost_two_steps_safety_wit_8.
Proof.
  pre_process; entailer!; try lia.
  - match goal with
    | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
        pose proof (H i ltac:(lia))
    end; lia.
  - match goal with
    | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
        pose proof (H i ltac:(lia))
    end.
    assert (Hpref : sum (sublist 0 (i + 1) l) <= sum l).
    { apply sum_prefix_le_full_nonneg.
      - lia.
      - intros j Hj.
        match goal with
        | H : forall k : Z, 0 <= k < n_pre -> 0 <= Znth k l 0 |- _ =>
            apply H; rewrite <- H12; exact Hj
        end. }
    rewrite sum_prefix_snoc in Hpref by lia.
    lia.
Qed.

Lemma proof_of_min_cost_two_steps_safety_wit_9 : min_cost_two_steps_safety_wit_9.
Proof.
  pre_process; entailer!; try lia.
  - match goal with
    | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
        pose proof (H i ltac:(lia))
    end; lia.
  - match goal with
    | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
        pose proof (H i ltac:(lia))
    end.
    assert (Hpref : sum (sublist 0 (i + 1) l) <= sum l).
    { apply sum_prefix_le_full_nonneg.
      - lia.
      - intros j Hj.
        match goal with
        | H : forall k : Z, 0 <= k < n_pre -> 0 <= Znth k l 0 |- _ =>
            apply H; rewrite <- H12; exact Hj
        end. }
    rewrite sum_prefix_snoc in Hpref by lia.
    assert (sum (sublist 0 (i - 1) l) <= sum (sublist 0 i l)).
    {
      replace i with ((i - 1) + 1) at 2 by lia.
      rewrite sum_prefix_snoc by lia.
      match goal with
      | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
          pose proof (H (i - 1) ltac:(lia))
      end.
      lia.
    }
    lia.
Qed.

Lemma proof_of_min_cost_two_steps_entail_wit_1 : min_cost_two_steps_entail_wit_1.
Proof.
  pre_process; entailer!; try lia.
  - rewrite sublist_0_2_by_Znth by lia. simpl. lia.
  - pose proof (H3 0 ltac:(lia)).
    pose proof (H3 1 ltac:(lia)).
    lia.
  - replace (2 - 1) with 1 by lia.
    rewrite sublist_0_1_by_Znth by lia. simpl. lia.
  - apply H3. lia.
  - rewrite sublist_0_2_by_Znth by lia. simpl. reflexivity.
  - replace (2 - 1) with 1 by lia.
    rewrite sublist_0_1_by_Znth by lia. simpl. reflexivity.
Qed.

Lemma proof_of_min_cost_two_steps_entail_wit_2_1 : min_cost_two_steps_entail_wit_2_1.
Proof.
  pre_process; entailer!; try lia.
  - apply store_int_undef_store_int.
  - match goal with
    | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
        pose proof (H i_2 ltac:(lia))
    end.
    rewrite sum_prefix_snoc by lia.
    lia.
  - match goal with
    | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
        pose proof (H i_2 ltac:(lia))
    end; lia.
  - replace (i_2 + 1 - 1) with i_2 by lia.
    match goal with
    | H : prev1 <= sum (sublist 0 i_2 l) |- _ => exact H
    end.
  - rewrite min_cost_two_steps_z_prefix_snoc by lia.
    rewrite <- H4.
    rewrite <- H3.
    rewrite Z.min_l by lia.
    reflexivity.
  - replace (i_2 + 1 - 1) with i_2 by lia.
    match goal with
    | H : prev1 = min_cost_two_steps_z (sublist 0 i_2 l) |- _ => exact H
    end.
Qed.

Lemma proof_of_min_cost_two_steps_entail_wit_2_2 : min_cost_two_steps_entail_wit_2_2.
Proof.
  pre_process; entailer!; try lia.
  - apply store_int_undef_store_int.
  - match goal with
    | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
        pose proof (H i_2 ltac:(lia))
    end.
    rewrite sum_prefix_snoc by lia.
    assert (sum (sublist 0 (i_2 - 1) l) <= sum (sublist 0 i_2 l)).
    {
      replace i_2 with ((i_2 - 1) + 1) at 2 by lia.
      rewrite sum_prefix_snoc by lia.
      match goal with
      | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
          pose proof (H (i_2 - 1) ltac:(lia))
      end.
      lia.
    }
    lia.
  - match goal with
    | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
        pose proof (H i_2 ltac:(lia))
    end; lia.
  - replace (i_2 + 1 - 1) with i_2 by lia.
    match goal with
    | H : prev1 <= sum (sublist 0 i_2 l) |- _ => exact H
    end.
  - rewrite min_cost_two_steps_z_prefix_snoc by lia.
    rewrite <- H4.
    rewrite <- H3.
    rewrite Z.min_r by lia.
    reflexivity.
  - replace (i_2 + 1 - 1) with i_2 by lia.
    match goal with
    | H : prev1 = min_cost_two_steps_z (sublist 0 i_2 l) |- _ => exact H
    end.
Qed.

Lemma proof_of_min_cost_two_steps_return_wit_2 : min_cost_two_steps_return_wit_2.
Proof.
  pre_process; entailer!; try lia.
  assert (i_2 = n_pre) by lia.
  subst i_2.
  match goal with
  | Hprev : prev1 = min_cost_two_steps_z (sublist 0 n_pre l),
    Hlen : Zlength l = n_pre |- _ =>
      rewrite Hprev; f_equal; rewrite <- Hlen; apply sublist_self; reflexivity
  end.
Qed.
