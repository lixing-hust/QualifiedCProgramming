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
From SimpleC.EE.CAV.verify_20260421_134943_house_robber Require Import house_robber_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import house_robber.
Local Open Scope sac.
Local Close Scope sac.

Fixpoint house_robber_prev_acc (prev2 prev1 : Z) (l : list Z) : Z :=
  match l with
  | nil => prev2
  | x :: xs =>
      let cur := Z.max (prev2 + x) prev1 in
      house_robber_prev_acc prev1 cur xs
  end.

Lemma house_robber_acc_snoc : forall xs x prev2 prev1,
  house_robber_acc prev2 prev1 (xs ++ x :: nil) =
  Z.max (house_robber_prev_acc prev2 prev1 xs + x)
        (house_robber_acc prev2 prev1 xs).
Proof.
  induction xs; intros; simpl.
  - reflexivity.
  - rewrite IHxs. reflexivity.
Qed.

Lemma house_robber_acc_prev_prefix : forall xs prev2 prev1,
  1 <= Zlength xs ->
  house_robber_acc prev2 prev1 (sublist 0 (Zlength xs - 1) xs) =
  house_robber_prev_acc prev2 prev1 xs.
Proof.
  induction xs; intros prev2 prev1 Hlen.
  - rewrite Zlength_nil in Hlen. lia.
  - destruct xs.
    + simpl.
      replace (Z.succ 0 - 1) with 0 by lia.
      simpl. reflexivity.
    + rewrite sublist_cons1 by
        (rewrite Zlength_cons, Zlength_cons; pose proof Zlength_nonneg xs; lia).
      simpl.
      rewrite !Zlength_cons.
      replace (Z.succ (Z.succ (Zlength xs)) - 1 - 1)
        with (Z.succ (Zlength xs) - 1) by lia.
      replace (Z.succ (Zlength xs) - 1)
        with (Zlength (z :: xs) - 1) by
        (rewrite Zlength_cons; lia).
      rewrite IHxs by
        (rewrite Zlength_cons; pose proof Zlength_nonneg xs; lia).
      reflexivity.
Qed.

Lemma house_robber_spec_prev_prefix : forall xs,
  house_robber_spec (sublist 0 (Zlength xs - 1) xs) =
  house_robber_prev_acc 0 0 xs.
Proof.
  intros xs.
  destruct xs.
  - simpl. reflexivity.
  - unfold house_robber_spec.
    apply house_robber_acc_prev_prefix.
    rewrite Zlength_cons. pose proof Zlength_nonneg xs. lia.
Qed.

Lemma house_robber_spec_snoc : forall xs x,
  house_robber_spec (xs ++ x :: nil) =
  Z.max (house_robber_spec (sublist 0 (Zlength xs - 1) xs) + x)
        (house_robber_spec xs).
Proof.
  intros xs x.
  unfold house_robber_spec.
  rewrite house_robber_acc_snoc.
  rewrite house_robber_spec_prev_prefix.
  reflexivity.
Qed.

Lemma house_robber_spec_prefix_snoc : forall l i,
  0 <= i < Zlength l ->
  house_robber_spec (sublist 0 (i + 1) l) =
  Z.max (house_robber_spec (sublist 0 (i - 1) l) + Znth i l 0)
        (house_robber_spec (sublist 0 i l)).
Proof.
  intros l i Hi.
  pose proof (Zlength_correct l).
  destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
  - subst i.
    rewrite (sublist_single 0 l 0) by lia.
    replace (sublist 0 (0 - 1) l) with (@nil Z) by
      (unfold sublist; simpl; reflexivity).
    replace (sublist 0 0 l) with (@nil Z) by
      (unfold sublist; simpl; reflexivity).
    unfold house_robber_spec. simpl. reflexivity.
  - assert (1 <= i) by lia.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single i l 0) by lia.
  rewrite house_robber_spec_snoc.
  replace (Zlength (sublist 0 i l) - 1) with (i - 1) by
    (rewrite Zlength_sublist by lia; lia).
  rewrite sublist_sublist00 by lia.
  reflexivity.
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
  pose proof (Zlength_correct l).
  rewrite <- (sublist_self l (Zlength l)) at 2 by reflexivity.
  rewrite (sublist_split 0 (Zlength l) k l) by lia.
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
  pose proof (Zlength_correct l).
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite sum_app.
  rewrite (sublist_single i l 0) by lia.
  simpl. lia.
Qed.

Lemma proof_of_house_robber_safety_wit_4 : house_robber_safety_wit_4.
Proof.
  pre_process; entailer!; try lia.
  - match goal with
    | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
        pose proof (H i ltac:(lia))
    end.
    lia.
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
            apply H; rewrite <- H10; exact Hj
        end. }
    rewrite sum_prefix_snoc in Hpref by lia.
    lia.
Qed.

Lemma proof_of_house_robber_entail_wit_1 : house_robber_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  all: unfold sublist; simpl; lia.
Qed.

Lemma proof_of_house_robber_entail_wit_2_1 : house_robber_entail_wit_2_1.
Proof.
  pre_process.
  sep_apply store_int_undef_store_int.
  sep_apply store_int_undef_store_int.
  entailer!.
  - match goal with
    | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
        pose proof (H i_2 ltac:(lia))
    end.
    rewrite sum_prefix_snoc by lia.
    lia.
  - match goal with
    | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
        pose proof (H i_2 ltac:(lia))
    end.
    rewrite sum_prefix_snoc by lia.
    lia.
  - replace (i_2 + 1 - 1) with i_2 by lia.
    assumption.
  - rewrite house_robber_spec_prefix_snoc by lia.
    rewrite <- H3.
    rewrite <- H4.
    symmetry. apply Z.max_l. lia.
Qed.

Lemma proof_of_house_robber_entail_wit_2_2 : house_robber_entail_wit_2_2.
Proof.
  pre_process.
  sep_apply store_int_undef_store_int.
  sep_apply store_int_undef_store_int.
  entailer!.
  - match goal with
    | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
        pose proof (H i_2 ltac:(lia))
    end.
    rewrite sum_prefix_snoc by lia.
    lia.
  - match goal with
    | H : forall j : Z, 0 <= j < n_pre -> 0 <= Znth j l 0 |- _ =>
        pose proof (H i_2 ltac:(lia))
    end.
    rewrite sum_prefix_snoc by lia.
    lia.
  - replace (i_2 + 1 - 1) with i_2 by lia.
    assumption.
  - rewrite house_robber_spec_prefix_snoc by lia.
    rewrite <- H3.
    rewrite <- H4.
    symmetry. apply Z.max_r. lia.
Qed.

Lemma proof_of_house_robber_return_wit_1 : house_robber_return_wit_1.
Proof.
  pre_process.
  entailer!.
  assert (i_2 = n_pre) by lia.
  subst i_2.
  rewrite H2.
  f_equal.
  apply sublist_self.
  symmetry. assumption.
Qed.
