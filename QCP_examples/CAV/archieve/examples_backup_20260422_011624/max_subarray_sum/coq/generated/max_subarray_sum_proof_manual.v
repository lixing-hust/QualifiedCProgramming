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
From SimpleC.EE.CAV.verify_20260421_132710_max_subarray_sum Require Import max_subarray_sum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import max_subarray_sum.
Local Open Scope sac.

Lemma sublist_head_cons :
  forall (l : list Z) i n,
    0 <= i < n ->
    n <= Zlength l ->
    sublist i n l = Znth i l 0 :: sublist (i + 1) n l.
Proof.
  intros l i n Hi Hn.
  rewrite (sublist_split i n (i + 1) l) by (pose proof Zlength_correct l; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  simpl.
  reflexivity.
Qed.

Lemma sum_sublist_snoc :
  forall (l : list Z) lo i,
    0 <= lo <= i ->
    i < Zlength l ->
    sum (sublist lo (i + 1) l) = sum (sublist lo i l) + Znth i l 0.
Proof.
  intros l lo i Hlo Hi.
  rewrite (sublist_split lo (i + 1) i l) by (pose proof Zlength_correct l; lia).
  rewrite sum_app.
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  simpl.
  lia.
Qed.

Lemma max_subarray_sum_acc_sublist_step :
  forall (l : list Z) i n cur best,
    0 <= i < n ->
    n <= Zlength l ->
    max_subarray_sum_acc cur best (sublist i n l) =
    max_subarray_sum_acc
      (Z.max (Znth i l 0) (cur + Znth i l 0))
      (Z.max best (Z.max (Znth i l 0) (cur + Znth i l 0)))
      (sublist (i + 1) n l).
Proof.
  intros l i n cur best Hi Hn.
  rewrite sublist_head_cons by assumption.
  simpl.
  unfold max_subarray_sum_step.
  reflexivity.
Qed.

Lemma suffix_bound_new :
  forall (l : list Z) start i cur,
    0 <= start < i ->
    i < Zlength l ->
    cur = sum (sublist start i l) ->
    (forall lo, 0 <= lo < i -> sum (sublist lo i l) <= cur) ->
    cur + Znth i l 0 < Znth i l 0 ->
    forall lo, 0 <= lo < i + 1 -> sum (sublist lo (i + 1) l) <= Znth i l 0.
Proof.
  intros l start i cur Hstart Hi Hcur Hmax Hbranch lo Hlo.
  destruct (Z.eq_dec lo i).
  - subst lo.
    rewrite sum_sublist_snoc by lia.
    rewrite sublist_nil by lia.
    simpl.
    lia.
  - assert (0 <= lo < i) by lia.
    rewrite sum_sublist_snoc by lia.
    specialize (Hmax lo H).
    lia.
Qed.

Lemma suffix_bound_extend :
  forall (l : list Z) start i cur,
    0 <= start < i ->
    i < Zlength l ->
    cur = sum (sublist start i l) ->
    (forall lo, 0 <= lo < i -> sum (sublist lo i l) <= cur) ->
    cur + Znth i l 0 >= Znth i l 0 ->
    forall lo, 0 <= lo < i + 1 -> sum (sublist lo (i + 1) l) <= cur + Znth i l 0.
Proof.
  intros l start i cur Hstart Hi Hcur Hmax Hbranch lo Hlo.
  destruct (Z.eq_dec lo i).
  - subst lo.
    rewrite sum_sublist_snoc by lia.
    rewrite sublist_nil by lia.
    simpl.
    lia.
  - assert (0 <= lo < i) by lia.
    rewrite sum_sublist_snoc by lia.
    specialize (Hmax lo H).
    lia.
Qed.

Lemma proof_of_max_subarray_sum_safety_wit_4 : max_subarray_sum_safety_wit_4.
Proof.
  unfold max_subarray_sum_safety_wit_4.
  intros.
  entailer!.
  - subst cur.
    replace (sum (sublist start i l) + Znth i l 0) with
      (sum (sublist start (i + 1) l)).
    + match goal with
      | H : forall lo hi : Z, _ -> _ <= sum (sublist lo hi l) <= _ |- _ =>
          pose proof (H start (i + 1) ltac:(lia))
      end.
      lia.
    + rewrite sum_sublist_snoc by lia.
      reflexivity.
  - subst cur.
    replace (sum (sublist start i l) + Znth i l 0) with
      (sum (sublist start (i + 1) l)).
    + match goal with
      | H : forall lo hi : Z, _ -> _ <= sum (sublist lo hi l) <= _ |- _ =>
          pose proof (H start (i + 1) ltac:(lia))
      end.
      lia.
    + rewrite sum_sublist_snoc by lia.
      reflexivity.
Qed.

Lemma proof_of_max_subarray_sum_safety_wit_5 : max_subarray_sum_safety_wit_5.
Proof.
  unfold max_subarray_sum_safety_wit_5.
  intros.
  entailer!.
  - subst cur.
    replace (sum (sublist start i l) + Znth i l 0) with
      (sum (sublist start (i + 1) l)).
    + match goal with
      | H : forall lo hi : Z, _ -> _ <= sum (sublist lo hi l) <= _ |- _ =>
          pose proof (H start (i + 1) ltac:(lia))
      end.
      lia.
    + rewrite sum_sublist_snoc by lia.
      reflexivity.
  - subst cur.
    replace (sum (sublist start i l) + Znth i l 0) with
      (sum (sublist start (i + 1) l)).
    + match goal with
      | H : forall lo hi : Z, _ -> _ <= sum (sublist lo hi l) <= _ |- _ =>
          pose proof (H start (i + 1) ltac:(lia))
      end.
      lia.
    + rewrite sum_sublist_snoc by lia.
      reflexivity.
Qed.

Lemma proof_of_max_subarray_sum_entail_wit_1 : max_subarray_sum_entail_wit_1.
Proof.
  unfold max_subarray_sum_entail_wit_1.
  intros.
  Exists 0.
  entailer!.
  - assert (sublist 0 n_pre l = l).
    { rewrite <- H1. apply sublist_self. reflexivity. }
    assert (sublist 0 n_pre l = Znth 0 l 0 :: sublist 1 n_pre l).
    { rewrite sublist_head_cons by lia. reflexivity. }
    assert (l = Znth 0 l 0 :: sublist 1 n_pre l).
    { transitivity (sublist 0 n_pre l).
      - symmetry. exact H3.
      - exact H4. }
    replace (max_subarray_sum_spec l) with
      (max_subarray_sum_acc (Znth 0 l 0) (Znth 0 l 0) (sublist 1 n_pre l)).
    + reflexivity.
    + rewrite H5.
      simpl.
      change (Znth 0 (Znth 0 l 0 :: sublist 1 n_pre l) 0) with (Znth 0 l 0).
      replace (sublist 1 n_pre (Znth 0 l 0 :: sublist 1 n_pre l))
        with (sublist 1 n_pre l).
      * reflexivity.
      * rewrite sublist_cons2.
        -- replace (n_pre - 1) with (Zlength (sublist 1 n_pre l)).
           ++ replace (1 - 1) with 0 by lia.
              symmetry.
              apply sublist_self. reflexivity.
           ++ rewrite Zlength_sublist by lia. lia.
        -- lia.
        -- rewrite Zlength_cons.
           rewrite Zlength_sublist by lia.
           lia.
  - intros lo_2 Hlo.
    assert (lo_2 = 0) by lia.
    subst lo_2.
    replace (sum (sublist 0 1 l)) with (Znth 0 l 0).
    + lia.
    + change (sum (sublist 0 1 l)) with (sum (sublist 0 (0 + 1) l)).
      rewrite (sublist_single 0 l 0) by (rewrite <- Zlength_correct; lia).
      simpl.
      lia.
  - replace (sum (sublist 0 1 l)) with (Znth 0 l 0).
    + lia.
    + change (sum (sublist 0 1 l)) with (sum (sublist 0 (0 + 1) l)).
      rewrite (sublist_single 0 l 0) by (rewrite <- Zlength_correct; lia).
      simpl.
      lia.
Qed.

Lemma proof_of_max_subarray_sum_entail_wit_2_1 : max_subarray_sum_entail_wit_2_1.
Proof.
  unfold max_subarray_sum_entail_wit_2_1.
  intros.
  Exists i.
  entailer!.
  - rewrite <- H8.
    rewrite (max_subarray_sum_acc_sublist_step l i n_pre cur best) by (pose proof Zlength_correct l; lia).
    unfold max_subarray_sum_step.
    replace (Z.max (Znth i l 0) (cur + Znth i l 0)) with (Znth i l 0) by lia.
    replace (Z.max best (Znth i l 0)) with (Znth i l 0) by lia.
    reflexivity.
  - apply suffix_bound_new with (start := start_2) (cur := cur); try lia; assumption.
  - rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
    simpl.
    lia.
Qed.

Lemma proof_of_max_subarray_sum_entail_wit_2_2 : max_subarray_sum_entail_wit_2_2.
Proof.
  unfold max_subarray_sum_entail_wit_2_2.
  intros.
  Exists start_2.
  entailer!.
  - rewrite <- H8.
    rewrite (max_subarray_sum_acc_sublist_step l i n_pre cur best) by (pose proof Zlength_correct l; lia).
    unfold max_subarray_sum_step.
    replace (Z.max (Znth i l 0) (cur + Znth i l 0)) with (cur + Znth i l 0) by lia.
    replace (Z.max best (cur + Znth i l 0)) with (cur + Znth i l 0) by lia.
    reflexivity.
  - apply suffix_bound_extend with (start := start_2); try lia; assumption.
  - rewrite sum_sublist_snoc by lia.
    subst cur.
    reflexivity.
Qed.

Lemma proof_of_max_subarray_sum_entail_wit_2_3 : max_subarray_sum_entail_wit_2_3.
Proof.
  unfold max_subarray_sum_entail_wit_2_3.
  intros.
  Exists start_2.
  entailer!.
  - rewrite <- H8.
    rewrite (max_subarray_sum_acc_sublist_step l i n_pre cur best) by (pose proof Zlength_correct l; lia).
    unfold max_subarray_sum_step.
    replace (Z.max (Znth i l 0) (cur + Znth i l 0)) with (cur + Znth i l 0) by lia.
    replace (Z.max best (cur + Znth i l 0)) with best by lia.
    reflexivity.
  - apply suffix_bound_extend with (start := start_2); try lia; assumption.
  - rewrite sum_sublist_snoc by lia.
    subst cur.
    reflexivity.
Qed.

Lemma proof_of_max_subarray_sum_entail_wit_2_4 : max_subarray_sum_entail_wit_2_4.
Proof.
  unfold max_subarray_sum_entail_wit_2_4.
  intros.
  Exists i.
  entailer!.
  - rewrite <- H8.
    rewrite (max_subarray_sum_acc_sublist_step l i n_pre cur best) by (pose proof Zlength_correct l; lia).
    unfold max_subarray_sum_step.
    replace (Z.max (Znth i l 0) (cur + Znth i l 0)) with (Znth i l 0) by lia.
    replace (Z.max best (Znth i l 0)) with best by lia.
    reflexivity.
  - apply suffix_bound_new with (start := start_2) (cur := cur); try lia; assumption.
  - rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
    simpl.
    lia.
Qed.

Lemma proof_of_max_subarray_sum_return_wit_1 : max_subarray_sum_return_wit_1.
Proof.
  unfold max_subarray_sum_return_wit_1.
  intros.
  entailer!.
  assert (i = n_pre) by lia.
  subst i.
  match goal with
  | H : max_subarray_sum_acc cur best (sublist n_pre n_pre l) = max_subarray_sum_spec l |- _ =>
      rewrite sublist_nil in H by lia;
      simpl in H;
      exact H
  end.
Qed.
