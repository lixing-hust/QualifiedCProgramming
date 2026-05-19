Load "../spec/123".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import naive_C_Rules.
Import ListNotations.
Local Open Scope Z_scope.

Inductive odd_collatz_prefix (original : Z) : Z -> list Z -> Prop :=
| odd_collatz_init :
    0 < original ->
    odd_collatz_prefix original original [1]
| odd_collatz_odd :
    forall n l,
      odd_collatz_prefix original n l ->
      n <> 1 ->
      n mod 2 = 1 ->
      odd_collatz_prefix original (3 * n + 1) (l ++ [n])
| odd_collatz_even :
    forall n l,
      odd_collatz_prefix original n l ->
      n <> 1 ->
      n mod 2 = 0 ->
      odd_collatz_prefix original (n / 2) l.

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

Definition problem_123_spec_z (n : Z) (result : list Z) : Prop :=
  problem_123_spec n result.

Inductive collatz_list_to (original : Z) : Z -> list Z -> Prop :=
| collatz_list_to_init :
    collatz_list_to original original []
| collatz_list_to_odd :
    forall n seq,
      collatz_list_to original n seq ->
      n <> 1 ->
      n mod 2 = 1 ->
      collatz_list_to original (3 * n + 1) (seq ++ [n])
| collatz_list_to_even :
    forall n seq,
      collatz_list_to original n seq ->
      n <> 1 ->
      n mod 2 = 0 ->
      collatz_list_to original (n / 2) (seq ++ [n]).

Definition collatz_step_safe (original current : Z) (output : list Z) : Prop :=
  odd_collatz_prefix original current output ->
  0 < current < INT_MAX /\
  0 < 3 * current + 1 < INT_MAX /\
  (current <> 1 -> Zlength output < 1024) /\
  (current mod 2 = 0 ->
     0 < current / 2 < INT_MAX).

Definition problem_123_pre_z (n : Z) : Prop :=
  0 < n < INT_MAX /\
  forall current output,
    collatz_step_safe n current output.

Lemma problem_123_pre_z_initial : forall n,
  problem_123_pre_z n ->
  0 < n < INT_MAX /\ odd_collatz_prefix n n [1].
Proof.
  intros n Hpre.
  destruct Hpre as [Hn _].
  split; [assumption | constructor; lia].
Qed.

Lemma collatz_step_safe_of_pre : forall original current output,
  problem_123_pre_z original ->
  odd_collatz_prefix original current output ->
  0 < current < INT_MAX /\
  0 < 3 * current + 1 < INT_MAX /\
  (current <> 1 -> Zlength output < 1024) /\
  (current mod 2 = 0 ->
     0 < current / 2 < INT_MAX).
Proof.
  intros original current output Hpre Hprefix.
  destruct Hpre as [_ Hsafe].
  unfold collatz_step_safe in Hsafe.
  apply Hsafe; assumption.
Qed.

Lemma Z_rem_2_eq_1_to_mod : forall n,
  0 < n ->
  n % 2 = 1 ->
  n mod 2 = 1.
Proof.
  intros n Hn Hrem.
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  exact Hrem.
Qed.

Lemma Z_rem_2_neq_1_to_mod_0 : forall n,
  0 < n ->
  n % 2 <> 1 ->
  n mod 2 = 0.
Proof.
  intros n Hn Hrem.
  assert (Hmod_bound : 0 <= n mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  lia.
Qed.

Lemma odd_collatz_odd_quot_step : forall original n output,
  odd_collatz_prefix original n output ->
  n <> 1 ->
  0 < n ->
  n % 2 = 1 ->
  odd_collatz_prefix original (n * 3 + 1) (output ++ [n]).
Proof.
  intros original n output Hprefix Hnot1 Hpos Hodd.
  replace (n * 3 + 1) with (3 * n + 1) by lia.
  apply odd_collatz_odd; try assumption.
  apply Z_rem_2_eq_1_to_mod; assumption.
Qed.

Lemma odd_collatz_even_quot_step : forall original n output,
  odd_collatz_prefix original n output ->
  n <> 1 ->
  0 < n ->
  n % 2 <> 1 ->
  odd_collatz_prefix original (n ÷ 2) output.
Proof.
  intros original n output Hprefix Hnot1 Hpos Heven.
  replace (n ÷ 2) with (n / 2).
  - apply odd_collatz_even; try assumption.
    apply Z_rem_2_neq_1_to_mod_0; assumption.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.

Lemma Zmod_1_even_false_123 : forall n,
  n mod 2 = 1 ->
  Z.even n = false.
Proof.
  intros n Hmod.
  rewrite Zmod_odd in Hmod.
  destruct (Z.odd n) eqn:Hodd.
  - rewrite <- Z.negb_odd.
    rewrite Hodd.
    reflexivity.
  - discriminate.
Qed.

Lemma Zmod_0_even_true_123 : forall n,
  n mod 2 = 0 ->
  Z.even n = true.
Proof.
  intros n Hmod.
  rewrite Zeven_mod.
  apply Zeq_is_eq_bool.
  exact Hmod.
Qed.

Lemma collatz_aux_app_path_123 : forall original current seq,
  collatz_list_to original current seq ->
  forall fuel,
    collatz_aux original (length seq + fuel)%nat =
    seq ++ collatz_aux current fuel.
Proof.
  intros original current seq Hpath.
  induction Hpath; intros fuel.
  - reflexivity.
  - rewrite app_length.
    simpl.
    replace (length seq + 1 + fuel)%nat with (length seq + S fuel)%nat by lia.
    rewrite IHHpath.
    simpl.
    destruct (n =? 1) eqn:Hn1.
    { apply Z.eqb_eq in Hn1. contradiction. }
    rewrite Zmod_1_even_false_123 by assumption.
    replace (n * 3 + 1) with (3 * n + 1) by lia.
    rewrite <- app_assoc.
    reflexivity.
  - rewrite app_length.
    simpl.
    replace (length seq + 1 + fuel)%nat with (length seq + S fuel)%nat by lia.
    rewrite IHHpath.
    simpl.
    destruct (n =? 1) eqn:Hn1.
    { apply Z.eqb_eq in Hn1. contradiction. }
    rewrite Zmod_0_even_true_123 by assumption.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma collatz_list_to_collatz_list_123 : forall original seq,
  collatz_list_to original 1 seq ->
  collatz_list original (seq ++ [1]).
Proof.
  intros original seq Hpath.
  unfold collatz_list.
  exists (length seq + 1)%nat.
  split.
  - rewrite collatz_aux_app_path_123 with (current := 1) (seq := seq) by assumption.
    simpl.
    reflexivity.
  - rewrite last_last.
    reflexivity.
Qed.

Lemma filter_odd_app_123 : forall l x,
  filter (fun x => Z.odd x) (l ++ [x]) =
  filter (fun x => Z.odd x) l ++
  if Z.odd x then [x] else [].
Proof.
  intros l x.
  rewrite filter_app.
  simpl.
  destruct (Z.odd x); reflexivity.
Qed.

Lemma odd_collatz_prefix_path_123 : forall original current raw_l,
  odd_collatz_prefix original current raw_l ->
  exists seq,
    collatz_list_to original current seq /\
    Permutation raw_l (1 :: filter (fun x => Z.odd x) seq).
Proof.
  intros original current raw_l Hprefix.
  induction Hprefix.
  - exists [].
    split.
    + constructor.
    + reflexivity.
  - destruct IHHprefix as [seq [Hpath Hperm]].
    exists (seq ++ [n]).
    split.
    + apply collatz_list_to_odd; assumption.
    + rewrite filter_odd_app_123.
      match goal with H : n mod 2 = 1 |- _ => rewrite Zmod_odd in H end.
      destruct (Z.odd n) eqn:Hodd.
      * simpl.
        eapply Permutation_trans.
        -- apply Permutation_app; [exact Hperm|reflexivity].
        -- reflexivity.
      * discriminate.
  - destruct IHHprefix as [seq [Hpath Hperm]].
    exists (seq ++ [n]).
    split.
    + apply collatz_list_to_even; assumption.
    + rewrite filter_odd_app_123.
      match goal with H : n mod 2 = 0 |- _ => rewrite Zmod_even in H end.
      destruct (Z.even n) eqn:Heven.
      * assert (Hodd : Z.odd n = false).
        {
          rewrite <- Z.negb_even.
          rewrite Heven.
          reflexivity.
        }
        rewrite Hodd.
        rewrite app_nil_r.
        exact Hperm.
      * discriminate.
Qed.

Lemma odd_collatz_prefix_original_spec_123 : forall original raw_l,
  odd_collatz_prefix original 1 raw_l ->
  exists c_seq,
    collatz_list original c_seq /\
    Permutation raw_l (filter (fun x => Z.odd x) c_seq).
Proof.
  intros original raw_l Hprefix.
  destruct (odd_collatz_prefix_path_123 _ _ _ Hprefix) as [seq [Hpath Hperm]].
  exists (seq ++ [1]).
  split.
  - apply collatz_list_to_collatz_list_123.
    exact Hpath.
  - rewrite filter_odd_app_123.
    simpl.
    eapply Permutation_trans.
    + exact Hperm.
    + rewrite <- (app_nil_r (1 :: filter (fun x : Z => Z.odd x) seq)).
      apply Permutation_middle.
Qed.

Lemma problem_123_spec_z_of_sorted : forall original raw_l sorted_l,
  odd_collatz_prefix original 1 raw_l ->
  sorted_int_list_by 1 sorted_l ->
  Permutation raw_l sorted_l ->
  problem_123_spec_z original sorted_l.
Proof.
  intros original raw_l sorted_l Hprefix Hsorted Hperm.
  unfold problem_123_spec_z, problem_123_spec.
  destruct (odd_collatz_prefix_original_spec_123 _ _ Hprefix)
    as [c_seq [Hcollatz Hraw_filter]].
  exists c_seq.
  repeat split.
  - exact Hcollatz.
  - eapply Permutation_trans.
    + apply Permutation_sym. exact Hperm.
    + exact Hraw_filter.
  - unfold sorted_int_list_by in Hsorted.
    simpl in Hsorted.
    exact Hsorted.
Qed.
