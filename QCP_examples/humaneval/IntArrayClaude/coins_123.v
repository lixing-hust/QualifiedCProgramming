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
  exists raw_l,
    odd_collatz_prefix n 1 raw_l /\
    sorted_int_list_by 1 result /\
    Permutation raw_l result.

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

Lemma problem_123_spec_z_of_sorted : forall original raw_l sorted_l,
  odd_collatz_prefix original 1 raw_l ->
  sorted_int_list_by 1 sorted_l ->
  Permutation raw_l sorted_l ->
  problem_123_spec_z original sorted_l.
Proof.
  intros.
  exists raw_l.
  repeat split; assumption.
Qed.
