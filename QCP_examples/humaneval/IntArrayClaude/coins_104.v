Load "../spec/104".

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

Definition problem_104_pre_z (l : list Z) : Prop :=
  Forall (fun n => 0 < n < INT_MAX) l.

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

Fixpoint zero_list_nat (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => 0 :: zero_list_nat n'
  end.

Definition zero_list (n : Z) : list Z :=
  zero_list_nat (Z.to_nat n).

Lemma zero_list_nat_length : forall n,
  length (zero_list_nat n) = n.
Proof.
  induction n; simpl; lia.
Qed.

Lemma zero_list_Zlength : forall n,
  0 <= n ->
  Zlength (zero_list n) = n.
Proof.
  intros n Hn.
  unfold zero_list.
  rewrite Zlength_correct.
  rewrite zero_list_nat_length.
  lia.
Qed.

Inductive odd_digit_scan_state (original : Z) : Z -> Z -> Prop :=
| odd_scan_init :
    0 < original ->
    odd_digit_scan_state original original 1
| odd_scan_zero :
    odd_digit_scan_state original 0 0
| odd_scan_even :
    forall num,
      odd_digit_scan_state original num 1 ->
      0 < num ->
      num mod 2 = 0 ->
      odd_digit_scan_state original (num / 10) 0
| odd_scan_odd :
    forall num,
      odd_digit_scan_state original num 1 ->
      0 < num ->
      num mod 2 <> 0 ->
      odd_digit_scan_state original (num / 10) 1.

Definition only_odd_digits_z (n : Z) : Prop :=
  exists num, odd_digit_scan_state n num 1 /\ num <= 0.

Definition has_even_digit_z (n : Z) : Prop :=
  exists num, odd_digit_scan_state n num 0.

Inductive unique_digits_prefix (input : list Z) : Z -> list Z -> Prop :=
| unique_digits_prefix_nil :
    unique_digits_prefix input 0 []
| unique_digits_prefix_add :
    forall i output,
      0 <= i < Zlength input ->
      unique_digits_prefix input i output ->
      only_odd_digits_z (Znth i input 0) ->
      unique_digits_prefix input (i + 1) (output ++ [Znth i input 0])
| unique_digits_prefix_skip :
    forall i output,
      0 <= i < Zlength input ->
      unique_digits_prefix input i output ->
      has_even_digit_z (Znth i input 0) ->
      unique_digits_prefix input (i + 1) output.

Definition problem_104_spec_z (input output : list Z) : Prop :=
  exists filtered,
    unique_digits_prefix input (Zlength input) filtered /\
    sorted_int_list_by 1 output /\
    Permutation filtered output.

Lemma problem_104_pre_z_Znth : forall l i,
  problem_104_pre_z l ->
  0 <= i < Zlength l ->
  0 < Znth i l 0 < INT_MAX.
Proof.
  intros l i Hpre Hi.
  unfold problem_104_pre_z in Hpre.
  rewrite Forall_forall in Hpre.
  apply Hpre.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma odd_digit_scan_state_bounds : forall original num u,
  0 <= original ->
  odd_digit_scan_state original num u ->
  0 <= num <= original /\ (u = 0 \/ u = 1).
Proof.
  intros original num u Horig Hstate.
  induction Hstate.
  - split; lia.
  - split; lia.
  - destruct IHHstate as [Hbounds Hu].
    split.
    + assert (0 <= num / 10) by (apply Z.div_pos; lia).
      assert (num / 10 <= num).
      {
        apply Z.div_le_upper_bound; lia.
      }
      lia.
    + lia.
  - destruct IHHstate as [Hbounds Hu].
    split.
    + assert (0 <= num / 10) by (apply Z.div_pos; lia).
      assert (num / 10 <= num).
      {
        apply Z.div_le_upper_bound; lia.
      }
      lia.
    + lia.
Qed.

Lemma only_odd_digits_done : forall original num u,
  odd_digit_scan_state original num u ->
  (u = 0 \/ u = 1) ->
  num <= 0 ->
  u <> 0 ->
  only_odd_digits_z original.
Proof.
  intros original num u Hstate Hu01 Hnum Hu.
  exists num.
  split.
  - replace u with 1 in Hstate by lia.
    exact Hstate.
  - exact Hnum.
Qed.

Lemma has_even_digit_done : forall original num u,
  odd_digit_scan_state original num u ->
  u = 0 ->
  has_even_digit_z original.
Proof.
  intros original num u Hstate Hu.
  exists num.
  replace u with 0 in Hstate by lia.
  exact Hstate.
Qed.

Lemma odd_scan_even_quot : forall original num,
  odd_digit_scan_state original num 1 ->
  0 < num ->
  num % 2 = 0 ->
  odd_digit_scan_state original (num ÷ 10) 0.
Proof.
  intros original num Hstate Hpos Heven.
  replace (num ÷ 10) with (num / 10).
  - apply odd_scan_even with (num := num); try assumption.
    rewrite Z.rem_mod_nonneg in Heven by lia.
    exact Heven.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.

Lemma odd_scan_odd_quot : forall original num,
  odd_digit_scan_state original num 1 ->
  0 < num ->
  num % 2 <> 0 ->
  odd_digit_scan_state original (num ÷ 10) 1.
Proof.
  intros original num Hstate Hpos Hodd.
  replace (num ÷ 10) with (num / 10).
  - apply odd_scan_odd with (num := num); try assumption.
    intro Hmod.
    apply Hodd.
    rewrite Z.rem_mod_nonneg by lia.
    exact Hmod.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.

Lemma unique_digits_prefix_add_step : forall input i output,
  0 <= i < Zlength input ->
  unique_digits_prefix input i output ->
  only_odd_digits_z (Znth i input 0) ->
  unique_digits_prefix input (i + 1) (output ++ [Znth i input 0]).
Proof.
  intros.
  apply unique_digits_prefix_add; assumption.
Qed.

Lemma unique_digits_prefix_skip_step : forall input i output,
  0 <= i < Zlength input ->
  unique_digits_prefix input i output ->
  has_even_digit_z (Znth i input 0) ->
  unique_digits_prefix input (i + 1) output.
Proof.
  intros.
  apply unique_digits_prefix_skip; assumption.
Qed.

Lemma problem_104_spec_z_of_sorted : forall input filtered output,
  unique_digits_prefix input (Zlength input) filtered ->
  sorted_int_list_by 1 output ->
  Permutation filtered output ->
  problem_104_spec_z input output.
Proof.
  intros.
  exists filtered.
  repeat split; assumption.
Qed.
