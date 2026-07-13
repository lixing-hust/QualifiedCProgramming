(* def order_by_points(nums):
"""
Write a function which sorts the given list of integers
in ascending order according to the sum of their digits.
Note: if there are several items with similar sum of their digits,
order them based on their index in original list.

For example:
>>> order_by_points([1, 11, -1, -11, -12]) == [-1, -11, 1, -12, 11]
>>> order_by_points([]) == []
""" *)

Require Import ZArith.
Require Import Coq.Lists.List.
Require Import Permutation.
Require Import Sorting.Sorted.
Require Import Arith.
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import GmpNumber.
Import ListNotations.
Open Scope Z_scope.

(* decimal_digits is the canonical decimal representation of |n|. *)
Definition decimal_digits (n : Z) (digits : list Z) : Prop :=
  list_within_bound 10 digits /\
  list_to_Z 10 digits = Z.abs n /\
  ((n = 0 /\ digits = [0]) \/
   (n <> 0 /\ digits <> [] /\ last digits 0 <> 0)).

(* digit_sum_list sums a decimal digit list. *)
Definition digit_sum_list (digits : list Z) : Z :=
  fold_left Z.add digits 0.

(* signed_digit_sum treats the most significant digit of a negative number as signed. *)
Definition signed_digit_sum (n sum : Z) : Prop :=
  exists digits,
    decimal_digits n digits /\
    ((n < 0 /\
      sum = digit_sum_list (removelast digits) - last digits 0) \/
     (0 <= n /\
      sum = digit_sum_list digits)).

(* le_digit_sum orders values by signed digit sum. *)
Definition le_digit_sum (z1 z2 : Z) : Prop :=
  exists s1 s2,
    signed_digit_sum z1 s1 /\
    signed_digit_sum z2 s2 /\
    s1 <= s2.

Definition scored_by_digit_sum (values scores : list Z) : Prop :=
  length values = length scores /\
  forall i x s,
    nth_error values i = Some x ->
    nth_error scores i = Some s ->
    signed_digit_sum x s.

Definition score_eqb (s : Z) (p : Z * Z) : bool :=
  Z.eqb (snd p) s.

(* stable_digit_sum_order keeps the input order inside each equal-sum group. *)
Definition stable_digit_sum_order (l_in output : list Z) : Prop :=
  exists input_scores output_scores,
    scored_by_digit_sum l_in input_scores /\
    scored_by_digit_sum output output_scores /\
    forall s,
      filter (score_eqb s) (combine output output_scores) =
      filter (score_eqb s) (combine l_in input_scores).

(* problem_145_pre accepts any integer list. *)
Definition problem_145_pre (l_in : list Z) : Prop := True.

(* problem_145_spec characterizes stable sorting by signed digit sum. *)
Definition problem_145_spec (l_in : list Z) (output : list Z) : Prop :=
  Permutation output l_in /\
  Sorted le_digit_sum output /\
  stable_digit_sum_order l_in output.
