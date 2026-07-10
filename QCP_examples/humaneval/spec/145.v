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
Import ListNotations.
Open Scope Z_scope.

(* digit_fuel_145 documents the original benchmark's bounded digit range. *)
Definition digit_fuel_145 : nat := 8%nat.

(* decimal_digit returns the digit at decimal position p of a non-negative number. *)
Definition decimal_digit (n : Z) (p : nat) : Z :=
  (n / Z.of_nat (Nat.pow 10 p)) mod 10.

(* msd_pos returns the highest position with a non-zero digit, defaulting to 0. *)
Definition msd_pos (n : Z) : nat :=
  fst
    (fold_left
       (fun acc p =>
          let d := decimal_digit n p in
          if d =? 0 then acc else (p, d))
       (seq 0 (S digit_fuel_145))
       (0%nat, 0)).

(* digit_sum_abs sums the decimal digits of a non-negative number. *)
Definition digit_sum_abs (n : Z) : Z :=
  fold_left Z.add (map (decimal_digit n) (seq 0 (S (msd_pos n)))) 0.

(* sum_digits treats the most significant digit of a negative number as signed. *)
Definition sum_digits (n : Z) : Z :=
  let t := Z.abs n in
  if n <? 0
  then digit_sum_abs t - 2 * decimal_digit t (msd_pos t)
  else digit_sum_abs t.

(* le_stable orders indexed values by digit sum and keeps original-index ties stable. *)
Definition le_stable (p1 p2 : Z * nat) : Prop :=
  let (z1, i1) := p1 in
  let (z2, i2) := p2 in
  let s1 := sum_digits z1 in
  let s2 := sum_digits z2 in
  s1 < s2 \/ (s1 = s2 /\ (i1 <= i2)%nat).

(* indexed attaches each input element to its original zero-based position. *)
Definition indexed (l_in : list Z) : list (Z * nat) :=
  combine l_in (seq 0 (length l_in)).

(* problem_145_pre accepts any integer list. *)
Definition problem_145_pre (l_in : list Z) : Prop := True.

(* problem_145_spec characterizes stable sorting by signed digit sum. *)
Definition problem_145_spec (l_in : list Z) (output : list Z) : Prop :=
  exists indexed_output,
    Permutation indexed_output (indexed l_in) /\
    Sorted le_stable indexed_output /\
    output = map fst indexed_output.
