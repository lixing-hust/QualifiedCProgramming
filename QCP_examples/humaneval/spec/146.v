(* def specialFilter(nums):
"""Write a function that takes an array of numbers as input and returns
the number of elements in the array that are greater than 10 and both
first and last digits of a number are odd (1, 3, 5, 7, 9).
For example:
specialFilter([15, -73, 14, -15]) => 1
specialFilter([33, -2, -3, 45, 21, 109]) => 2
""" *)

Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Arith.Arith.
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import GmpNumber.
Import ListNotations.
Open Scope Z_scope.

(* decimal_digits follows spec/145.v: digits are stored least-significant first. *)
Definition decimal_digits (n : Z) (digits : list Z) : Prop :=
  list_within_bound 10 digits /\
  list_to_Z 10 digits = Z.abs n /\
  ((n = 0 /\ digits = [0]) \/
   (n <> 0 /\ digits <> [] /\ last digits 0 <> 0)).

(* decimal_edge_digits exposes the most and least significant decimal digits. *)
Definition decimal_edge_digits (n first last_digit : Z) : Prop :=
  exists digits,
    decimal_digits n digits /\
    first = last digits 0 /\
    last_digit = hd 0 digits.

(* Each input contributes either 1 or 0 to the final count. *)
Definition special_number_score (n score : Z) : Prop :=
  exists first last_digit,
    decimal_edge_digits n first last_digit /\
    ((10 < n /\
      Z.odd first = true /\
      Z.odd last_digit = true /\
      score = 1) \/
     ((n <= 10 \/
       Z.odd first = false \/
       Z.odd last_digit = false) /\
      score = 0)).

(* problem_146_pre accepts any integer list. *)
Definition problem_146_pre (nums : list Z) : Prop := True.

(* problem_146_spec states that output is the count of special numbers. *)
Definition problem_146_spec (nums : list Z) (output : Z) : Prop :=
  exists scores,
    Forall2 special_number_score nums scores /\
    output = fold_left Z.add scores 0.
