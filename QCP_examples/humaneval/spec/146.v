(* def specialFilter(nums):
"""Write a function that takes an array of numbers as input and returns
the number of elements in the array that are greater than 10 and both
first and last digits of a number are odd (1, 3, 5, 7, 9).
For example:
specialFilter([15, -73, 14, -15]) => 1
specialFilter([33, -2, -3, 45, 21, 109]) => 2
""" *)

Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.Ascii Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

(* last_digit returns the final decimal digit of the absolute value. *)
Definition last_digit (n : Z) : Z := Z.abs (n mod 10).

(* decimal_digit returns the digit at decimal position p of a non-negative number. *)
Definition decimal_digit (n : Z) (p : nat) : Z :=
  (n / Z.of_nat (Nat.pow 10 p)) mod 10.

(* msd returns the most significant decimal digit by keeping the last non-zero digit. *)
Definition msd (n : Z) : Z :=
  snd
    (fold_left
       (fun acc p =>
          let d := decimal_digit n p in
          if d =? 0 then acc else (p, d))
       (seq 0 (Z.to_nat n + 1))
       (0%nat, 0)).

(* special_number_b recognizes values greater than 10 whose first and last digits are odd. *)
Definition special_number_b (n : Z) : bool :=
  let abs_n := Z.abs n in (10 <? n) && (Z.odd (msd abs_n)) && (Z.odd (last_digit abs_n)).

(* specialFilter_impl counts special numbers in the input list. *)
Definition specialFilter_impl (nums : list Z) : Z := Z.of_nat (length (filter special_number_b nums)).

(* problem_146_pre accepts any integer list. *)
Definition problem_146_pre (nums : list Z) : Prop := True.

(* problem_146_spec states that output is the count of special numbers. *)
Definition problem_146_spec (nums : list Z) (output : Z) : Prop :=
  output = specialFilter_impl nums.
