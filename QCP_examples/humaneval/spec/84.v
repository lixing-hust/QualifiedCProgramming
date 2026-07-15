(* def solve(N):
"""Given a positive integer N, return the total sum of its digits in binary.

Example
For N = 1000, the sum of digits will be 1 the output should be "1".
For N = 150, the sum of digits will be 6 the output should be "110".
For N = 147, the sum of digits will be 12 the output should be "1100".

Variables:
@N integer
Constraints: 0 ≤ N ≤ 10000.
Output:
a string of binary number
""" *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import GmpNumber.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

(* decimal_digits follows spec/79.v's GmpNumber digit-list style:
   digits are stored least-significant first. *)
Definition decimal_digits (N : nat) (digits : list Z) : Prop :=
  list_within_bound 10 digits /\
  list_to_Z 10 digits = Z.of_nat N /\
  ((N = 0%nat /\ digits = [0]) \/
   (N <> 0%nat /\ digits <> [] /\ last digits 0 <> 0)).

(* digit_sum_list sums a decimal digit list. *)
Definition digit_sum_list (digits : list Z) : Z :=
  fold_left Z.add digits 0.

(* decimal_digit_sum relates N to the sum of its decimal digits. *)
Definition decimal_digit_sum (N : nat) (sum : Z) : Prop :=
  exists digits,
    decimal_digits N digits /\
    sum = digit_sum_list digits.

(* bit_char converts a binary digit to its ASCII character. *)
Definition bit_char (b : Z) : ascii :=
  if Z.eqb b 0 then "0"%char else "1"%char.

(* binary_digits uses the same canonical low-digit-first positional encoding as spec/79.v. *)
Definition binary_digits (n : Z) (bits : list Z) : Prop :=
  list_within_bound 2 bits /\
  list_to_Z 2 bits = n /\
  ((n = 0 /\ bits = [0]) \/
   (n <> 0 /\ bits <> [] /\ last bits 0 = 1)).

(* The visible binary string prints the most significant bit first. *)
Definition binary_string_from_digits (bits : list Z) : string :=
  string_of_list_ascii (map bit_char (rev bits)).

(* problem_84_pre keeps the benchmark input bound. *)
Definition problem_84_pre (N : nat) : Prop := (N <= 10000)%nat.

(* problem_84_spec relates output to the canonical binary string of the decimal digit sum. *)
Definition problem_84_spec (N : nat) (output : string) : Prop :=
  exists sum bits,
    decimal_digit_sum N sum /\
    binary_digits sum bits /\
    output = binary_string_from_digits bits.
