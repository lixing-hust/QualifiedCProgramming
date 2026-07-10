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
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* sum_decimal_digits sums decimal digits by enumerating enough digit positions. *)
Definition sum_decimal_digits (n : nat) : nat :=
  fold_left Nat.add (map (fun p => (n / Nat.pow 10 p) mod 10) (seq 0 n)) 0.

(* bit_char converts a binary digit to its ASCII character. *)
Definition bit_char (b : nat) : ascii :=
  if Nat.eqb b 0 then "0"%char else "1"%char.

(* msb_pos returns the highest non-zero binary position, defaulting to 0. *)
Definition msb_pos (n : nat) : nat :=
  fst
    (fold_left
       (fun acc p =>
          let b := (n / Nat.pow 2 p) mod 2 in
          if Nat.eqb b 0 then acc else (p, b))
       (seq 0 (S n))
       (0, 0)).

(* nat_to_binary_string converts n to binary using finite bit-position enumeration. *)
Definition nat_to_binary_string (n : nat) : string :=
  if Nat.eqb n 0 then "0"
  else
    string_of_list_ascii
      (map (fun p => bit_char ((n / Nat.pow 2 p) mod 2)) (rev (seq 0 (S (msb_pos n))))).

(* solve_impl converts the decimal digit sum of N to binary. *)
Definition solve_impl (N : nat) : string :=
  nat_to_binary_string (sum_decimal_digits N).

(* problem_84_pre keeps the benchmark input bound. *)
Definition problem_84_pre (N : nat) : Prop := (N <= 10000)%nat.

(* problem_84_spec states that output is the binary digit-sum string. *)
Definition problem_84_spec (N : nat) (output : string) : Prop :=
  output = solve_impl N.
