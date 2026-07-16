(* You are given two positive integers n and m, and your task is to compute the
average of the integers from n through m (including n and m).
Round the answer to the nearest integer and convert that to binary.
If n is greater than m, return -1.
Example:
rounded_avg(1, 5) => "11"
rounded_avg(7, 5) => "-1"
rounded_avg(10, 20) => "1111"
rounded_avg(20, 33) => "11010" *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import GmpNumber.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

(* bit_char converts a binary digit to its ASCII character. *)
Definition bit_char (b : Z) : ascii :=
  if Z.eqb b 0 then "0"%char else "1"%char.

(* As in spec/79.v, bits are stored least-significant first.  The final
   condition gives zero its unique representation and excludes leading zeros
   from every positive representation. *)
Definition binary_digits (n : nat) (bits : list Z) : Prop :=
  list_within_bound 2 bits /\
  list_to_Z 2 bits = Z.of_nat n /\
  ((n = O /\ bits = [0]) \/
   (n <> O /\ bits <> [] /\ last bits 0 = 1)).

(* The visible binary string prints the most significant bit first. *)
Definition binary_string_from_digits (bits : list Z) : string :=
  string_of_list_ascii (map bit_char (rev bits)).

(* problem_103_pre requires positive endpoints. *)
Definition problem_103_pre (n m : Z) : Prop := n > 0 /\ m > 0.

(* A successful result relates the integer average to a natural number and
   then relates that number to its canonical binary representation. *)
Definition problem_103_spec (n m : Z) (output : string) : Prop :=
  (n > m /\ output = "-1") \/
  (exists avg bits,
     n <= m /\
     Z.of_nat avg = (n + m) / 2 /\
     binary_digits avg bits /\
     output = binary_string_from_digits bits).
