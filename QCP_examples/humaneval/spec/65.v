(* def circular_shift(x, shift):
"""Circular shift the digits of the integer x, shift the digits right by shift
and return the result as a string.
If shift > number of digits, return digits reversed.
>>> circular_shift(12, 1)
"21"
>>> circular_shift(12, 2)
"12"
""" *)

Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.
From SimpleC.EE.Applications_human.minigmp_sumlib Require Import GmpNumber.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

(* decimal_digits relates x to its decimal digits in reading order. *)
Definition decimal_digits (x : nat) (digits : list Z) : Prop :=
  list_within_bound 10 (rev digits) /\
  list_to_Z 10 (rev digits) = Z.of_nat x /\
  ((x = 0%nat /\ digits = [0]) \/
   (x <> 0%nat /\ digits <> [] /\ hd 0 digits <> 0)).

(* digit_ascii maps one decimal digit to its character. *)
Definition digit_ascii (d : Z) : ascii :=
  ascii_of_nat (Z.to_nat (48 + d)).

(* digits_to_string maps l1 to a character list and then uses the stdlib
   string/list conversion, so leading zero digits are preserved. *)
Definition digits_to_string (digits : list Z) : string :=
  string_of_list_ascii (map digit_ascii digits).

(* digits_string relates shifted digits l1 to the returned string. *)
Definition digits_string (digits : list Z) (result : string) : Prop :=
  result = digits_to_string digits.

(* circular_shift_digits relates l and l1 by the source index of each output digit. *)
Definition circular_shift_digits
    (digits : list Z) (shift : nat) (output_digits : list Z) : Prop :=
  let len := Zlength digits in
  Zlength output_digits = len /\
  forall i,
    0 <= i < len ->
    Znth i output_digits 0 =
    if (len <? Z.of_nat shift)%Z then
      Znth (len - 1 - i) digits 0
    else
      Znth ((len - (Z.of_nat shift mod len) + i) mod len) digits 0.

(* problem_65_pre imposes no input constraints. *)
Definition problem_65_pre (x : nat) (shift : nat) : Prop := True.

(* problem_65_spec characterizes the output through digit relations. *)
Definition problem_65_spec (x : nat) (shift : nat) (result : string) : Prop :=
  exists digits output_digits,
    decimal_digits x digits /\
    circular_shift_digits digits shift output_digits /\
    digits_string output_digits result.
