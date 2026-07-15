
(* def hex_key(num):
"""You have been tasked to write a function that receives
a hexadecimal number as a string and counts the number of hexadecimal
digits that are primes (prime number, or a prime, is a natural number
greater than 1 that is not a product of two smaller natural numbers).
Hexadecimal digits are 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F.
Prime numbers are 2, 3, 5, 7, 11, 13, 17,...
So you have to determine a number of the following digits: 2, 3, 5, 7,
B (=decimal 11), D (=decimal 13).
Note: you may assume the input is always correct or empty string,
and symbols A,B,C,D,E,F are always uppercase.
Examples:
For num = "AB" the output should be 1.
For num = "1077E" the output should be 2.
For num = "ABED1A33" the output should be 4.
For num = "123456789ABCDEF0" the output should be 6.
For num = "2020" the output should be 2.
""" *)

Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* is_prime_hex_digit recognizes hexadecimal digits with prime numeric value. *)
Definition is_prime_hex_digit (c : ascii) : bool :=
  match c with
  | "2"%char | "3"%char | "5"%char | "7"%char
  | "B"%char | "D"%char => true
  | _ => false
  end.

(* prime_hex_digit states that a character is one of the prime-valued hex digits. *)
Definition prime_hex_digit (c : ascii) : Prop :=
  is_prime_hex_digit c = true.

(* prime_hex_digits says the witness list contains exactly the prime hex digit values from s. *)
Definition prime_hex_digits (s : string) (digits : list ascii) : Prop :=
  (forall c, In c digits -> In c (list_ascii_of_string s) /\ prime_hex_digit c) /\
  (forall c, In c (list_ascii_of_string s) -> prime_hex_digit c -> In c digits).

(* problem_78_pre imposes no input constraints. *)
Definition problem_78_pre (s : string) : Prop := True.

(* problem_78_spec states the count through an explicit list of prime hex digits. *)
Definition problem_78_spec (s : string) (output : nat) : Prop :=
  exists digits,
    prime_hex_digits s digits /\
    output = length digits.
