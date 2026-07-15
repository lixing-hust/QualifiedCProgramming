(* def decimal_to_binary(decimal):
"""You will be given a number in decimal form and your task is to convert it to
binary format. The function should return a string, with each character representing a binary
number. Each character in the string will be '0' or '1'.

There will be an extra couple of characters 'db' at the beginning and at the end of the string.
The extra characters are there to help with the format.

Examples:
decimal_to_binary(15) # returns "db1111db"
decimal_to_binary(32) # returns "db100000db"
""" *)
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

(* binary_digits uses the GmpNumber low-digit-first positional encoding. *)
Definition binary_digits (decimal : nat) (bits : list Z) : Prop :=
  list_within_bound 2 bits /\
  list_to_Z 2 bits = Z.of_nat decimal /\
  ((decimal = O /\ bits = [0]) \/
   (decimal <> O /\ bits <> [] /\ last bits 0 = 1)).

(* The visible binary string prints the most significant bit first. *)
Definition binary_string_from_digits (bits : list Z) : string :=
  string_of_list_ascii (map bit_char (rev bits)).
  
(* problem_79_pre imposes no input constraints. *)
Definition problem_79_pre (decimal : nat) : Prop := True.

(* problem_79_spec relates output to some canonical binary digit list. *)
Definition problem_79_spec (decimal : nat) (output : string) : Prop :=
  exists bits,
    binary_digits decimal bits /\
    output = "db" ++ binary_string_from_digits bits ++ "db".
