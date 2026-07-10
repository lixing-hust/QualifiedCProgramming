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
(* 导入Coq中处理字符串和列表所需的基础库 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.


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
  match n with
  | O => "0"
  | _ =>
      string_of_list_ascii
        (map (fun p => bit_char ((n / Nat.pow 2 p) mod 2)) (rev (seq 0 (S (msb_pos n)))))
  end.

(* decimal_to_binary_impl wraps the binary representation with db delimiters. *)
Definition decimal_to_binary_impl (decimal : nat) : string :=
  "db" ++ nat_to_binary_string decimal ++ "db".
  
(* problem_79_pre imposes no input constraints. *)
Definition problem_79_pre (decimal : nat) : Prop := True.

(* problem_79_spec states that output is the delimited binary representation. *)
Definition problem_79_spec (decimal : nat) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.
