(* def encrypt(s):
"""Create a function encrypt that takes a string as an argument and
returns a string encrypted with the alphabet being rotated.
The alphabet should be rotated in a manner such that the letters
shift down by two multiplied to two places.
For example:
encrypt('hi') returns 'lm'
encrypt('asdfghjkl') returns 'ewhjklnop'
encrypt('gf') returns 'kj'
encrypt('et') returns 'ix'
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Arith.
Import ListNotations.
Local Open Scope char_scope.

(* One output character is four positions after the input character,
   wrapping around inside the lowercase alphabet. *)
Definition shifted_by_four (c_in c_out : ascii) : Prop :=
  let a := nat_of_ascii "a" in
  nat_of_ascii c_out = a + (nat_of_ascii c_in - a + 4) mod 26.

(* is_lowercase_ascii recognizes lowercase ASCII letters. *)
Definition is_lowercase_ascii (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a"%char <= n <= nat_of_ascii "z"%char)%nat.

(* all_lowercase_ascii requires every character in the string to be lowercase. *)
Definition all_lowercase_ascii (s : string) : Prop :=
  Forall is_lowercase_ascii (list_ascii_of_string s).

(* problem_89_pre restricts the input to lowercase ASCII letters. *)
Definition problem_89_pre (s : string) : Prop := all_lowercase_ascii s.

(* The input and output strings are pointwise related by the rotation. *)
Definition problem_89_spec (s : string) (output : string) : Prop :=
  Forall2 shifted_by_four
    (list_ascii_of_string s)
    (list_ascii_of_string output).
