
(* def vowels_count(s):
"""Write a function vowels_count which takes a string representing
a word as input and returns the number of vowels in the string.
Vowels in this case are 'a', 'e', 'i', 'o', 'u'. Here, 'y' is also a
vowel, but only when it is at the end of the given word.

Example:
>>> vowels_count("abcde")
2
>>> vowels_count("ACEDY")
3
""" *)

Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Arith.Arith Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* is_vowel_char recognizes ordinary English vowels in either case. *)
Definition is_vowel_char (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

(* is_y recognizes y/Y for the terminal-vowel rule. *)
Definition is_y (c : ascii) : bool :=
  match c with
  | "y"%char | "Y"%char => true
  | _ => false
  end.

(* terminal_y_count contributes one when the final character is y or Y. *)
Definition terminal_y_count (chars : list ascii) : nat :=
  match rev chars with
  | c :: _ => if is_y c then 1 else 0
  | [] => 0
  end.

(* vowels_count_func counts ordinary vowels plus a terminal y/Y. *)
Definition vowels_count_func (s : string) : nat :=
  let chars := list_ascii_of_string s in
  length (filter is_vowel_char chars) + terminal_y_count chars.

(* vowels_count_impl is the public implementation-level expression. *)
Definition vowels_count_impl (s : string) : nat :=
  vowels_count_func s.

(* problem_64_pre imposes no input constraints. *)
Definition problem_64_pre (s : string) : Prop := True.

(* problem_64_spec states that output is the vowel count with terminal y/Y rule. *)
Definition problem_64_spec (s : string) (output : nat) : Prop :=
  output = vowels_count_impl s.
