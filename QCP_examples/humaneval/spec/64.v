
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

Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Arith.Arith Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* regular_vowel_64 recognizes ordinary English vowels in either case. *)
Definition regular_vowel_64 (c : ascii) : Prop :=
  c = "a"%char \/ c = "e"%char \/ c = "i"%char \/ c = "o"%char \/
  c = "u"%char \/ c = "A"%char \/ c = "E"%char \/ c = "I"%char \/
  c = "O"%char \/ c = "U"%char.

(* counted_vowel_position_64 states that index i contributes one to the answer. *)
Definition counted_vowel_position_64 (chars : list ascii) (i : nat) : Prop :=
  exists c,
    nth_error chars i = Some c /\
    (regular_vowel_64 c \/
     ((c = "y"%char \/ c = "Y"%char) /\ S i = List.length chars)).

(* selected_vowel_positions_64 is exactly the finite set of counted positions. *)
Definition selected_vowel_positions_64 (chars : list ascii) (positions : list nat) : Prop :=
  NoDup positions /\
  forall i,
    In i positions <-> counted_vowel_position_64 chars i.

(* problem_64_pre imposes no input constraints. *)
Definition problem_64_pre (s : string) : Prop := True.

(* problem_64_spec states that output is the number of positions counted as vowels. *)
Definition problem_64_spec (s : string) (output : nat) : Prop :=
  exists positions,
    selected_vowel_positions_64 (list_ascii_of_string s) positions /\
    output = List.length positions.
