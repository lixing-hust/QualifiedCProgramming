(* def sorted_list_sum(lst):
"""Write a function that accepts a list of strings as a parameter,
deletes the strings that have odd lengths from it,
and returns the resulted list with a sorted order,
The list is always a list of strings and never an array of numbers,
and it may contain duplicates.
The order of the list should be ascending by length of each word, and you
should return the list sorted by that rule.
If two words have the same length, sort the list alphabetically.
The function should return a list of strings in sorted order.
You may assume that all words will have the same length.
For example:
assert list_sort(["aa", "a", "aaa"]) => ["aa"]
assert list_sort(["ab", "a", "aaa", "cd"]) => ["ab", "cd"]
""" *)

Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation Coq.Sorting.Sorted Coq.Structures.OrderedTypeEx.
Import ListNotations.


Definition lex_le (s1 s2 : string) : Prop :=
  String_as_OT.lt s1 s2 \/ s1 = s2.

Definition string_le (s1 s2 : string) : Prop :=
  String.length s1 < String.length s2 \/
  String.length s1 = String.length s2 /\ lex_le s1 s2.

Definition has_even_length (s : string) : bool := Nat.even (length s).

(* 任意字符串列表输入均可 *)
Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  Permutation output (filter has_even_length input) /\
  StronglySorted string_le output.
