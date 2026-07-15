(* def anti_shuffle(s):
"""
Write a function that takes a string and returns an ordered version of it.
Ordered version of string, is a string where all words (separated by space)
are replaced by a new word where all the characters arranged in
ascending order based on ascii value.
Note: You should keep the order of words and blank spaces in the sentence.

For example:
anti_shuffle('Hi') returns 'Hi'
anti_shuffle('hello') returns 'ehllo'
anti_shuffle('Hello World!!!') returns 'Hello !!!Wdlor'
""" *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.

Import ListNotations.
Open Scope string_scope.

Definition no_space_string (s : string) : Prop :=
  Forall (fun c => c <> " "%char) (list_ascii_of_string s).

Definition split_by_spaces (s : string) (parts : list string) : Prop :=
  String.concat " " parts = s /\ Forall no_space_string parts.

Definition ascii_le (c1 c2 : ascii) : Prop :=
  nat_of_ascii c1 <= nat_of_ascii c2.

Definition sorted_string (s : string) : Prop :=
  StronglySorted ascii_le (list_ascii_of_string s).

Definition sorted_version (s s_sorted : string) : Prop :=
  Permutation (list_ascii_of_string s) (list_ascii_of_string s_sorted) /\
  sorted_string s_sorted.

Definition problem_86_pre (s : string) : Prop := True.

Definition problem_86_spec (s s_out : string) : Prop :=
  exists L L2 : list string,
    split_by_spaces s L /\
    Forall2 sorted_version L L2 /\
    s_out = String.concat " " L2.
