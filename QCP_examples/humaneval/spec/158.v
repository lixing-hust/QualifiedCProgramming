(* def find_max(words):
"""Write a function that accepts a list of strings.
The list contains different words. Return the word with maximum number
of unique characters. If multiple strings have maximum number of unique
characters, return the one which comes first in lexicographical order.

find_max(["name", "of", "string"]) == "string"
find_max(["name", "enam", "game"]) == "enam"
find_max(["aaaaaaa", "bb" ,"cc"]) == ""aaaaaaa"
 *)
(* 导入必要的 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Structures.OrderedTypeEx.
Import ListNotations.

(* string_le is standard lexicographic order, including equality. *)
Definition string_le (s1 s2 : string) : Prop :=
  s1 = s2 \/ String_as_OT.lt s1 s2.

(* count_unique_chars counts distinct ASCII characters with the library nodup. *)
Definition count_unique_chars (s : string) : nat :=
  List.length (nodup Ascii.ascii_dec (list_ascii_of_string s)).

(* problem_158_pre requires a non-empty word list. *)
Definition problem_158_pre (words : list string) : Prop := words <> [].

(*
  find_max 函数的程序规约 (Spec)。
*)
(* problem_158_spec selects a word with maximal unique-character count and lexicographic tie-break. *)
Definition problem_158_spec (words : list string) (result : string) : Prop :=
  In result words /\
  forall w, In w words ->
    let c_res := count_unique_chars result in
    let c_w := count_unique_chars w in
    c_res > c_w \/ (c_res = c_w /\ string_le result w).
