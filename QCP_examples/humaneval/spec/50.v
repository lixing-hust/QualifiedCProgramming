(* def encode_shift(s: str):
"""
returns encoded string by shifting every character by 5 in the alphabet.
"""
return "".join([chr(((ord(ch) + 5 - ord("a")) % 26) + ord("a")) for ch in s])


def decode_shift(s: str):
"""
takes as input string encoded with encode_shift function. Returns decoded string.
""" *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith. (* For nat arithmetic like mod *)
Import ListNotations.
Open Scope string_scope.

(* 定义单个字符的解密操作 *)
Definition decode_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  let a := nat_of_ascii "a"%char in
  ascii_of_nat (a + (n - a + 21) mod 26).

Definition is_lowercase_ascii (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a"%char <= n <= nat_of_ascii "z"%char)%nat.

Fixpoint all_lowercase_ascii (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String c rest => is_lowercase_ascii c /\ all_lowercase_ascii rest
  end.

(* Pre: `decode_shift` is specified for lowercase alphabetic strings. *)
Definition problem_50_pre (l' : string) : Prop := all_lowercase_ascii l'.

(* decode_shift 程序的规约 *)
Definition problem_50_spec (l' l : string) : Prop :=
  let list_l := list_ascii_of_string l in
  let list_l' := list_ascii_of_string l' in
  list_l = map decode_char list_l'.
