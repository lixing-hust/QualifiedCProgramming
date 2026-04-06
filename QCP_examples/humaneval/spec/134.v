(* def check_if_last_char_is_a_letter(txt):
'''
Create a function that returns True if the last character
of a given string is an alphabetical character and is not
a part of a word, and False otherwise.
Note: "word" is a group of characters separated by space.

Examples:
check_if_last_char_is_a_letter("apple pie") ➞ False
check_if_last_char_is_a_letter("apple pi e") ➞ True
check_if_last_char_is_a_letter("apple pi e ") ➞ False
check_if_last_char_is_a_letter("") ➞ False
''' *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Import ListNotations.


(* 空格字符 *)
Definition space : ascii := Ascii.ascii_of_nat 32.

(* 判断是否为英文字母 (A-Z 或 a-z) *)
Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122).

(* 判定：s 是否以单个字母作为最后的 token（最后字符是字母，且前一字符要么不存在要么是空格） *)
Definition ends_with_single_letter_pred (s : string) : Prop :=
  let l := list_ascii_of_string s in
  exists pre c,
    l = pre ++ [c] /\
    is_alpha c /\
    (pre = [] \/ exists pre', pre = pre' ++ [space]).

(* 任意字符列表均可 *)
Definition problem_134_pre (s : string) : Prop := True.

(* 最终 Spec：输入 s，输出 b。当且仅当 ends_with_single_letter_pred s 成立时返回 true。 *)
Definition problem_134_spec (s : string) (b : bool) : Prop :=
  b = true <-> ends_with_single_letter_pred s.
