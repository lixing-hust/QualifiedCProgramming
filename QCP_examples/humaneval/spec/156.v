(* def int_to_mini_roman(number):
"""
Given a positive integer, obtain its roman numeral equivalent as a string,
and return it in lowercase.
Restrictions: 1 <= num <= 1000

Examples:
>>> int_to_mini_roman(19) == 'xix'
>>> int_to_mini_roman(152) == 'clii'
>>> int_to_mini_roman(426) == 'cdxxvi'
""" *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith. (* <-- 添加这一行来导入算术库 *)
Import ListNotations.

(*
  一个辅助规约，用于定义单个数字（0-9）到其小写罗马数字字符（作为 list ascii）的映射。
  - roman_char:  i, v, x
*)
Definition roman_digit_spec (one ten five : ascii) (digit : nat) (res : list ascii) : Prop :=
  (digit = 0 /\ res = []) \/
  (digit = 1 /\ res = [one]) \/
  (digit = 2 /\ res = [one; one]) \/
  (digit = 3 /\ res = [one; one; one]) \/
  (digit = 4 /\ res = [one; five]) \/
  (digit = 5 /\ res = [five]) \/
  (digit = 6 /\ res = [five; one]) \/
  (digit = 7 /\ res = [five; one; one]) \/
  (digit = 8 /\ res = [five; one; one; one]) \/
  (digit = 9 /\ res = [one; ten]).

(* 输入限制：1 <= number <= 1000 *)
Definition problem_156_pre (number : nat) : Prop := 1 <= number /\ number <= 1000.

(*
  int_to_mini_roman 程序的程序规约
*)
Definition problem_156_spec (number : nat) (result : string) : Prop :=
  1 <= number <= 1000 /\
  (exists m c x i rm rc rx ri,
    number = 1000 * m + 100 * c + 10 * x + i /\
    m = number / 1000 /\
    c = (number / 100) mod 10 /\
    x = (number / 10) mod 10 /\
    i = number mod 10 /\
    ( (m = 1 /\ rm = ["m"%char]) \/ (m = 0 /\ rm = []) ) /\
    roman_digit_spec "c"%char "m"%char "d"%char c rc /\
    roman_digit_spec "x"%char "c"%char "l"%char x rx /\
    roman_digit_spec "i"%char "x"%char "v"%char i ri /\
    result = string_of_list_ascii (rm ++ rc ++ rx ++ ri)).