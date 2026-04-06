(* def remove_vowels(text):
"""
remove_vowels is a function that takes string and returns string without vowels.
>>> remove_vowels('')
''
>>> remove_vowels("abcdef\nghijklm")
'bcdf\nghjklm'
>>> remove_vowels('abcdef')
'bcdf'
>>> remove_vowels('aaaaa')
''
>>> remove_vowels('aaBAA')
'B'
>>> remove_vowels('zbcd')
'zbcd'
""" *)
(* 导入 Coq 标准库中的 ASCII 字符和列表模块 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(*
 * 描述: 判断一个 ASCII 字符是否是元音字母（包括大小写）。
 * @param c: ascii - 输入的字符。
 * @return: bool - 如果是元音则返回 true，否则返回 false。
 * )
*)
Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Fixpoint filter_string (f : ascii -> bool) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if f c then String c (filter_string f s') else filter_string f s'
  end.

(*
 * 描述: 这是 remove_vowels 函数的程序规约 (Specification)，完全基于属性定义。
 * 它将输出列表 (output) 定义为输入列表 (input) 中所有非元音字母的集合。
 *
 * @param input: string - 输入的原始字符列表。
 * @param output: string - 函数的输出字符列表。
 * @return: Prop - 一个表示输入和输出之间关系的命题。
 *)
(* Pre: no special constraints for `remove_vowels` *)
Definition problem_51_pre (input : string) : Prop := True.

Definition problem_51_spec (input : string) (output : string) : Prop :=
  output = filter_string (fun c => negb (is_vowel c)) input.
