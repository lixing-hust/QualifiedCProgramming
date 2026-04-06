(* def is_nested(string):
'''
Create a function that takes a string as input which contains only square brackets.
The function should return True if and only if there is a valid subsequence of brackets
where at least one bracket in the subsequence is nested.

is_nested('[[]]') ➞ True
is_nested('[]]]]]]][[[[[]') ➞ False
is_nested('[][]') ➞ False
is_nested('[]') ➞ False
is_nested('[[][]]') ➞ True
is_nested('[[]][[') ➞ True
''' *)
(* 引入 Coq 标准库中的字符串、列表和 Ascii 字符集 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

(* 定义开方括号和闭方括号的 Ascii 字符表示 *)
Definition open_bracket : ascii := "["%char.
Definition close_bracket : ascii := "]"%char.

Fixpoint contains_subseq (s : list ascii) (target : list ascii) : bool :=
  match target with
  | [] => true
  | t :: ts =>
      match s with
      | [] => false
      | c :: cs =>
          if Ascii.ascii_dec c t then
            contains_subseq cs ts
          else
            contains_subseq cs target
      end
  end.

Definition is_nested (s : string) : bool :=
  contains_subseq (list_ascii_of_string s) [open_bracket; open_bracket; close_bracket; close_bracket].

(* 仅允许 '[' 或 ']' 字符 *)
Definition problem_132_pre (s : string) : Prop :=
  Forall (fun c => c = "["%char \/ c = "]"%char) (list_ascii_of_string s).

(*
  程序规约：is_nested_spec s_in output
  它将输入字符串 s_in 与布尔输出 output 关联起来。
  
  规约内容：
  输出为 `true` 当且仅当输入字符串包含 "[[]]" 作为子序列。
*)
Definition problem_132_spec (s : string) (output : bool) : Prop :=
  output = is_nested s.