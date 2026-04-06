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

(*
  谓词：Subsequence s1 s2
  表示列表 s1 是列表 s2 的一个子序列。
*)
Inductive Subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, Subsequence [] l
  | sub_cons_hd : forall x l1 l2, Subsequence l1 l2 -> Subsequence (x :: l1) (x :: l2)
  | sub_cons_tl : forall x l1 l2, Subsequence l1 l2 -> Subsequence l1 (x :: l2).

(*
  谓词：WellFormed s
  表示 s 是一个格式良好的方括号序列。
  - wf_nil: 空列表是格式良好的。
  - wf_nest: 如果 s 是格式良好的，那么 "[s]" 也是格式良好的。
  - wf_concat: 如果 s1 和 s2 都是格式良好的，那么它们的拼接 s1s2 也是格式良好的。
*)
Inductive WellFormed : list ascii -> Prop :=
  | wf_nil : WellFormed []
  | wf_nest : forall s, WellFormed s -> WellFormed (open_bracket :: s ++ [close_bracket])
  | wf_concat : forall s1 s2, WellFormed s1 -> WellFormed s2 -> WellFormed (s1 ++ s2).

(*
  谓词：NonNestedWellFormed s
  表示 s 是一个格式良好但没有任何嵌套的序列。
  这样的序列只能由空序列或多个 "[]" 拼接而成。
  - nnwf_nil: 空列表是无嵌套的。
  - nnwf_concat: 如果 s 是无嵌套的，那么 "[]" 与 s 的拼接也是无嵌套的。
*)
Inductive NonNestedWellFormed : list ascii -> Prop :=
  | nnwf_nil : NonNestedWellFormed []
  | nnwf_concat : forall s, NonNestedWellFormed s -> NonNestedWellFormed ([open_bracket; close_bracket] ++ s).

(* 仅允许 '[' 或 ']' 字符 *)
Definition problem_132_pre (s_in : list ascii) : Prop :=
  Forall (fun c => c = "["%char \/ c = "]"%char) s_in.

(*
  程序规约：is_nested_spec s_in output
  它将输入字符串 s_in 与布尔输出 output 关联起来。
  
  规约内容：
  输出为 `true` 当且仅当 (iff) 存在一个输入字符串的子序列 `s`，
  它是一个格式良好的方括号序列 (`WellFormed s`)，
  并且它不仅仅是由 "[]" 拼接而成的 (`~ NonNestedWellFormed s`)，即它必须包含嵌套。
*)
Definition problem_132_spec (s_in : list ascii) (output : bool) : Prop :=
  let s_list := s_in in
  (output = true <->
    (exists s,
      Subsequence s s_list /\
      WellFormed s /\
      ~ NonNestedWellFormed s)
  ).