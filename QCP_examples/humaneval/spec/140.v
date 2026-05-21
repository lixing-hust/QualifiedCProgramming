(* def fix_spaces(text):
Given a string text, replace all spaces in it with underscores,
and if a string has more than 2 consecutive spaces,
then replace all consecutive spaces with -

fix_spaces("Example") == "Example"
fix_spaces("Example 1") == "Example_1"
fix_spaces(" Example 2") == "_Example_2"
fix_spaces(" Example 3") == "_Example-3" *)
(* 导入列表和ASCII字符所需的基础库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(* 为清晰起见，定义字符常量 *)
Definition space : ascii := " ".
Definition underscore : ascii := "_".
Definition dash : ascii := "-".

Definition flush_spaces (n : nat) : list ascii :=
  match n with
  | 0 => []
  | 1 => [underscore]
  | 2 => [underscore; underscore]
  | _ => [dash]
  end.

(*
  核心函数: `fix_spaces_func input`
  pending 记录当前尚未输出的连续空格段长度。
  遇到非空格时先输出 pending 空格段，再输出当前字符。
*)
Fixpoint fix_spaces_scan (l : list ascii) (pending : nat) : list ascii :=
  match l with
  | [] => flush_spaces pending
  | c :: tl =>
      if Ascii.ascii_dec c space then
        fix_spaces_scan tl (S pending)
      else
        flush_spaces pending ++ c :: fix_spaces_scan tl 0
  end.

Definition fix_spaces (s : string) : string :=
  let l := list_ascii_of_string s in
  string_of_list_ascii (fix_spaces_scan l 0).

(* 输入文本任意 *)
Definition problem_140_pre (s : string) : Prop := True.
(*
  程序规约 (Spec)
  它断言输出列表等于 `fix_spaces` 函数对输入列表的应用结果。
*)
Definition problem_140_spec (s : string) (output : string) : Prop :=
  output = fix_spaces s.
