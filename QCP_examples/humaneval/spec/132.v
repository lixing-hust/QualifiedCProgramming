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
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

(* 定义开方括号和闭方括号的 Ascii 字符表示 *)
Definition open_bracket : ascii := "["%char.

(* close_bracket is the ASCII closing square bracket. *)
Definition close_bracket : ascii := "]"%char.

Record bracket_scan_state : Type := {
  scan_current : Z;
  scan_maximum : Z;
  scan_nested : bool
}.

(* One step of the canonical reset-on-unmatched-close scan. *)
Definition bracket_scan_step
    (state : bracket_scan_state) (c : ascii) : bracket_scan_state :=
  let current :=
    if ascii_dec c open_bracket
    then scan_current state + 1
    else Z.max 0 (scan_current state - 1) in
  let maximum := Z.max (scan_maximum state) current in
  {| scan_current := current;
     scan_maximum := maximum;
     scan_nested :=
       orb (scan_nested state)
         (Z.leb (current + 2) maximum) |}.

Definition canonical_bracket_scan (s : string) : bracket_scan_state :=
  fold_left bracket_scan_step (list_ascii_of_string s)
    {| scan_current := 0; scan_maximum := 0; scan_nested := false |}.

(*
  Once [scan_nested] becomes true it remains true.  Thus this is equivalent
  to the C program's early return when [count <= maxcount - 2].
*)
Definition nested_depth_drop (s : string) : Prop :=
  scan_nested (canonical_bracket_scan s) = true.

(* problem_132_pre only allows square bracket characters. *)
Definition problem_132_pre (s : string) : Prop :=
  Forall (fun c => c = "["%char \/ c = "]"%char) (list_ascii_of_string s).

(*
  程序规约：is_nested_spec s_in output
  它将输入字符串 s_in 与布尔输出 output 关联起来。
  
  规约内容：
  输出为 `true` 当且仅当扫描深度从某个历史高点下降至少两层。
*)
(* problem_132_spec relates the boolean result to the canonical scan. *)
Definition problem_132_spec (s : string) (output : bool) : Prop :=
  output = true <-> nested_depth_drop s.
