(*Input to this function is a string containing multiple groups of nested parentheses. Your goal is to
separate those group into separate strings and return the list of those.
Separate groups are balanced (each open brace is properly closed) and not nested within each other
Ignore any spaces in the input string.
>>> separate_paren_groups('( ) (( )) (( )( ))')
['()', '(())', '(()())'] *)

(* 引入所需的基础库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

(* 定义 '(' 和 ')' 的 ASCII 表示 *)
Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

(*
  规约 1: balanced_chars(cs)
  使用前缀计数关系刻画括号平衡，避免在规格文件中写本地递归定义。
*)
Definition balanced_chars (cs : list ascii) : Prop :=
  count_occ ascii_dec cs lparen = count_occ ascii_dec cs rparen /\
  forall prefix suffix,
    cs = (prefix ++ suffix)%list ->
    count_occ ascii_dec prefix rparen <= count_occ ascii_dec prefix lparen.

Definition IsBalanced (s : string) : Prop :=
  balanced_chars (list_ascii_of_string s).

(*
  辅助函数: 移除列表中的空格。这里复用标准库 filter，而非本地递归。
*)
Definition nonspace_char (c : ascii) : bool :=
  if ascii_dec c space then false else true.

Definition chars_without_spaces (s : string) : list ascii :=
  filter nonspace_char (list_ascii_of_string s).

Definition remove_spaces (s : string) : string :=
  string_of_list_ascii (chars_without_spaces s).

(*
  辅助断言: 检查一个字符是否为括号或空格
  直接使用等式，其类型为 Prop
*)
Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

(*
  辅助断言: 字符是否为括号。
*)
Definition is_paren (c : ascii) : Prop :=
  c = lparen \/ c = rparen.

(*
  辅助断言: 检查字符串中的所有字符是否满足属性 P。
  这里复用标准库 List.Forall。
*)
Definition ForallChars (P : ascii -> Prop) (s : string) : Prop :=
  Forall P (list_ascii_of_string s).

(*
  一个 primitive group 是一个非空、平衡、只含括号的最外层括号组；
  “没有非空真前缀已经平衡”排除了 "()()" 这类多个组粘在一起的情况。
*)
Definition primitive_group_chars (cs : list ascii) : Prop :=
  cs <> [] /\
  Forall is_paren cs /\
  balanced_chars cs /\
  forall prefix suffix,
    cs = (prefix ++ suffix)%list ->
    prefix <> [] ->
    suffix <> [] ->
    ~ balanced_chars prefix.

Definition primitive_group (s : string) : Prop :=
  primitive_group_chars (list_ascii_of_string s).

Definition output_chars (output : list string) : list ascii :=
  List.concat (map list_ascii_of_string output).

(*
  前提条件: separate_paren_groups_pre
  1. 输入列表中的所有字符都必须是括号或空格。
  2. 移除空格后的输入列表必须是平衡的。
*)
Definition problem_1_pre (input : string) : Prop :=
  (ForallChars is_paren_or_space input) /\
  (balanced_chars (chars_without_spaces input)).
(*
  最终的程序规约: separate_paren_groups_spec(input, output)
*)
Definition problem_1_spec (input : string) (output : list string) : Prop :=
  Forall primitive_group output /\
  output_chars output = chars_without_spaces input.
