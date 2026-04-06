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

(*
  辅助关系: `skip_leading_spaces input remaining`
  这个关系为真，当且仅当 `remaining` 是 `input` 列表移除所有前导空格后的结果。
*)
Inductive skip_leading_spaces: list ascii -> list ascii -> Prop :=
  | sls_nil:
      skip_leading_spaces [] []
  | sls_non_space (c : ascii) (l : list ascii):
      c <> space ->
      skip_leading_spaces (c :: l) (c :: l)
  | sls_space (l l' : list ascii):
      skip_leading_spaces l l' ->
      skip_leading_spaces (space :: l) l'.

(*
  核心关系: `fix_spaces_relation input output`
  该关系通过一组构造规则，定义了输入列表和输出列表之间的合法转换。
  每一条规则都对应程序逻辑中的一个分支。
*)
Inductive fix_spaces_relation : list ascii -> list ascii -> Prop :=
  (* 规则1: 输入为空列表，则输出也必须为空列表。 *)
  | fsr_nil:
      fix_spaces_relation [] []

  (* 规则2: 输入以非空格字符 `c` 开头。
     输出也以 `c` 开头，然后对其余列表应用相同的关系。 *)
  | fsr_non_space (c : ascii) (i' o' : list ascii):
      c <> space ->
      fix_spaces_relation i' o' ->
      fix_spaces_relation (c :: i') (c :: o')

  (* 规则3: 输入以单个空格开头 (即下一个字符不是空格，或已到列表末尾)。
     该空格被替换为下划线。 *)
  | fsr_single_space (i' o' : list ascii):
      (match i' with
       | [] => True
       | c :: _ => c <> space
       end) ->
      fix_spaces_relation i' o' ->
      fix_spaces_relation (space :: i') (underscore :: o')

  (* 规则4: 输入以至少两个空格开头。
     输出一个破折号，并跳过所有连续的前导空格，然后对其余列表应用关系。 *)
  | fsr_multi_space (i_after_2_spaces i_rem o' : list ascii):
      (* i_after_2_spaces 是紧跟在头两个空格后的子列表 *)
      (* i_rem 是 i_after_2_spaces 跳过其所有前导空格后的结果 *)
      skip_leading_spaces i_after_2_spaces i_rem ->
      fix_spaces_relation i_rem o' ->
      fix_spaces_relation (space :: space :: i_after_2_spaces) (dash :: o').

(* 输入文本任意 *)
Definition problem_140_pre (s : string) : Prop := True.
(*
  程序规约 (Spec)
  它断言输入列表和输出列表必须满足 `fix_spaces_relation` 所定义的关系。
*)
Definition problem_140_spec (s_in s_out : string) : Prop :=
  fix_spaces_relation (list_ascii_of_string s_in) (list_ascii_of_string s_out).

