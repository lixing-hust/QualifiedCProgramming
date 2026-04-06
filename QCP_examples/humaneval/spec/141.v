(* def file_name_check(file_name):
"""Create a function which takes a string representing a file's name, and returns
'Yes' if the the file's name is valid, and returns 'No' otherwise.
A file's name is considered to be valid if and only if all the following conditions
are met:
- There should not be more than three digits ('0'-'9') in the file's name.
- The file's name contains exactly one dot '.'
- The substring before the dot should not be empty, and it starts with a letter from
the latin alphapet ('a'-'z' and 'A'-'Z').
- The substring after the dot should be one of these: ['txt', 'exe', 'dll']
Examples:
file_name_check("example.txt") # => 'Yes'
file_name_check("1example.dll") # => 'No' (the name should start with a latin alphapet letter)
""" *)
(* 引入必要的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Import Nat.


(*
  辅助定义（返回 bool）: 检查一个字符是否为数字。
  我们使用 <=? 这个符号，它代表返回 bool 的比较运算。
*)
Definition is_digit_bool (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (nat_of_ascii "0"%char <=? n) && (n <=? nat_of_ascii "9"%char).

(*
  辅助定义（返回 Prop）: 检查一个字符是否为拉丁字母。
*)
Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a"%char <= n /\ n <= nat_of_ascii "z"%char) \/
  (nat_of_ascii "A"%char <= n /\ n <= nat_of_ascii "Z"%char).

(* 输入文件名为任意字符列表，无额外约束 *)
Definition problem_141_pre (file_name : string) : Prop := True.

(* file_name_check 函数的程序规约 *)
Definition problem_141_spec (file_name_str : string) (result : string) : Prop :=
  let file_name := list_ascii_of_string file_name_str in
  (* 定义一个命题 `is_valid` 来描述一个文件名是否有效 *)
  let is_valid :=
    (* 条件1: 文件名中数字的数量不能超过三个 *)
    (length (filter is_digit_bool file_name) <= 3) /\

    (* 将文件名按唯一的'.'分割成前缀和后缀 *)
    (exists prefix suffix,
      file_name = prefix ++ "."%char :: suffix /\
      ~ In "."%char (prefix ++ suffix) /\

      (* 条件2: '.'之前的部分不能为空，且必须以字母开头 *)
      (exists first_char rest_prefix,
        prefix = first_char :: rest_prefix /\ is_alpha first_char) /\

      (* 条件3: '.'之后的部分必须是 "txt", "exe", 或 "dll" 之一 *)
      (suffix = ("t"::"x"::"t"::[])%char \/
       suffix = ("e"::"x"::"e"::[])%char \/
       suffix = ("d"::"l"::"l"::[])%char))
  in
  (* 规约的核心：如果文件名有效，则结果为 "Yes"，否则为 "No" *)
  (is_valid /\ result = "Yes") \/
  (~is_valid /\ result = "No").