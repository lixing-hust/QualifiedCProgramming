(* def encrypt(s):
"""Create a function encrypt that takes a string as an argument and
returns a string encrypted with the alphabet being rotated.
The alphabet should be rotated in a manner such that the letters
shift down by two multiplied to two places.
For example:
encrypt('hi') returns 'lm'
encrypt('asdfghjkl') returns 'ewhjklnop'
encrypt('gf') returns 'kj'
encrypt('et') returns 'ix'
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope char_scope.

(*
  char_relation 定义了单个输入字符 c_in 和输出字符 c_out 之间的关系。
  这遵循字母表向下移动 4 (2*2) 位的规则。
*)
Definition char_relation (c_in c_out : ascii) : Prop :=
  match c_in with
  | "a" => c_out = "e" | "b" => c_out = "f" | "c" => c_out = "g" | "d" => c_out = "h"
  | "e" => c_out = "i" | "f" => c_out = "j" | "g" => c_out = "k" | "h" => c_out = "l"
  | "i" => c_out = "m" | "j" => c_out = "n" | "k" => c_out = "o" | "l" => c_out = "p"
  | "m" => c_out = "q" | "n" => c_out = "r" | "o" => c_out = "s" | "p" => c_out = "t"
  | "q" => c_out = "u" | "r" => c_out = "v" | "s" => c_out = "w" | "t" => c_out = "x"
  | "u" => c_out = "y" | "v" => c_out = "z" | "w" => c_out = "a" | "x" => c_out = "b"
  | "y" => c_out = "c" | "z" => c_out = "d"
  (* 对于非小写字母的任何其他字符，它保持不变 *)
  | _ => c_out = c_in
  end.

Definition problem_89_pre (s : string) : Prop := True.

(*
  encrypt_spec (程序规约)
  它规定：
  1. 输入列表 s 和输出列表 output 的长度必须相等.
  2. 对于两个列表中每个位置上对应的字符 (c_in, c_out)，
     它们必须满足 char_relation 定义的关系。
*)
Definition problem_89_spec (s : string) (output : string) : Prop :=
  String.length s = String.length output /\
  forall i, i < String.length s ->
    match String.get i s, String.get i output with
    | Some c_in, Some c_out => char_relation c_in c_out
    | _, _ => False
    end.