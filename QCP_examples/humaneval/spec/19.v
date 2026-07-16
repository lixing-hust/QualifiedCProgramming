(* """ Input is a space-delimited string of numberals from 'zero' to 'nine'.
Valid choices are 'zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight' and 'nine'.
Return the string with numbers sorted from smallest to largest
>>> sort_numbers('three one five')
'one three five'
""" *)

(* Spec(input, output) :=

∃ input_list, output_list,
    String.concat " " input_list = input ∧
    String.concat " " output_list = output ∧
    IsPermutation(input_list, output_list) ∧
    IsSorted(output_list) *)


(* 导入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Permutation.

(* 导入列表表示法 *)
Import ListNotations.
Open Scope string_scope.

(*
  定义一个从单词 (string) 到数字 (nat) 的关系。
*)
Inductive WordToNum : string -> nat -> Prop :=
  | wtn_zero  : WordToNum "zero" 0
  | wtn_one   : WordToNum "one" 1
  | wtn_two   : WordToNum "two" 2
  | wtn_three : WordToNum "three" 3
  | wtn_four  : WordToNum "four" 4
  | wtn_five  : WordToNum "five" 5
  | wtn_six   : WordToNum "six" 6
  | wtn_seven : WordToNum "seven" 7
  | wtn_eight : WordToNum "eight" 8
  | wtn_nine  : WordToNum "nine" 9.

(* 定义一个谓词，用于判断一个 string 是否是有效的数字单词 *)
Definition is_valid_word (s : string) : Prop :=
  exists n, WordToNum s n.

(*
  定义一个谓词，用于判断一个 string 列表是否已排序。
*)
Definition IsSorted (l : list string) : Prop :=
  forall i j, (i < j)%nat -> j < length l ->
    forall s_i s_j n_i n_j,
      nth i l "" = s_i ->
      nth j l "" = s_j ->
      WordToNum s_i n_i ->
      WordToNum s_j n_j ->
      (n_i <= n_j)%nat.

Definition SpaceDelimited (s : string) (words : list string) : Prop :=
  String.concat " " words = s.

Definition problem_19_pre (input : string) : Prop :=
  exists input_list,
    SpaceDelimited input input_list /\
    Forall is_valid_word input_list.

Definition problem_19_spec (input output : string) : Prop :=
    exists input_list output_list,
    SpaceDelimited input input_list /\
    SpaceDelimited output output_list /\
    Forall is_valid_word input_list /\
    Forall is_valid_word output_list /\

    (*  输出列表是输入列表的一个排列 *)
    Permutation input_list output_list /\

    (*  输出列表是排好序的 *)
    IsSorted output_list.
