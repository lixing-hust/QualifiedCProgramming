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

(* word_to_num maps valid numeral words to their numeric value. *)
Definition word_to_num (s : string) : option nat :=
  if string_dec s "zero" then Some 0
  else if string_dec s "one" then Some 1
  else if string_dec s "two" then Some 2
  else if string_dec s "three" then Some 3
  else if string_dec s "four" then Some 4
  else if string_dec s "five" then Some 5
  else if string_dec s "six" then Some 6
  else if string_dec s "seven" then Some 7
  else if string_dec s "eight" then Some 8
  else if string_dec s "nine" then Some 9
  else None.

(* is_valid_word states that a string is one of the ten numeral words. *)
Definition is_valid_word (s : string) : Prop :=
  exists n, word_to_num s = Some n.

(*
  定义一个谓词，用于判断一个 string 列表是否已排序。
*)
Definition IsSorted (l : list string) : Prop :=
  forall i j, (i < j)%nat -> j < length l ->
    forall s_i s_j n_i n_j,
      nth i l "" = s_i ->
      nth j l "" = s_j ->
      word_to_num s_i = Some n_i ->
      word_to_num s_j = Some n_j ->
      (n_i <= n_j)%nat.

(* SpaceDelimited relates a string to the words joined by single spaces. *)
Definition SpaceDelimited (s : string) (words : list string) : Prop :=
  String.concat " " words = s.

(* problem_19_pre requires the input to be a space-delimited list of numeral words. *)
Definition problem_19_pre (input : string) : Prop :=
  exists input_list,
    SpaceDelimited input input_list /\
    Forall is_valid_word input_list.

(* problem_19_spec characterizes a sorted permutation of the numeral words. *)
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
