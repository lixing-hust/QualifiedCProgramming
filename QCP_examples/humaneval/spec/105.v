(* Given an array of integers, sort the integers that are between 1 and 9 inclusive,
reverse the resulting array, and then replace each digit by its corresponding name from
"One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine".

For example:
arr = [2, 1, 1, 4, 5, 8, 2, 3]
-> sort arr -> [1, 1, 2, 2, 3, 4, 5, 8]
-> reverse arr -> [8, 5, 4, 3, 2, 2, 1, 1]
return ["Eight", "Five", "Four", "Three", "Two", "Two", "One", "One"]

If the array is empty, return an empty array:
arr = []
return []

If the array has any strange number ignore it:
arr = [1, -1 , 55]
-> sort arr -> [-1, 1, 55]
-> reverse arr -> [55, 1, -1]
return = ['One'] *)

(* 引入所需的Coq标准库 *)
Require Import Coq.Lists.List.      (* List 操作, 包括 Permutation *)
Require Import Coq.Strings.String.  (* String 类型 *)
Require Import Coq.ZArith.ZArith.    (* Z整数类型及其操作 *)
Require Import Coq.Sorting.Sorted.     (* 引入 Sorted 属性的定义 *)
Require Import Permutation.
Import ListNotations. (* 启用列表的 [a; b; c] 写法 *)
Open Scope Z_scope.



(*
  辅助函数 (1):
  定义一个布尔函数，用于检查一个整数 `z` 是否在 1 到 9 之间（包含边界）。
*)
Definition is_target_digit (z : Z) : bool :=
  (1 <=? z) && (z <=? 9).

(*
  辅助函数 (2):
  将一个 1 到 9 的整数转换为其对应的英文单词字符串。
*)
Definition digit_to_word (z : Z) : string :=
  match z with
  | 1 => "One"%string
  | 2 => "Two"%string
  | 3 => "Three"%string
  | 4 => "Four"%string
  | 5 => "Five"%string
  | 6 => "Six"%string
  | 7 => "Seven"%string
  | 8 => "Eight"%string
  | 9 => "Nine"%string
  | _ => ""%string
  end.
(* 输入可以包含任意整数 *)

Definition problem_105_pre (l_in : list Z) : Prop := True.

(*
  程序规约 (Program Specification):
  这是一个 Prop (命题)，它表达了输入列表 l_in 和输出列表 l_out 之间的关系。
  这次我们使用声明式的方式来定义排序。
*)
Definition problem_105_spec (l_in : list Z) (l_out : list string) : Prop :=
  (* 步骤 1: 筛选出 l_in 中所有 1 到 9 之间的整数 *)
  let l_filtered := filter is_target_digit l_in in

  (*
    步骤 2: 声明存在一个中间列表 `l_sorted`，它满足排序的属性。
    这是一种更符合Coq风格的规约写法。
  *)
  exists (l_sorted : list Z),
    (* 属性a: l_sorted 是 l_filtered 的一个排列 *)
    (Permutation l_filtered l_sorted /\
    (* 属性b: l_sorted 是根据小于等于关系升序排列的 *)
     Sorted Z.le l_sorted) /\
    (* 步骤 3 & 4: 后续步骤与之前相同，基于这个满足属性的 l_sorted 进行 *)
    let l_reversed := rev l_sorted in
    l_out = map digit_to_word l_reversed.