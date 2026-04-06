(* Given an array of integers nums, find the minimum sum of any non-empty sub-array
of nums.
Example
minSubArraySum([2, 3, 4, 1, 2, 4]) == 1
minSubArraySum([-1, -2, -3]) == -6 *)

(* 引入所需的库 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.



Open Scope Z_scope.
(* 定义一个函数来计算整数列表的和 *)
Definition list_sum (l : list Z) : Z :=
  fold_left Z.add l 0.

(* nums 非空 *)
Definition problem_114_pre (nums : list Z) : Prop := nums <> [].

(* 定义一个规约来描述最小子数组和的属性 *)
Definition problem_114_spec (nums : list Z) (min_sum : Z) : Prop :=
  (* 1. 存在性 (Existence): 必须存在一个非空子数组，其和等于 min_sum *)
  (exists sub_array,
    sub_array <> [] /\
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) /\
    list_sum sub_array = min_sum)
  /\
  (* 2. 最小性 (Minimality): 对于所有非空的子数组，它们的和都必须大于或等于 min_sum *)
  (forall sub_array,
    sub_array <> [] ->
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) ->
    min_sum <= list_sum sub_array).