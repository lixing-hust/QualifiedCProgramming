(*Given an array arr of integers and a positive integer k, return a sorted list
of length k with the maximum k numbers in arr.

Example 1:

Input: arr = [-3, -4, 5], k = 3
Output: [-4, -3, 5]

Example 2:

Input: arr = [4, -4, 4], k = 2
Output: [4, 4]

Example 3:

Input: arr = [-3, 2, 1, 2, -1, -2, 1], k = 1
Output: [2]

Note:
1. The length of the array will be in the range of [1, 1000].
2. The elements in the array will be in the range of [-1000, 1000].
3. 0 <= k <= len(arr) *)

(* 引入所需的Coq库 *)
Require Import Coq.Lists.List.      (* List基本操作 *)
Require Import Coq.ZArith.ZArith.    (* 整数Z *)
Require Import Coq.Sorting.Permutation. (* Permutation定义 *)
Require Import Coq.Sorting.Sorted.      (* Sorted定义 *)
Import ListNotations.
(* 打开整数和列表的作用域以便使用相关操作符 *)
Open Scope Z_scope.
Open Scope list_scope.

(* 约束：1 <= length arr <= 1000；元素绝对值 <= 1000；0 <= k <= length arr *)
Definition problem_120_pre (arr : list Z) (k : nat) : Prop :=
       (length arr >= 1)%nat /\ (length arr <= 1000)%nat /\
       Forall (fun z => (-1000 <= z /\ z <= 1000)) arr /\
       (k <= length arr)%nat.

(*
 * @brief 程序规约：top_k_spec
 * @param arr 输入的整数列表
 * @param k   需要选出的最大元素数量
 * @param res 输出的结果列表
 *
 * 这个规约断言 res 是 arr 中 k 个最大元素的有序列表。
 *)
Definition problem_120_spec (arr : list Z) (k : nat) (res : list Z) : Prop :=
  (* 1. 输出列表的长度必须为 k *)
  length res = k /\

  (* 2. 输出列表必须是升序排列的 *)
  Sorted Z.le res /\

  (* 3. 存在一个 "剩余" 列表 rest_of_arr，它包含 arr 中所有未被选入 res 的元素 *)
  (exists rest_of_arr,
    (* 3a. res 和 rest_of_arr 的组合是原始列表 arr 的一个排列组合。
           这确保了 res 中的所有元素都来自 arr，且元素的数量/重复次数正确。 *)
    Permutation (res ++ rest_of_arr) arr /\

    (* 3b. res 中的任何元素都必须大于或等于 rest_of_arr 中的任何元素。
           这确保了 res 包含的是 k 个最大的数。 *)
    (forall x y, In x res -> In y rest_of_arr -> y <= x)).