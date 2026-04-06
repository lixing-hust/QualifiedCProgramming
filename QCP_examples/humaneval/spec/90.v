(* def next_smallest(lst):
"""
You are given a list of integers.
Write a function next_smallest() that returns the 2nd smallest element of the list.
Return None if there is no such element.

next_smallest([1, 2, 3, 4, 5]) == 2
next_smallest([5, 1, 4, 3, 2]) == 2
next_smallest([]) == None
next_smallest([1, 1]) == None
""" *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_90_pre (l : list Z) : Prop := True.

(*
  problem_90_spec l res

  一个描述 next_smallest 函数行为的规约。

  - l: 输入的整数列表 (list Z)
  - res: 函数的返回结果 (option Z)

  规约分为两种情况:
  1. 当函数返回 Some z (找到了第二小的值):
     - 必须存在一个最小值 s1。
     - z 必须在列表中，并且严格大于 s1。
     - z 必须是所有大于 s1 的元素中最小的那个。

  2. 当函数返回 None (没有找到第二小的值):
     - 这意味着列表中不存在两个或以上不同的元素。
*)
Definition  problem_90_spec (l : list Z) (res : option Z) : Prop :=
  match res with
  | Some z => (* `Some` 情况：z 是第二小的值 *)
    exists s1,
      In s1 l /\                                (* 1. 存在一个元素 s1 在列表 l 中 *)
      (forall x, In x l -> s1 <= x) /\          (* 2. s1 是列表中的最小值 *)
      In z l /\                                 (* 3. z 也在列表 l 中 *)
      s1 < z /\                                 (* 4. z 严格大于最小值 s1 *)
      (forall y, In y l -> s1 < y -> z <= y)    (* 5. 对于任何大于 s1 的列表元素 y，z 都小于或等于 y *)

  | None => (* `None` 情况：列表中没有第二小的值 *)
    ~ (exists x y, In x l /\ In y l /\ x <> y)  (* 列表 l 中不存在两个不同的元素 *)
  end.