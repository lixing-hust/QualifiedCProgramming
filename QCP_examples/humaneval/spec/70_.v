(* def strange_sort_list(lst):
'''
Given list of integers, return list in strange order.
Strange sorting, is when you start with the minimum value,
then maximum of the remaining integers, then minimum and so on.

Examples:
strange_sort_list([1, 2, 3, 4]) == [1, 4, 2, 3]
strange_sort_list([5, 5, 5, 5]) == [5, 5, 5, 5]
strange_sort_list([]) == []
''' *)
(* 引入 Coq 标准库以使用列表、自然数和置换等概念 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.

(* 引入列表的标准表示法，如 [] 和 x :: xs *)
Import ListNotations.
Open Scope Z_scope.

(*
  辅助定义 1: is_min l a
  断言 'a' 是自然数列表 'l' 中的最小元素。
  它要求 'a' 必须在 'l' 中，并且 'l' 中的所有元素都大于等于 'a'。
*)
Definition is_min (l : list Z) (a : Z) : Prop :=
  In a l /\ (forall x, In x l -> Z.le a x).

(*
  辅助定义 2: is_max l a
  断言 'a' 是自然数列表 'l' 中的最大元素。
  它要求 'a' 必须在 'l' 中，并且 'l' 中的所有元素都小于等于 'a'。
*)
Definition is_max (l : list Z) (a : Z) : Prop :=
  In a l /\ (forall x, In x l -> Z.le x a).

(*
  核心定义: StrangeSort_Min 与 StrangeSort_Max
  这是一个相互递归的归纳定义，用于描述“奇怪排序”的交替规则。
*)
Inductive StrangeSort_Min : list Z -> list Z -> Prop :=
  (* 基本情况: 空列表的奇怪排序结果是空列表 *)
  | SSMin_nil : StrangeSort_Min [] []
  
  (*
    归纳情况:
    如果 'x' 是列表 'l' 的最小值，
    并且 'xs' 是对除去 'x' 后的剩余列表 'l_rem' 进行“从最大值开始”的奇怪排序的结果，
    那么 'x :: xs' 就是对 'l' 进行“从最小值开始”的奇怪排序的结果。
    我们使用 `Permutation l (x :: l_rem)` 来表示 'l_rem' 是 'l' 除去一个 'x' 后的列表。
  *)
  | SSMin_cons : forall l l_rem x xs,
      Permutation l (x :: l_rem) ->
      is_min l x ->
      StrangeSort_Max l_rem xs ->
      StrangeSort_Min l (x :: xs)

with StrangeSort_Max : list Z -> list Z -> Prop :=
  (* 基本情况: 空列表的奇怪排序结果是空列表 *)
  | SSMax_nil : StrangeSort_Max [] []
  
  (*
    归纳情况:
    如果 'y' 是列表 'l' 的最大值，
    并且 'ys' 是对除去 'y' 后的剩余列表 'l_rem' 进行“从最小值开始”的奇怪排序的结果，
    那么 'y :: ys' 就是对 'l' 进行“从最大值开始”的奇怪排序的结果。
  *)
  | SSMax_cons : forall l l_rem y ys,
      Permutation l (y :: l_rem) ->
      is_max l y ->
      StrangeSort_Min l_rem ys ->
      StrangeSort_Max l (y :: ys).

Definition problem_70_pre (l_in : list Z) : Prop := True.
(*
  程序规约 (Spec): problem_70_spec l_in l_out
  
  对于输入列表 l_in 和输出列表 l_out，我们断言它们满足 StrangeSort_Min 关系，
  因为题目描述的排序是从最小值开始的。

*)
Definition problem_70_spec (l_in l_out : list Z) : Prop :=
  StrangeSort_Min l_in l_out.

