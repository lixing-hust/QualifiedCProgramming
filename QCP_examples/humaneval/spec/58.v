(* def common(l1: list, l2: list):
"""Return sorted unique common elements for two lists.
>>> common([1, 4, 3, 34, 653, 2, 5], [5, 7, 1, 5, 9, 653, 121])
[1, 5, 653]
>>> common([5, 3, 2, 8], [3, 2])
[2, 3]

""" *)
Require Import Coq.ZArith.ZArith. (* 导入整数库，提供 Z 类型和 Z.le *)
Require Import Coq.Lists.List.      (* 导入列表库 *)
Require Import Sorting.Sorted.
Import ListNotations.

(*
 *
 * 描述了输入列表 l1, l2 与输出列表 l_out 之间的关系。
 *)
(* Pre: no special constraints for `common` *)
Definition problem_58_pre (l1 l2 : list Z) : Prop := True.

Definition problem_58_spec (l1 l2 l_out: list Z) : Prop :=
  (* 条件1: 公共性与完备性 *)
  (* l_out 中的任意整数 x，当且仅当 x 同时在 l1 和 l2 中。*)
  (forall x: Z, In x l_out <-> (In x l1 /\ In x l2)) /\

  (* 条件2: 有序性 *)
  (* l_out 是根据整数的小于等于关系 (Z.le) 排序的。 *)
  Sorted Z.le l_out /\

  (* 条件3: 唯一性 *)
  (* l_out 中没有重复元素。 *)
  NoDup l_out.
 