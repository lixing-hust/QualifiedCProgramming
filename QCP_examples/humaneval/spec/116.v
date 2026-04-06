(*In this Kata, you have to sort an array of non-negative integers according to
number of ones in their binary representation in ascending order.
For similar number of ones, sort based on decimal value.

It must be implemented like this:
>>> sort_array([1, 5, 2, 3, 4]) == [1, 2, 3, 4, 5]
>>> sort_array([1, 0, 2, 3, 4]) [0, 1, 2, 3, 4] *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Permutation.
Require Import Sorting.Sorted.
Import ListNotations.


(*
  定义一个带有 "燃料" 参数的辅助函数。
  递归在燃料参数 `fuel` 上是结构性的 (S fuel' -> fuel')，
  这满足了 Coq 对 Fixpoint 的要求。
*)
Fixpoint count_ones_helper (n fuel : nat) : nat :=
  match fuel with
  | 0 => 0 (* 燃料耗尽，停止递归 *)
  | S fuel' => (* 还有燃料 *)
      match n with
      | 0 => 0 (* n为0，递归的自然基准情况 *)
      | _ => (n mod 2) + count_ones_helper (n / 2) fuel' (* 递归调用，燃料减少 *)
      end
  end.

(*
  定义主函数，它用 n 自身作为初始燃料来调用辅助函数。
  对于任何 n，其二进制表示的位数都小于 n 本身，所以 n 是足够多的“燃料”。
*)
Definition count_ones (n : nat) : nat :=
  count_ones_helper n n.

(*
  定义两个自然数的比较逻辑:
  - 首先比较它们二进制中1的个数
  - 如果1的个数相等，则直接比较数值大小
*)
Definition lt_custom (a b : nat) : Prop :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  (ones_a < ones_b) \/ (ones_a = ones_b /\ a < b).

(* 用于实现的bool版本比较函数 *)
Definition lt_custom_bool (a b : nat) : bool :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  if ones_a <? ones_b then true
  else if ones_a =? ones_b then a <? b
  else false.

(*
  排序函数的规约 (Spec)

  它描述了输入列表(input)和输出列表(output)之间的关系
*)

(* 实现排序函数 *)
Fixpoint insert_sorted (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t =>
      if lt_custom_bool x h then
        x :: l
      else
        h :: insert_sorted x t
  end.

Fixpoint sort_array_impl (input : list nat) : list nat :=
  match input with
  | [] => []
  | h :: t => insert_sorted h (sort_array_impl t)
  end.

(* 输入为非负整数列表（nat 已保证） *)
Definition problem_116_pre (input : list nat) : Prop := True.

Definition problem_116_spec (input output : list nat) : Prop :=
  output = sort_array_impl input.