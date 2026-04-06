(* def tri(n):
"""Everyone knows Fibonacci sequence, it was studied deeply by mathematicians in
the last couple centuries. However, what people don't know is Tribonacci sequence.
Tribonacci sequence is defined by the recurrence:
tri(1) = 3
tri(n) = 1 + n / 2, if n is even.
tri(n) = tri(n - 1) + tri(n - 2) + tri(n + 1), if n is odd.
For example:
tri(2) = 1 + (2 / 2) = 2
tri(4) = 3
tri(3) = tri(2) + tri(1) + tri(4)
= 2 + 3 + 3 = 8
You are given a non-negative integer number n, you have to a return a list of the
first n + 1 numbers of the Tribonacci sequence.
Examples:
tri(3) = [1, 3, 2, 8]
""" *)
Require Import Arith.
Require Import List.
Import ListNotations.


(* 定义一个归纳关系来描述Tribonacci序列中每个元素的值 *)
Inductive trib_val : nat -> nat -> Prop :=
  | trib_1 : trib_val 1 3
  | trib_even : forall n, n mod 2 = 0 -> trib_val n (1 + n / 2)
  | trib_odd : forall n v1 v2 v3,
      n > 1 ->
      n mod 2 = 1 ->
      trib_val (n - 1) v1 ->
      trib_val (n - 2) v2 ->
      trib_val (n + 1) v3 ->
      trib_val n (v1 + v2 + v3).

(* n 为非负整数（nat 已满足），无额外约束 *)
Definition problem_130_pre (n : nat) : Prop := True.

(* 定义tri函数的程序规约 *)
Definition problem_130_spec (n : nat) (l : list nat) : Prop :=
  length l = n + 1 /\
  forall i, i <= n ->
    exists v, nth i l 0 = v /\ trib_val i v.