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


(* 使用Fixpoint来实现Tribonacci序列的计算 *)
Fixpoint tri (n : nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 3
  | S (S k) =>
      if Nat.even n then
        1 + n / 2
      else
        let t_prev := 1 + (n - 1) / 2 in
        let t_next := 1 + (n + 1) / 2 in
        t_prev + tri k + t_next
  end.

(* n 为非负整数（nat 已满足），无额外约束 *)
Definition problem_130_pre (n : nat) : Prop := True.

(* 定义tri函数的程序规约 *)
Definition problem_130_spec (n : nat) (l : list nat) : Prop :=
  length l = n + 1 /\
  forall i, i <= n -> nth i l 0 = tri i.