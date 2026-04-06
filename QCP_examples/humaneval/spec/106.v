(* Implement the function f that takes n as a parameter,
and returns a list of size n, such that the value of the element at index i is the factorial of i if i is even
or the sum of numbers from 1 to i otherwise.
i starts from 1.
the factorial of i is the multiplication of the numbers from 1 to i (1 * 2 * ... * i).
Example:
f(5) == [1, 2, 6, 24, 15] *)

(* 引入 Coq 的自然数和列表库 *)
Require Import Nat.
Require Import List.
Require Import Factorial.
Import ListNotations.

(* n 为自然数，无额外约束 *)
Definition problem_106_pre (n : nat) : Prop := True.

Definition problem_106_spec (n : nat) (l : list nat) : Prop :=
  (* 规约作为输入/输出关系，而不是直接计算输出。
     l 的长度必须为 n，并且对于每个位置 i (问题陈述中从 1 开始)，
     l 中第 i 个元素（在 Coq 列表中为 index i-1）当 i 为偶数时等于 factorial i，
     否则等于从 1 到 i 的和。

     实现说明：为避免单独的递归定义，我们在规约内部使用高斯求和公式来计算
     1+2+...+i：sum i = (i * (i + 1)) / 2，并通过局部函数 `sum` 引入该表达式。
  *)
  let sum := fun i => Nat.div (i * (i + 1)) 2 in
  length l = n /\
  (forall i, 1 <= i -> i <= n -> nth_error l (i - 1) = Some (if even i then fact i else sum i)).
