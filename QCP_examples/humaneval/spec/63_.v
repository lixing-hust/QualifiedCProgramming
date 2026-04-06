(* def fibfib(n: int):
"""The FibFib number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
fibfib(0) == 0
fibfib(1) == 0
fibfib(2) == 1
fibfib(n) == fibfib(n-1) + fibfib(n-2) + fibfib(n-3).
Please write a function to efficiently compute the n-th element of the fibfib number sequence.
>>> fibfib(1)
0
>>> fibfib(5)
4
>>> fibfib(8)
24
""" *)
(* 引入Coq中关于自然数的基础库 *)
Require Import Coq.Init.Nat.

(*
  is_fibfib n res 是一个归纳定义的命题，它断言 "res 是第 n 个 FibFib 数"。
  这个定义直接从 fibfib 函数的数学定义翻译而来。
*)
Inductive is_fibfib : nat -> nat -> Prop :=
  (* Base Case 1: 第 0 个 FibFib 数是 0 *)
  | ff_zero : is_fibfib 0 0

  (* Base Case 2: 第 1 个 FibFib 数是 0 *)
  | ff_one  : is_fibfib 1 0

  (* Base Case 3: 第 2 个 FibFib 数是 1 *)
  | ff_two  : is_fibfib 2 1

  (*
    Inductive Step: 归纳步骤。
    如果 res_n, res_n1, res_n2 分别是第 n, n+1, n+2 个 FibFib 数，
    那么第 n+3 个 FibFib 数就是它们三者的和。
  *)
  | ff_step : forall n res_n res_n1 res_n2,
      is_fibfib n res_n ->
      is_fibfib (S n) res_n1 ->
      is_fibfib (S (S n)) res_n2 ->
      is_fibfib (S (S (S n))) (res_n + res_n1 + res_n2).

Definition problem_63_pre (n : nat) : Prop := True.
(*
  problem_63_spec 是对 fibfib 函数的程序规约。

  它指出，一个函数若要满足此规约，其对于任何输入 n，
  必须返回一个结果 res，使得 is_fibfib n res 命题为真。

  参数：
  - n: nat    (代表程序的输入)
  - res: nat  (代表程序的输出)
*)
Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  is_fibfib n res.

