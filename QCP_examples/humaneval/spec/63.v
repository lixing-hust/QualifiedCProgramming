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

Fixpoint fibfib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 0
    | S n'' =>
      match n'' with
      | 0 => 1
      | S n''' => fibfib n' + fibfib n'' + fibfib n'''
      end
    end
  end.

Definition problem_63_pre (n : nat) : Prop := True.
(*
  problem_63_spec 是对 fibfib 函数的程序规约。

  它指出，一个函数若要满足此规约，其对于任何输入 n，
  必须返回一个结果 res，使得 res = fibfib n。

  参数：
  - n: nat    (代表程序的输入)
  - res: nat  (代表程序的输出)
*)
Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  res = fibfib n.

