(* def is_simple_power(x, n):
"""Your task is to write a function that returns true if a number x is a simple
power of n and false in other cases.
x is a simple power of n if n**int=x
For example:
is_simple_power(1, 4) => true
is_simple_power(2, 2) => true
is_simple_power(8, 2) => true
is_simple_power(3, 2) => false
is_simple_power(3, 1) => false
is_simple_power(5, 3) => false
""" *)
Require Import Arith. (* 导入包含自然数和幂运算的算术库 *)
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.
(*
  problem_76_spec 定义了输入 x, n 和布尔值输出 result 之间的关系。
  它规定：当且仅当存在一个自然数 k，使得 x = n^k 成立时，函数的返回结果 result 为 true。
*)
Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

