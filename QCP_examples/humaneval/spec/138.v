(* def is_equal_to_sum_even(n):
"""Evaluate whether the given number n can be written as the sum of exactly 4 positive even numbers
Example
is_equal_to_sum_even(4) == False
is_equal_to_sum_even(6) == False
is_equal_to_sum_even(8) == True
""" *)
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* 正的偶数：存在 k>0 使 e = 2*k *)
Definition is_positive_even (e : Z) : Prop :=
  exists k : Z, e = 2 * k /\ (k > 0)%Z.

(* 任意整数 n 均可 *)
Definition problem_138_pre (n : Z) : Prop := True.

(* Spec：当且仅当存在四个正偶数之和等于 n 时返回 true *)
Definition problem_138_spec (n : Z) (b : bool) : Prop :=
  b = true <-> exists e1 e2 e3 e4 : Z,
    is_positive_even e1 /\
    is_positive_even e2 /\
    is_positive_even e3 /\
    is_positive_even e4 /\
    n = e1 + e2 + e3 + e4.
