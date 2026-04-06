(* def count_up_to(n):
"""Implement a function that takes an non-negative integer and returns an array of the first n
integers that are prime numbers and less than n.
for example:
count_up_to(5) => [2,3]
count_up_to(11) => [2,3,5,7]
count_up_to(0) => []
count_up_to(20) => [2,3,5,7,11,13,17,19]
count_up_to(1) => []
count_up_to(18) => [2,3,5,7,11,13,17]
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted. (* 引入 Sorted 定义 *)
Import ListNotations.
Open Scope nat_scope.

(* n 是自然数即非负，无附加约束 *)
Definition problem_96_pre (n : nat) : Prop := True.


Definition problem_96_spec (n : nat) (result : list nat) : Prop :=
  (* 属性1: 结果列表中的所有元素都是素数 *)
  (forall p, In p result -> prime (Z.of_nat p)) /\

  (* 属性2: 结果列表中的所有元素都小于 n *)
  (forall p, In p result -> p < n) /\

  (* 属性3: 所有小于 n 的素数都在结果列表中 (完备性) *)
  (forall p, prime (Z.of_nat p) -> p < n -> In p result) /\

  (* 属性4: 列表是严格升序的 *)
  Sorted lt result /\

  (* 属性5: 列表中没有重复元素 *)
  NoDup result.