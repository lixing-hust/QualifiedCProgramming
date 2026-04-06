(*def skjkasdkd(lst):
"""You are given a list of integers.
You need to find the largest prime value and return the sum of its digits.

Examples:
For lst = [0,3,2,1,3,5,7,4,5,5,5,2,181,32,4,32,3,2,32,324,4,3] the output should be 10
For lst = [1,0,1,8,2,4597,2,1,3,40,1,2,1,2,4,2,5,1] the output should be 25
For lst = [1,3,1,32,5107,34,83278,109,163,23,2323,32,30,1,9,3] the output should be 13
For lst = [0,724,32,71,99,32,6,0,5,91,83,0,5,6] the output should be 11
For lst = [0,81,12,3,1,21] the output should be 3
For lst = [0,8,1,2,1,7] the output should be 7
""" *)
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Znumtheory. 
Import ListNotations.
Open Scope nat_scope.
(*
  辅助定义2: 计算一个自然数各位数字之和 (使用燃料)
*)
Fixpoint sum_digits_fueled (n fuel : nat) : nat :=
  match fuel with
  | 0 => 0 (* 燃料耗尽，停止递归 *)
  | S fuel' =>
    match n with
    | 0 => 0 (* n 本身为 0，则各位和为 0 *)
    | _ => (n mod 10) + sum_digits_fueled (n / 10) fuel'
    end
  end.

Definition sum_digits (n : nat) : nat :=
  sum_digits_fueled n n.

(* 输入列表可含任意自然数（允许为空） *)
Definition problem_94_pre (lst : list nat) : Prop := True.

Definition problem_94_spec (lst : list nat) (output : nat) : Prop :=
  (exists p,
    (* 1. 必须存在一个p，它是列表lst中的元素 *)
    In p lst /\

    (* 2. p必须是一个素数 *)
    prime (Z.of_nat p) /\

    (* 3. p是列表lst中所有素数里最大的一个 *)
    (forall p', In p' lst -> prime (Z.of_nat p') -> p' <= p) /\

    (* 4. 最终的输出output等于p的各位数字之和 *)
    output = sum_digits p)
  \/
  (* 如果列表中不存在素数，输出为0 *)
  ((forall x, In x lst -> ~ prime (Z.of_nat x)) /\ output = 0).