(*You are given two intervals,
where each interval is a pair of integers. For example, interval = (start, end) = (1, 2).
The given intervals are closed which means that the interval (start, end)
includes both start and end.
For each given interval, it is assumed that its start is less or equal its end.
Your task is to determine whether the length of intersection of these two
intervals is a prime number.
Example, the intersection of the intervals (1, 3), (2, 4) is (2, 3)
which its length is 1, which not a prime number.
If the length of the intersection is a prime number, return "YES",
otherwise, return "NO".
If the two intervals don't intersect, return "NO".


[input/output] samples:
intersection((1, 2), (2, 3)) ==> "NO"
intersection((-1, 1), (0, 4)) ==> "NO"
intersection((-3, -1), (-5, 5)) ==> "YES" *)

(* 引入所需的基础 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
(* 提供 Nat 的比较和取模运算 *)

(* 允许使用列表和作用域的标准表示法 *)
Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope string_scope.

(* 区间为闭区间，且满足 start <= end *)
Definition problem_127_pre (i1 i2 : Z * Z) : Prop :=
  let '(s1,e1) := i1 in
  let '(s2,e2) := i2 in s1 <= e1 /\ s2 <= e2.

Definition problem_127_spec (i1 i2 : Z * Z) (output : string) : Prop :=
  let (s1, e1) := i1 in
  let (s2, e2) := i2 in

  (* 计算交集的起始点和结束点 *)
  let s_inter := Z.max s1 s2 in
  let e_inter := Z.min e1 e2 in

  (* 分情况讨论：区间是否相交 *)
  if Z.leb s_inter e_inter then
    (* 情况1: 区间相交 *)
    let len_nat := Z.to_nat (e_inter - s_inter) in
    (* 规约：
       - 如果交集长度是素数，那么输出必须是 "YES"。
       - 如果交集长度不是素数，那么输出必须是 "NO"。
       我们用逻辑 "或" (\/) 来连接这两种可能。*)
    (prime (Z.of_nat len_nat) /\ output = "YES") \/
    (~prime (Z.of_nat len_nat) /\ output = "NO")
  else
    (* 情况2: 区间不相交，输出必须是 "NO" *)
    output = "NO".