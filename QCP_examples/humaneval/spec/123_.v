(* Given a positive integer n, return a sorted list that has the odd numbers in collatz sequence.

The Collatz conjecture is a conjecture in mathematics that concerns a sequence defined
as follows: start with any positive integer n. Then each term is obtained from the
previous term as follows: if the previous term is even, the next term is one half of
the previous term. If the previous term is odd, the next term is 3 times the previous
term plus 1. The conjecture is that no matter what value of n, the sequence will always reach 1.

Note:
1. Collatz(1) is [1].
2. returned list sorted in increasing order.

For example:
get_odd_collatz(5) returns [1, 5] # The collatz sequence for 5 is [5, 16, 8, 4, 2, 1], so the odd numbers are only 1, and 5. *)

(* 引用 Coq 标准库 *)
Require Import Coq.ZArith.ZArith.   (* 整数库 *)
Require Import Coq.Lists.List.      (* 列表库 *)
Require Import Coq.Sorting.Permutation. (* 列表置换关系 *)
Require Import Coq.Sorting.Sorted.      (* 列表排序谓词 *)

Import ListNotations.
Open Scope Z_scope.

(*
  [collatz_list n l] 定义了一个归纳谓词，
  用来描述列表 [l] 是从正整数 [n] 开始的 Collatz 序列。
  该定义隐含了序列会终止于 1 的假设。
*)
Inductive collatz_list (n : Z) : list Z -> Prop :=
  (* 基础情况：如果 n 等于 1，那么它的 Collatz 序列是 [1] *)
  | cl_one : n = 1 -> collatz_list n [1]
  (* 归纳步骤（偶数）：如果 n 是大于 1 的偶数，
     且 l' 是 n/2 的 Collatz 序列，那么 (n :: l') 是 n 的 Collatz 序列。*)
  | cl_even : forall l',
      n > 1 ->
      Z.even n = true -> (* <- 已修正 *)
      collatz_list (n / 2) l' ->
      collatz_list n (n :: l')
  (* 归纳步骤（奇数）：如果 n 是大于 1 的奇数，
     且 l' 是 3*n+1 的 Collatz 序列，那么 (n :: l') 是 n 的 Collatz 序列。*)
  | cl_odd : forall l',
      n > 1 ->
      Z.odd n = true -> (* <- 已修正 *)
      collatz_list (3 * n + 1) l' ->
      collatz_list n (n :: l').

(* n 为正整数 *)
Definition problem_123_pre (n : Z) : Prop := n > 0.
(*
  [problem_123_spec n result] 定义了程序的规约。
  它描述了输入 [n] 和输出 [result] 之间必须满足的关系。
*)
Definition  problem_123_spec (n : Z) (result : list Z) : Prop :=
  (* 存在一个列表 c_seq ... *)
  exists (c_seq : list Z),
    (* ... c_seq 是 n 的 Collatz 序列 ... *)
    collatz_list n c_seq /\
    (* ... 并且，输出 result 是 c_seq 中所有奇数元素构成的列表的一个排列 ... *)
    Permutation result (filter (fun x => Z.odd x) c_seq) /\ (* <- 已修正 *)
    (* ... 并且，输出 result 必须是升序排列的。 *)
    Sorted Z.le result.