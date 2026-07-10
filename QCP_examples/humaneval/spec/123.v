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

(* collatz_step relates one Collatz sequence value to its successor. *)
Definition collatz_step (x y : Z) : Prop :=
  x <> 1 /\ y = if Z.even x then x / 2 else 3 * x + 1.

(* collatz_list says l starts at n, ends at 1, and follows Collatz adjacent steps. *)
Definition collatz_list (n : Z) (l : list Z) : Prop :=
  l <> [] /\
  hd 0 l = n /\
  last l 0 = 1 /\
  Forall (fun p => collatz_step (fst p) (snd p)) (combine l (tl l)).

(* problem_123_pre requires a positive input. *)
Definition problem_123_pre (n : Z) : Prop := n > 0.
(*
  [get_odd_collatz_spec n result] 定义了程序的规约。
  它描述了输入 [n] 和输出 [result] 之间必须满足的关系。
*)
(* problem_123_spec returns the sorted odd elements of a Collatz sequence for n. *)
Definition  problem_123_spec (n : Z) (result : list Z) : Prop :=
  (* 存在一个列表 c_seq ... *)
  exists (c_seq : list Z),
    (* ... c_seq 是 n 的 Collatz 序列 ... *)
    collatz_list n c_seq /\
    (* ... 并且，输出 result 是 c_seq 中所有奇数元素构成的列表的一个排列 ... *)
    Permutation result (filter (fun x => Z.odd x) c_seq) /\ (* <- 已修正 *)
    (* ... 并且，输出 result 必须是升序排列的。 *)
    Sorted Z.le result.
