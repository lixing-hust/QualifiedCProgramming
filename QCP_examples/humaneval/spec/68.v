(* def pluck(arr):
Given an array representing a branch of a tree that has non-negative integer nodes
your task is to pluck one of the nodes and return it.
The plucked node should be the node with the smallest even value.
If multiple nodes with the same smallest even value are found return the node that has smallest index.

The plucked node should be returned in a list, [ smalest_value, its index ],
If there are no even values or the given array is empty, return [].

Example 1:
Input: [4,2,3]
Output: [2, 1]
Explanation: 2 has the smallest even value, and 2 has the smallest index.

Example 2:
Input: [1,2,3]
Output: [2, 1]
Explanation: 2 has the smallest even value, and 2 has the smallest index.

Example 3:
Input: []
Output: []

Example 4:
Input: [5, 0, 3, 0, 4, 2]
Output: [0, 1]
Explanation: 0 is the smallest value, but there are two zeros,
so we will choose the first zero, which has the smallest index.

Constraints:
* 1 <= nodes.length <= 10000
* 0 <= node.value
*)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Definition problem_68_pre (arr : list nat) : Prop := True.

(* pluck 函数的程序规约 *)
Definition problem_68_spec (arr : list nat) (output : option (nat * nat)) : Prop :=
  match output with
  | None => (* 情况1: 输出为空 *)
    (* 当且仅当列表中没有偶数时，输出为 None *)
    forall val, In val arr -> Nat.even val = false
  | Some (v, i) => (* 情况2: 输出为 Some (v, i) *)
    (* 1. v 必须是 arr 中索引为 i 的元素 *)
    i < length arr /\ nth i arr 1 = v /\
    (* 2. v 必须是偶数 *)
    Nat.even v = true/\
    (* 3. v 必须是 arr 中所有偶数里最小的值 *)
    (forall val, In val arr -> Nat.even val = true -> v <= val) /\
    (* 4. i 必须是 v 在 arr 中首次出现的最小索引 *)
    (forall j, j < i -> nth j arr 1 <> v)
  end.

