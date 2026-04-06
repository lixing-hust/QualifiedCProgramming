(* def get_max_triples(n):
You are given a positive integer n. You have to create an integer array a of length n.
For each i (1 ≤ i ≤ n), the value of a[i] = i * i - i + 1.
Return the number of triples (a[i], a[j], a[k]) of a where i < j < k,
and a[i] + a[j] + a[k] is a multiple of 3.

Example :
Input: n = 5
Output: 1
Explanation:
a = [1, 3, 7, 13, 21]
The only valid triple is (1, 7, 13). *)
(* 引入所需的基础库 *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.


(*
 * 定义函数 a(i)，对应于 Python 程序中的 a[i] = i*i - i + 1。
 * 这里的索引 i 是从 1 开始的自然数（nat）。
 * 为了避免自然数减法可能出现的问题，我们使用整数（Z）进行计算。
 *)
Definition a_val (i : nat) : Z :=
  let i_z := Z.of_nat i in
  i_z * i_z - i_z + 1.

(*
 * 定义一个“有效三元组”的属性。
 * 一个三元组 (i, j, k) 是有效的，当且仅当它满足以下所有条件：
 * 1. 索引 i, j, k 满足 1 <= i < j < k <= n。
 * 2. 对应的值 a(i), a(j), a(k) 之和是 3 的倍数。
 *)
Definition is_valid_triple (n i j k : nat) : Prop :=
  (1 <= i)%nat /\ (i < j)%nat /\ (j < k)%nat /\ (k <= n)%nat /\
  (a_val i + a_val j + a_val k) mod 3 = 0.

(* 独立的输入前置条件 *)
Definition problem_147_pre (n : nat) : Prop := n > 0.

(*
 * get_max_triples 函数的程序规约。
 * 它通过一阶逻辑描述了输入 n 和输出 output 之间的关系。
 *)
Definition problem_147_spec (n : nat) (output : nat) : Prop :=
  (*
   * 存在一个三元组列表 l，它精确地包含了所有有效的、不重复的三元组，
   * 并且 output 是这个列表的长度。
   *)
  exists (l : list (nat * nat * nat)),
    (* 1. 列表 l 中的每一个元素 (i, j, k) 都必须是一个有效的 instill 三元组。 *)
    (forall ijk, In ijk l ->
      let '(i, j, k) := ijk in is_valid_triple n i j k) /\

    (* 2. 所有有效的 instill 三元组 (i, j, k) 都必须在列表 l 中。 *)
    (forall i j k, is_valid_triple n i j k -> In (i, j, k) l) /\

    (* 3. 列表 l 中没有重复的元素。 *)
    NoDup l /\

    (* 4. 函数的输出 output 必须等于列表 l 的长度。 *)
    output = length l.