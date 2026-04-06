(* triples_sum_to_zero takes a list of integers as an input.
it returns True if there are three distinct elements in the list that
sum to zero, and False otherwise.

>>> triples_sum_to_zero([1, 3, 5, 0])
False
>>> triples_sum_to_zero([1, 3, -2, 1])
True
>>> triples_sum_to_zero([1, 2, 3, 7])
False
>>> triples_sum_to_zero([2, 4, -5, 3, 9, 7])
True
>>> triples_sum_to_zero([1])
False *)

(*Spec(input : list int, output : bool) :=

​	∃i,j,k i<>k /\ i<>j /\ j<>k /\ input[i] + input[j] + input[k] = 0 → output = true /\
​	∀i,j,k i<>k /\ i<>j /\ j<>k /\ input[i] + input[j] + input[k] <> 0 → output = false *)


Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.
(* Pre: no additional constraints for `triples_sum_to_zero` by default *)
Definition problem_40_pre (input : list Z) : Prop := True.

Definition problem_40_spec (input : list Z) (output : bool) : Prop :=
  (*
    存在三个不同的索引 i, j, k，
    使得对应元素之和为 0。
    我们必须同时检查索引 i, j, k 在列表的有效范围内。
    nth 函数需要一个默认值 (这里是0)，如果索引越界，它会返回该默认值.
    但因为我们已经用 i < length input 等条件确保了索引有效，所以默认值不会被用到。
  *)
  (exists i j k : nat,
    (i <> j) /\ (i <> k) /\ (j <> k) /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (k < length input)%nat /\
    (nth i input 0 + nth j input 0 + nth k input 0 = 0))
  <-> (output = true).