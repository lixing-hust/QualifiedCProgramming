(* def can_arrange(arr):
Create a function which returns the largest index of an element which
is not greater than or equal to the element immediately preceding it. If
no such element exists then return -1. The given array will not contain
duplicate values.

Examples:
can_arrange([1,2,4,3,5]) = 3
can_arrange([1,2,3]) = -1 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.


(* 辅助：在位置 k (nat) 满足 C 程序中的条件 arr[k] <= k。 *)
Definition can_arrange_at (lst : list Z) (k : nat) : Prop :=
  (k < length lst)%nat /\
  match nth_error lst k with
  | Some x => (x <= Z.of_nat k)%Z
  | None => False
  end.

(* 输入数组不包含重复元素 *)
Definition problem_135_pre (lst : list Z) : Prop := NoDup lst.

(* 最终 Spec：
   - 若 r = -1，则不存在任何 k 使得 can_arrange_at lst k 成立；
   - 否则存在一个自然数 k，使 r = Z.of_nat k 且 can_arrange_at lst k，
     并且 k 是满足 can_arrange_at 的最大索引。 *)
Definition problem_135_spec (lst : list Z) (r : Z) : Prop :=
  (r = -1 /\ (forall k, ~ can_arrange_at lst k))
  \/
  (exists k : nat,
      r = Z.of_nat k /\
      can_arrange_at lst k /\
      (forall j : nat, can_arrange_at lst j -> (j <= k)%nat)).
