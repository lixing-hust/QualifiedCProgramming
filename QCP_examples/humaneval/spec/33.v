(* This function takes a list l and returns a list l' such that
l' is identical to l in the indicies that are not divisible by three, while its values at the indicies that are divisible by three are equal
to the values of the corresponding indicies of l, but sorted.
>>> sort_third([1, 2, 3])
[1, 2, 3]
>>> sort_third([5, 6, 3, 4, 8, 9, 2])
[2, 6, 3, 4, 8, 9, 5] *)

(* Spec(input : list int, output : list int) :=

​	length(input) = length(output) /\
​	∀i ∈ [0, length(input)), i % 3 <> 0 → output[i] = input[i]  /\
​	∀i ∈ [0, length(output)), ∃  j ∈ [0, length(intput))  i %3 = 0 -> j % 3 = 0 /\ input[j] = output[i] 
​	∀i ∈ [0, length(input)), ∃  j ∈ [0, length(output))  i %3 = 0 -> j % 3 = 0 /\ output[j] = input[i] /\ 
​	∀i,j ∈ [0, length(input)), i,j % 3 == 0 /\ i < j → output[i] ≤ output[j]

*)


Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Import ListNotations.
(* Pre: no additional constraints for `sort_third` by default *)
Definition problem_33_pre (input : list Z) : Prop := True.

(* Spec 的定义 *)
Definition problem_33_spec (input output : list Z) : Prop :=
  (* 1. input 是 output 的排列 (Permutation) *)
  Permutation input output /\

  (* 2. 如果索引 i 不能被 3 整除，则 output[i] 必须等于 input[i] *)
  (forall (i : nat), (i < length input)%nat -> (i mod 3 <> 0) ->
    nth i output 0%Z = nth i input 0%Z) /\

  (* 3. output 中所有索引能被 3 整除的元素，必须是按索引顺序排好序的 (非递减) *)
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 3 = 0 /\ j mod 3 = 0 /\ i < j ->
    (nth i output 0 <= nth j output 0)%Z).