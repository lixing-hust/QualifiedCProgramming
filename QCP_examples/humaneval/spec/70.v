(* def strange_sort_list(lst):
'''
Given list of integers, return list in strange order.
Strange sorting, is when you start with the minimum value,
then maximum of the remaining integers, then minimum and so on.

Examples:
strange_sort_list([1, 2, 3, 4]) == [1, 4, 2, 3]
strange_sort_list([5, 5, 5, 5]) == [5, 5, 5, 5]
strange_sort_list([]) == []
''' *)
(* 引入 Coq 标准库以使用列表、自然数和置换等概念 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.

(* 引入列表的标准表示法，如 [] 和 x :: xs *)
Import ListNotations.
Open Scope Z_scope.

(* count_z counts occurrences of an integer with the library count_occ. *)
Definition count_z (x : Z) (l : list Z) : nat :=
  count_occ Z.eq_dec l x.

(* available_after_prefix says x still remains after taking the first i outputs. *)
Definition available_after_prefix (l_in l_out : list Z) (x : Z) (i : nat) : Prop :=
  (count_z x (firstn i l_out) < count_z x l_in)%nat.

(* strange_extremal_at states the min/max choice required at output index i. *)
Definition strange_extremal_at (l_in l_out : list Z) (i : nat) (v : Z) : Prop :=
  available_after_prefix l_in l_out v i /\
  (Nat.even i = true -> forall y, available_after_prefix l_in l_out y i -> v <= y) /\
  (Nat.odd i = true -> forall y, available_after_prefix l_in l_out y i -> y <= v).

(* problem_70_pre imposes no input constraints. *)
Definition problem_70_pre (l_in : list Z) : Prop := True.

(* problem_70_spec characterizes alternating min/max selection from remaining values. *)
Definition problem_70_spec (l_in l_out : list Z) : Prop :=
  Permutation l_out l_in /\
  (forall i v, nth_error l_out i = Some v -> strange_extremal_at l_in l_out i v).
