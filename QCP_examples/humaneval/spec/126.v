(* Given a list of numbers, return whether or not they are sorted
in ascending order. If list has more than 1 duplicate of the same
number, return False. Assume no negative numbers and only integers.

Examples
is_sorted([5]) ➞ True
is_sorted([1, 2, 3, 4, 5]) ➞ True
is_sorted([1, 3, 2, 4, 5]) ➞ False
is_sorted([1, 2, 3, 4, 5, 6]) ➞ True
is_sorted([1, 2, 3, 4, 5, 6, 7]) ➞ True
is_sorted([1, 3, 2, 4, 5, 6, 7]) ➞ False
is_sorted([1, 2, 2, 3, 3, 4]) ➞ True
is_sorted([1, 2, 2, 2, 3, 4]) ➞ False *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.



(* 仅非负整数（nat 已满足），无额外约束 *)
Definition problem_126_pre (l : list nat) : Prop := True.

Definition sorted_no_triple_nat (l : list nat) : Prop :=
  (forall j, (1 <= j < length l)%nat ->
    nth (j - 1) l 0 <= nth j l 0) /\
  (forall j, (2 <= j < length l)%nat ->
    ~ (nth j l 0 = nth (j - 1) l 0 /\
       nth j l 0 = nth (j - 2) l 0)).

(* 程序规约 (Spec) *)
Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  sorted_no_triple_nat l <-> b = true.
