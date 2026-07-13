(* Given a non-empty list of integers, return the sum of all of the odd elements that are in even positions.
Examples
solution([5, 8, 7, 1]) ==> 12
solution([3, 3, 3, 3, 3]) ==> 9
solution([30, 13, 24, 321]) ==>0*)

Require Import Coq.Arith.Arith Coq.Lists.List.
Import ListNotations.

(* selected_121 states that indices/values are exactly the odd values at even zero-based indices. *)
Definition selected (l indices values : list nat) : Prop :=
  NoDup indices /\
  Forall2
    (fun i x => nth_error l i = Some x /\ Nat.Even i /\ Nat.Odd x)
    indices values /\
  forall i x,
    nth_error l i = Some x ->
    Nat.Even i ->
    Nat.Odd x ->
    In i indices.

(* problem_121_pre requires a non-empty list. *)
Definition problem_121_pre (l : list nat) : Prop := l <> [].

(* problem_121_spec states that output is the sum of all odd values at even zero-based indices. *)
Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  exists indices values,
    selected l indices values /\
    output = fold_right Nat.add 0 values.
