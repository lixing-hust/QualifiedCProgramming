(*In this Kata, you have to sort an array of non-negative integers according to
number of ones in their binary representation in ascending order.
For similar number of ones, sort based on decimal value.

It must be implemented like this:
>>> sort_array([1, 5, 2, 3, 4]) == [1, 2, 3, 4, 5]
>>> sort_array([1, 0, 2, 3, 4]) [0, 1, 2, 3, 4] *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Permutation.
Require Import Sorting.Sorted.
Import ListNotations.

(* count_ones counts set bits in the lower 31 binary positions. *)
Definition count_ones (n : nat) : nat :=
  length (filter (fun p => Nat.eqb ((n / Nat.pow 2 p) mod 2) 1) (seq 0 31)).

(* le_custom orders numbers first by bit count and then by numeric value. *)
Definition le_custom (a b : nat) : Prop :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  (ones_a < ones_b) \/ (ones_a = ones_b /\ a <= b).

(* problem_116_pre imposes no extra constraints beyond nat inputs. *)
Definition problem_116_pre (input : list nat) : Prop := True.

(* problem_116_spec characterizes sorting by bit count and numeric tie-breaker. *)
Definition problem_116_spec (input output : list nat) : Prop :=
  Permutation output input /\
  Sorted le_custom output.
