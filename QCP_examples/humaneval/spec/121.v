(* Given a non-empty list of integers, return the sum of all of the odd elements that are in even positions.
Examples
solution([5, 8, 7, 1]) ==> 12
solution([3, 3, 3, 3, 3]) ==> 9
solution([30, 13, 24, 321]) ==>0*)

Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

(* sum_odd_in_even_pos_aux sums odd values paired with even zero-based indices. *)
Definition sum_odd_in_even_pos_aux (l : list nat) (idx : nat) : nat :=
  fold_left
    Nat.add
    (map
       (fun p =>
          let i := fst p in
          let h := snd p in
          if (Nat.even i) && negb (Nat.even h) then h else 0)
       (combine (seq idx (length l)) l))
    0.

(* sum_odd_in_even_pos_impl starts the indexed sum at index 0. *)
Definition sum_odd_in_even_pos_impl (l : list nat) : nat := sum_odd_in_even_pos_aux l 0.

(* problem_121_pre requires a non-empty list. *)
Definition problem_121_pre (l : list nat) : Prop := l <> [].

(* problem_121_spec states that output is the selected-index sum. *)
Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  output = sum_odd_in_even_pos_impl l.
