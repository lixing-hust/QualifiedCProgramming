(* def search(lst):
'''
You are given a non-empty list of positive integers. Return the greatest integer that is greater than
zero, and has a frequency greater than or equal to the value of the integer itself.
The frequency of an integer is the number of times it appears in the list.
If no such a value exist, return -1.
Examples:
search([4, 1, 2, 2, 3, 1]) == 2
search([1, 2, 2, 3, 3, 3, 4, 4, 4]) == 3
search([5, 5, 4, 4, 4]) == -1 *)
Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

(* count returns the frequency of z in lst using the library filter. *)
Definition count (z : Z) (lst : list Z) : nat :=
  length (filter (fun h => Z.eqb z h) lst).

(* find_max_satisfying folds over candidates and keeps the greatest valid value. *)
Definition find_max_satisfying (lst : list Z) (candidates : list Z) (current_max : Z) : Z :=
  fold_left
    (fun best h =>
       if Z.of_nat (count h lst) >=? h then Z.max h best else best)
    candidates
    current_max.

(* search_impl returns the greatest value whose frequency is at least the value. *)
Definition search_impl (lst : list Z) : Z :=
  match lst with
  | [] => (-1)%Z
  | _ =>
      let candidates := lst in
      let max_val := find_max_satisfying lst candidates (-1)%Z in
      if max_val =? (-1)%Z then
        (-1)%Z
      else
        max_val
  end.

(* problem_69_pre requires a non-empty list of positive integers. *)
Definition problem_69_pre (lst : list Z) : Prop := lst <> []%list /\ (forall x, In x lst -> (x > 0)%Z).

(* problem_69_spec states that y is the result of the frequency search. *)
Definition problem_69_spec (lst : list Z) (y : Z) : Prop :=
  y = search_impl lst.
