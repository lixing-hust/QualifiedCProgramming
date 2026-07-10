(* def get_row(lst, x):
"""
You are given a 2 dimensional data, as a nested lists,
which is similar to matrix, however, unlike matrices,
each row may contain a different number of columns.
Given lst, and integer x, find integers x in the list,
and return list of tuples, [(x1, y1), (x2, y2) ...] such that
each tuple is a coordinate - (row, columns), starting with 0.
Sort coordinates initially by rows in ascending order.
Also, sort coordinates of the row by columns in descending order.

Examples:
get_row([
[1,2,3,4,5,6],
[1,2,3,4,1,6],
[1,2,3,4,5,1]
], 1) == [(0, 0), (1, 4), (1, 0), (2, 5), (2, 0)]
get_row([], 1) == []
get_row([[], [1], [1, 2, 3]], 3) == [(2, 2)]
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.

(*
 * coord_order sorts by row ascending and, within one row, column descending.
 *)
Definition coord_order (c1 c2 : Z * Z) : Prop :=
  fst c1 < fst c2 \/ (fst c1 = fst c2 /\ snd c1 > snd c2).

(* coord_hits states that coordinate (r,c) points to a cell equal to x. *)
Definition coord_hits (lst : list (list Z)) (x : Z) (coord : Z * Z) : Prop :=
  exists row,
    nth_error lst (Z.to_nat (fst coord)) = Some row /\
    nth_error row (Z.to_nat (snd coord)) = Some x /\
    0 <= fst coord /\ 0 <= snd coord.

(* problem_87_pre imposes no input constraints. *)
Definition problem_87_pre (lst : list (list Z)) (x : Z) : Prop := True.

(* problem_87_spec characterizes exactly the sorted coordinates whose cell equals x. *)
Definition problem_87_spec (lst : list (list Z)) (x : Z) (res : list (Z * Z)) : Prop :=
  (forall coord, In coord res <-> coord_hits lst x coord) /\
  Sorted coord_order res.
