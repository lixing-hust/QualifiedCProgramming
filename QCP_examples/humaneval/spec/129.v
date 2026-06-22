(*Given a grid with N rows and N columns (N >= 2) and a positive integer k,
each cell of the grid contains a value. Every integer in the range [1, N * N]
inclusive appears exactly once on the cells of the grid.
You have to find the minimum path of length k in the grid. You can start
from any cell, and in each step you can move to any of the neighbor cells,
in other words, you can go to cells which share an edge with you current
cell.
Please note that a path of length k means visiting exactly k cells (not
necessarily distinct).
You CANNOT go off the grid.
A path A (of length k) is considered less than a path B (of length k) if
after making the ordered lists of the values on the cells that A and B go
through (let's call them lst_A and lst_B), lst_A is lexicographically less
than lst_B, in other words, there exist an integer index i (1 <= i <= k)
such that lst_A[i] < lst_B[i] and for any j (1 <= j < i) we have
lst_A[j] = lst_B[j].
It is guaranteed that the answer is unique.
Return an ordered list of the values on the cells that the minimum path go through.

Examples:

Input: grid = [ [1,2,3], [4,5,6], [7,8,9]], k = 3
Output: [1, 2, 1]

Input: grid = [ [5,9,3], [4,1,6], [7,8,2]], k = 1
Output: [1] *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

Definition Grid := list (list nat).
Definition Pos := (nat * nat)%type.

Definition grid_cell (grid : Grid) (r c : nat) : nat :=
  nth c (nth r grid []) 0.

Definition cell_value (grid : Grid) (p : Pos) (v : nat) : Prop :=
  grid_cell grid (fst p) (snd p) = v.

Definition neighbor_min_at
    (grid : Grid) (n r c m : nat) : Prop :=
  r < n /\
  c < n /\
  grid_cell grid r c = 1 /\
  ((0 < r /\ m = grid_cell grid (r - 1) c) \/
   (S r < n /\ m = grid_cell grid (S r) c) \/
   (0 < c /\ m = grid_cell grid r (c - 1)) \/
   (S c < n /\ m = grid_cell grid r (S c))) /\
  (0 < r -> m <= grid_cell grid (r - 1) c) /\
  (S r < n -> m <= grid_cell grid (S r) c) /\
  (0 < c -> m <= grid_cell grid r (c - 1)) /\
  (S c < n -> m <= grid_cell grid r (S c)).

Definition is_neighbor_min_of_one (grid : Grid) (m : nat) : Prop :=
  exists n r c,
    length grid = n /\
    Forall (fun row => length row = n) grid /\
    neighbor_min_at grid n r c m.

Definition alternating_min_path_values (k m : nat) (output : list nat) : Prop :=
  length output = k /\
  forall i,
    i < k ->
    nth_error output i =
      Some (if Nat.even i then 1 else m).

Definition square_permutation_grid (grid : Grid) (n : nat) : Prop :=
  2 <= n /\
  length grid = n /\
  Forall (fun row => length row = n) grid /\
  Permutation (concat grid) (seq 1 (n * n)).

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  1 <= k /\
  exists n, square_permutation_grid grid n.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  exists m,
    is_neighbor_min_of_one grid m /\
    alternating_min_path_values k m output.
