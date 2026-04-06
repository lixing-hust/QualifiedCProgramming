(* Return median of elements in the list l.
>>> median([3, 1, 2, 4, 5])
3
>>> median([-10, 4, 6, 1000, 10, 20])
8.0 *)

(* Spec(input : list float, output : float) :=

​	∃Sorted_input, 
​		Sorted(input, Sorted_input) /\
​		length(input) % 2 =1  → output = Sorted_input[length(input) / 2] /\
​		length(input) % 2 <>1  → output = (Sorted_input[length(input) / 2] + Sorted_input[length(input) / 2 -1]) /2 *)

Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope R_scope.

(* Pre: input must be non-empty to define median *)
Definition problem_47_pre (input : list R) : Prop := input <> [].

Definition problem_47_spec(input : list R) (output : R) : Prop :=
  exists Sorted_input,
    Sorted Rle Sorted_input /\
    forall r : R, In r input <-> In r Sorted_input /\
    let len := length input in
    let halflen := ((length input) / 2)%nat in
    ((len mod 2 = 1)%nat -> output = nth halflen Sorted_input 0) /\
    ((len mod 2 = 0)%nat -> output = ((nth halflen Sorted_input 0) + (nth (halflen-1) Sorted_input 0)) / 2).