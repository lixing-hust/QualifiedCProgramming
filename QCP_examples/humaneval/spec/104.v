(* Given a list of positive integers x. return a sorted list of all
elements that hasn't any even digit.

Note: Returned list should be sorted in increasing order.

For example:
>>> unique_digits([15, 33, 1422, 1])
[1, 15, 33]
>>> unique_digits([152, 323, 1422, 10])
[] *)



(* 导入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Bool.Bool.

Import ListNotations.

(* is_odd_digit recognizes decimal odd digits. *)
Definition is_odd_digit (d : nat) : Prop :=
  d = 1 \/ d = 3 \/ d = 5 \/ d = 7 \/ d = 9.

(* all_digits_odd_list states that every digit in a list is odd. *)
Definition all_digits_odd_list (l : list nat) : Prop :=
  Forall is_odd_digit l.

(* nat_to_digits enumerates enough decimal positions for positive n. *)
Definition nat_to_digits (n : nat) : list nat :=
  map (fun p => (n / Nat.pow 10 p) mod 10) (seq 0 n).

(* has_only_odd_digits is the logical predicate for numbers with no even digit. *)
Definition has_only_odd_digits (n : nat) : Prop :=
  all_digits_odd_list (nat_to_digits n).

(* has_only_odd_digits_bool is the executable boolean used by library filter. *)
Definition has_only_odd_digits_bool (n : nat) : bool :=
  let digits := nat_to_digits n in
  forallb (fun d => orb (Nat.eqb d 1) (orb (Nat.eqb d 3) (orb (Nat.eqb d 5) (orb (Nat.eqb d 7) (Nat.eqb d 9))))) digits.

(* filter_odd_digits keeps exactly the elements whose decimal digits are all odd. *)
Definition filter_odd_digits (l : list nat) : list nat :=
  filter has_only_odd_digits_bool l.

(* problem_104_pre requires all input elements to be positive. *)
Definition problem_104_pre (x : list nat) : Prop := Forall (fun n => n > 0) x.

(* problem_104_spec characterizes the sorted list of elements with only odd digits. *)
Definition problem_104_spec (x y : list nat) : Prop :=
  Permutation y (filter_odd_digits x) /\
  Sorted le y.
