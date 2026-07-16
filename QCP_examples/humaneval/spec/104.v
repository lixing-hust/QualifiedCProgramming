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
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Bool.Bool.

Import ListNotations.

(* Decimal.uint is the stdlib decimal representation produced by Nat.to_uint.
   This eliminator is the no-Fixpoint form of:
   D0 rest -> 0 :: digits(rest), ..., D9 rest -> 9 :: digits(rest).
   Example: Nat.to_uint 15 is D1 (D5 Nil), so this returns [1; 5]. *)
Definition decimal_uint_digits (u : Decimal.uint) : list nat :=
  Decimal.uint_rect
    (fun _ => list nat)
    nil
    (fun _ digits => 0 :: digits)
    (fun _ digits => 1 :: digits)
    (fun _ digits => 2 :: digits)
    (fun _ digits => 3 :: digits)
    (fun _ digits => 4 :: digits)
    (fun _ digits => 5 :: digits)
    (fun _ digits => 6 :: digits)
    (fun _ digits => 7 :: digits)
    (fun _ digits => 8 :: digits)
    (fun _ digits => 9 :: digits)
    u.

(* decimal_nat_digits returns the decimal digits of n, with 0 represented as [0]. *)
Definition decimal_nat_digits (n : nat) : list nat :=
  match decimal_uint_digits (Nat.to_uint n) with
  | nil => [0]
  | digits => digits
  end.

(* has_only_odd_digits_bool is the executable boolean used by library filter. *)
Definition has_only_odd_digits_bool (n : nat) : bool :=
  forallb Nat.odd (decimal_nat_digits n).

(* filter_odd_digits keeps exactly the elements whose decimal digits are all odd. *)
Definition filter_odd_digits (l : list nat) : list nat :=
  filter has_only_odd_digits_bool l.

(* problem_104_pre requires all input elements to be positive. *)
Definition problem_104_pre (x : list nat) : Prop := Forall (fun n => n > 0) x.

(* problem_104_spec characterizes the sorted list of elements with only odd digits. *)
Definition problem_104_spec (x y : list nat) : Prop :=
  Permutation y (filter_odd_digits x) /\
  Sorted le y.
