(* Write a function count_nums which takes an array of integers and returns
the number of elements which has a sum of digits > 0.
If a number is negative, then its first signed digit will be negative:
e.g. -123 has signed digits -1, 2, and 3.
>>> count_nums([]) == 0
>>> count_nums([-1, 11, -11]) == 1
>>> count_nums([1, 1, 2]) == 3 *)

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.Arith.Arith.
Require Import Coq.Numbers.DecimalString.
Import ListNotations.
Open Scope Z_scope.

(* Decimal.uint is the stdlib decimal representation produced by Nat.to_uint.
   This eliminator is the no-Fixpoint form of:
   D0 rest -> 0 :: digits(rest), ..., D9 rest -> 9 :: digits(rest).
   Example: Nat.to_uint 123 is D1 (D2 (D3 Nil)), so this returns [1; 2; 3]. *)
Definition decimal_uint_digits (u : Decimal.uint) : list nat :=
  Decimal.uint_rect
    (fun _ => list nat)
    nil
    (fun _ digits => 0%nat :: digits)
    (fun _ digits => 1%nat :: digits)
    (fun _ digits => 2%nat :: digits)
    (fun _ digits => 3%nat :: digits)
    (fun _ digits => 4%nat :: digits)
    (fun _ digits => 5%nat :: digits)
    (fun _ digits => 6%nat :: digits)
    (fun _ digits => 7%nat :: digits)
    (fun _ digits => 8%nat :: digits)
    (fun _ digits => 9%nat :: digits)
    u.

(* decimal_nat_digits returns the decimal digits of n, with 0 represented as [0]. *)
Definition decimal_nat_digits (n : nat) : list nat :=
  match decimal_uint_digits (Nat.to_uint n) with
  | nil => [0%nat]
  | digits => digits
  end.

(* z_abs_decimal_digits returns the digits of the absolute value, as Z digits. *)
Definition z_abs_decimal_digits (n : Z) : list Z :=
  map Z.of_nat (decimal_nat_digits (Z.to_nat (Z.abs n))).

(* digit_sum_abs sums the decimal digits of a non-negative number. *)
Definition digit_sum_abs (n : Z) : Z :=
  fold_left Z.add (z_abs_decimal_digits n) 0.

(* most_significant_digit_abs returns the first digit of the absolute value. *)
Definition most_significant_digit_abs (n : Z) : Z :=
  match z_abs_decimal_digits n with
  | nil => 0
  | d :: _ => d
  end.

(* sum_digits treats the most significant digit of a negative number as signed. *)
Definition sum_digits (z : Z) : Z :=
  let w := Z.abs z in
  if z <? 0
  then digit_sum_abs w - 2 * most_significant_digit_abs w
  else digit_sum_abs w.

(* count_nums_impl counts inputs whose signed digit sum is positive. *)
Definition count_nums_impl (l : list Z) : Z :=
  Z.of_nat (length (filter (fun z => Z.gtb (sum_digits z) 0) l)).

(* problem_108_pre accepts any integer list. *)
Definition problem_108_pre (l : list Z) : Prop := True.

(* problem_108_spec states that output is the positive signed-digit-sum count. *)
Definition problem_108_spec (l : list Z) (output : Z) : Prop :=
  output = count_nums_impl l.
