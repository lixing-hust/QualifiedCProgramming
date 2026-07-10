(* Write a function count_nums which takes an array of integers and returns
the number of elements which has a sum of digits > 0.
If a number is negative, then its first signed digit will be negative:
e.g. -123 has signed digits -1, 2, and 3.
>>> count_nums([]) == 0
>>> count_nums([-1, 11, -11]) == 1
>>> count_nums([1, 1, 2]) == 3 *)

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

(* decimal_digit returns the digit at decimal position p of a non-negative number. *)
Definition decimal_digit (n : Z) (p : nat) : Z :=
  (n / Z.of_nat (Nat.pow 10 p)) mod 10.

(* msd_pos returns the highest position with a non-zero digit, defaulting to 0. *)
Definition msd_pos (n : Z) : nat :=
  fst
    (fold_left
       (fun acc p =>
          let d := decimal_digit n p in
          if d =? 0 then acc else (p, d))
       (seq 0 (Z.to_nat n + 1))
       (0%nat, 0)).

(* digit_sum_abs sums the decimal digits of a non-negative number. *)
Definition digit_sum_abs (n : Z) : Z :=
  fold_left Z.add (map (decimal_digit n) (seq 0 (S (msd_pos n)))) 0.

(* sum_digits treats the most significant digit of a negative number as signed. *)
Definition sum_digits (z : Z) : Z :=
  let w := Z.abs z in
  if z <? 0
  then digit_sum_abs w - 2 * decimal_digit w (msd_pos w)
  else digit_sum_abs w.

(* count_nums_impl counts inputs whose signed digit sum is positive. *)
Definition count_nums_impl (l : list Z) : Z :=
  Z.of_nat (length (filter (fun z => Z.gtb (sum_digits z) 0) l)).

(* problem_108_pre accepts any integer list. *)
Definition problem_108_pre (l : list Z) : Prop := True.

(* problem_108_spec states that output is the positive signed-digit-sum count. *)
Definition problem_108_spec (l : list Z) (output : Z) : Prop :=
  output = count_nums_impl l.
