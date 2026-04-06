(* Write a function count_nums which takes an array of integers and returns
the number of elements which has a sum of digits > 0.
If a number is negative, then its first signed digit will be negative:
e.g. -123 has signed digits -1, 2, and 3.
>>> count_nums([]) == 0
>>> count_nums([-1, 11, -11]) == 1
>>> count_nums([1, 1, 2]) == 3 *)

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.Init.Nat.
Import ListNotations.



Fixpoint nat_sum_digits_aux (n : nat) (fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' => match n with 0 => 0 | _ => (n mod 10) + nat_sum_digits_aux (n / 10) fuel' end
  end.
Fixpoint nat_get_msd_aux (m : nat) (fuel : nat) : nat :=
  match fuel with
  | 0 => m
  | S fuel' => if m <? 10 then m else nat_get_msd_aux (m / 10) fuel'
  end.

Definition nat_sum_digits (n : nat) : nat := nat_sum_digits_aux n n.
Definition nat_get_msd (n : nat) : nat := nat_get_msd_aux n n.

Definition sum_digits (z : Z) : Z :=
  if Z_gt_dec z 0 then Z.of_nat (nat_sum_digits (Z.to_nat z))
  else if Z.eq_dec z 0 then 0%Z
  else let p := Z.to_nat (- z) in Z.of_nat (nat_sum_digits p) - (2%Z) * (Z.of_nat (nat_get_msd p)).

Definition count_nums_impl (l : list Z) : nat :=
  length (filter (fun z => Z.gtb (sum_digits z) 0%Z) l).

(* 输入列表可为任意整数列表 *)
Definition problem_108_pre (l : list Z) : Prop := True.

Definition problem_108_spec (l : list Z) (output : nat) : Prop :=
  output = count_nums_impl l.
