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

Fixpoint signed_digit_loop (fuel : nat) (w sum : Z) : Z :=
  match fuel with
  | O => sum - w
  | S fuel' =>
      if w <? 10 then sum - w
      else signed_digit_loop fuel' (w / 10) (sum + w mod 10)
  end.

Definition sum_digits (z : Z) : Z :=
  if z >? 0 then 1
  else signed_digit_loop 11 (Z.abs z) 0.

Definition count_nums_impl (l : list Z) : Z :=
  Z.of_nat (length (filter (fun z => Z.gtb (sum_digits z) 0) l)).

(* 输入列表可为任意整数列表 *)
Definition problem_108_pre (l : list Z) : Prop := True.

Definition problem_108_spec (l : list Z) (output : Z) : Prop :=
  output = count_nums_impl l.
